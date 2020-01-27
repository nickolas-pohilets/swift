//
//  ClosureAsStructTransform.cpp
//  Swift
//
//  Created by Nickolas Pokhylets on 29/01/2020.
//

#include "ConstraintSystem.h"
#include "swift/AST/SourceFile.h"

//#include "MiscDiagnostics.h"
//#include "SolutionResult.h"
#include "TypeChecker.h"
#include "swift/AST/ASTVisitor.h"
#include "swift/AST/ProtocolConformance.h"
//#include "swift/AST/ASTWalker.h"
//#include "swift/AST/NameLookup.h"
//#include "swift/AST/NameLookupRequests.h"
//#include "swift/AST/ParameterList.h"
//#include "swift/AST/TypeCheckRequests.h"
#include "llvm/ADT/DenseMap.h"
#include "swift/AST/ParameterList.h"
#include "llvm/ADT/SmallVector.h"
//#include <iterator>
//#include <map>
//#include <memory>
//#include <utility>
//#include <tuple>
//

using namespace llvm;
using namespace swift;
using namespace constraints;

namespace {

Identifier findAvailableIdentifier(SourceFile* SF) {
  ASTContext &Context = SF->getASTContext();
  Identifier StructID;
  for (unsigned suffix = 0; ; suffix ++) {
    StructID = Context.getIdentifier("$_closure_as_struct_" + std::to_string(suffix));

    llvm::SmallVector<ValueDecl*, 4> Decls;
    SF->lookupValue(StructID, NLKind::UnqualifiedLookup, Decls);
    if (Decls.empty()) {
      // We found available identifier
      break;
    }
  }
  return StructID;
}

class ClosureAsStructRewriter: public ASTWalker {
  ASTContext & ctx;
  AppliedClosureAsStructTransform::DeclMap const & declMap;
public:
  ClosureAsStructRewriter(ASTContext & Context, AppliedClosureAsStructTransform::DeclMap const & map)
    : ASTWalker()
    , ctx(Context)
    , declMap(map)
  {}

  virtual std::pair<bool, Expr *> walkToExprPre(Expr *E) override {
    if (auto declRef = dyn_cast<DeclRefExpr>(E)) {
      auto D = declRef->getDecl();
      auto it = declMap.find(D);
      if (it != declMap.end()) {
        auto newRef = new (ctx) DeclRefExpr(
          ConcreteDeclRef(it->getSecond()),
          declRef->getNameLoc(),
          declRef->isImplicit(),
          declRef->getAccessSemantics(),
          declRef->getType()
        );
        return { false, newRef };
      }
    }
    return ASTWalker::walkToExprPre(E);
  }
};

} // namespace

constraints::AppliedClosureAsStructTransform
swift::appliedClosureAsStructTransform(constraints::ConstraintSystem &CS, 
    SmallVector<constraints::ClosureAsStructConformance, 4> ClosureProtocols,
    ClosureAsStructType *structType,
    ClosureExpr *closure,
    DeclContext *dc) {
  TypeChecker::computeCaptures(AnyFunctionRef(closure));

  SourceFile *SF = dc->getParentSourceFile();
  ASTContext &Context = closure->getASTContext();
  Identifier StructID = findAvailableIdentifier(SF);
  StructDecl *SD = new (Context) StructDecl(
    /* StructLoc = */SourceLoc(),
    /* Name = */StructID,
    /* NameLoc = */SourceLoc(),
    /* Inherited = */{ },
    /* GenericParams = */nullptr,
    /* DC = */SF);
  SD->getAttrs().add(new (Context) AccessControlAttr(
        SourceLoc(), SourceRange(), AccessLevel::Private, true));
  SD->setImplicit();

  llvm::SmallVector<TypeLoc, 4> Inherited;
  for (auto &record: ClosureProtocols) {
    if (record.Ty != structType) {
      continue;
    }
    Inherited.push_back(TypeLoc::withoutLoc(record.Proto->getDeclaredType()));
  }
  SD->setInherited(Context.AllocateCopy(Inherited));

  SmallVector<CapturedValue, 4> localCaptures;
  closure->getCaptureInfo().getLocalCaptures(localCaptures);

  AppliedClosureAsStructTransform::DeclMap declMap;
  std::vector<Expr *> initializedArgs;
  std::vector<Identifier> initializedLabels;
  std::vector<TupleTypeElt> tupleTypeElts;
  for (auto const & capture: localCaptures) {
    Identifier originalName = capture.getDecl()->getBaseName().getIdentifier();
    Identifier captureName = Context.getIdentifier(
        "$_capture_" + originalName.str().str());
    VarDecl* VD = new (Context) VarDecl(
      /*isStatic = */false,
      VarDecl::Introducer::Var,
      /*isCaptureList =*/false,
      capture.getLoc(),
      captureName,
      SD);

    VD->setImplicit();

    Type varTy = capture.getDecl()->getInterfaceType();
    VD->setInterfaceType(varTy);

    Pattern *P = new (Context) NamedPattern(VD);
    TypedPattern *TP = TypedPattern::createImplicit(Context, P, varTy);
    PatternBindingEntry entry(TP, SourceLoc(), nullptr, nullptr);
    auto PBD = PatternBindingDecl::create(
        Context, SourceLoc(), StaticSpellingKind::None, SourceLoc(), entry, SD);
    PBD->setImplicit();
    SD->addMember(PBD);
    SD->addMember(VD);

    auto result = declMap.insert(std::make_pair(capture.getDecl(), VD));
    assert(result.second);
    auto captureRef = new (Context) DeclRefExpr(
      ConcreteDeclRef(capture.getDecl()),
      DeclNameLoc(capture.getLoc()),
      /*implicit*/false,
      AccessSemantics::Ordinary,
      Type()
    );
    CS.setType(captureRef, varTy);
    initializedArgs.push_back(captureRef);
    initializedLabels.push_back(captureName);
    tupleTypeElts.push_back(TupleTypeElt(varTy, captureName));
  }

  FuncDecl* Requirement = structType->getClosureRequirement();
  ParameterList *RequirementParams = Requirement->getParameters();
  ParameterList *ClosureParams = closure->getParameters();
  assert(ClosureParams->getArray().size() == RequirementParams->getArray().size());
  size_t numArgs = ClosureParams->getArray().size();
  SmallVector<ParamDecl *, 8> params;
  for (size_t i = 0; i < numArgs; i++) {
    ParamDecl *closureParam = closure->getParameters()->get(i);
    ParamDecl *requirementParam = RequirementParams->get(i);
    ParamDecl *generatedParam = new (Context) ParamDecl(
        closureParam->getSpecifierLoc(),
        requirementParam->getArgumentNameLoc(),
        requirementParam->getArgumentName(),
        closureParam->getParameterNameLoc(),
        closureParam->getParameterName(),
        SD);
    generatedParam->setSpecifier(closureParam->getSpecifier());
    generatedParam->setImplicitlyUnwrappedOptional(closureParam->isImplicitlyUnwrappedOptional());
    generatedParam->setImplicit();
    declMap.insert(std::make_pair(closureParam, generatedParam));
    params.push_back(generatedParam);
  }

  ParameterList *Params = ParameterList::create(Context, ClosureParams->getLParenLoc(), params, ClosureParams->getRParenLoc());

  FuncDecl *FD = FuncDecl::createImplicit(
      /* Context = */Context,
      /* StaticSpelling = */StaticSpellingKind::None,
      /* Name = */Requirement->getEffectiveFullName(),
      /* NameLoc = */SourceLoc(),
      /* Async = */Requirement->hasAsync(),
      /* Throws = */Requirement->hasThrows(),
      /* GenericParams = */nullptr,
      /* BodyParams = */Params,
      /* FnRetType = */Requirement->getResultInterfaceType(),
      /* Parent = */SD);
  FD->setImplicit();
  SD->addMember(FD);

  SF->addTopLevelDecl(SD);
  for (auto *conformance : SD->getLocalConformances(ConformanceLookupKind::NonInherited)) {
    if (auto *normal = dyn_cast<NormalProtocolConformance>(conformance)) {
      TypeChecker::checkConformance(normal);
    }
  }

  ConstructorDecl *CD = SD->hasMemberwiseInitializer()
    ? SD->getMemberwiseInitializer() : SD->getDefaultInitializer();
  DeclRefExpr* ConstructorRef = new (Context) DeclRefExpr(
    ConcreteDeclRef(CD),
    DeclNameLoc(closure->getLoc()),
    /* implicit */true,
    AccessSemantics::Ordinary,
    Type()
  );
  CS.setType(ConstructorRef, CD->getInterfaceType());

  TypeExpr *TypeExpr = TypeExpr::createImplicit(
      SD->getDeclaredType(), Context);

  Type structTy = SD->getDeclaredType();
  CS.setType(TypeExpr, MetatypeType::get(structTy, Context));

  auto Constructor = new (Context) ConstructorRefCallExpr(
      ConstructorRef, TypeExpr);
  CS.setType(Constructor, CD->getMethodInterfaceType());

  auto CallExpr = CallExpr::createImplicit(
      Context, Constructor,  initializedArgs,  initializedLabels);
  CS.setType(CallExpr->getArg(), TupleType::get(tupleTypeElts, Context));
  CS.setType(CallExpr, CD->getResultInterfaceType());

  SmallVector<AnyFunctionType::Param, 4> typeParams;
  CD->getParameters()->getParams(typeParams);
  CS.setType(CallExpr->getArg(),
      AnyFunctionType::composeInput(Context, typeParams, false));

  AppliedClosureAsStructTransform transform;
  transform.closureExpr = closure;
  transform.generatedStructDecl = SD;
  transform.generatedStructType = structTy;
  transform.generatedExpr = CallExpr;
  transform.generatedFunc = FD;
  transform.declMap = std::move(declMap);

  return transform;
}

void constraints::AppliedClosureAsStructTransform::rewriteBody() const {
 ASTContext &Context = closureExpr->getASTContext();
 BraceStmt* body = closureExpr->getBody();
 ClosureAsStructRewriter Rewriter(Context, declMap);
 body->walk(Rewriter);
 generatedFunc->setBody(body);
 TypeChecker::typeCheckDecl(generatedStructDecl);
}
