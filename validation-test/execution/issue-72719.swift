// RUN: %target-swift-frontend -interpret %s
// REQUIRES: executable_test

// This only reproduced if you provide the -interpret flag!
// https://github.com/apple/swift/issues/72719

protocol D {}
struct U: D, Equatable {}
class Q<T> {}
class R<V, E: D & Equatable> {}
extension R where E == U {
    struct S<X> {}
    static func a<T>(_: T) -> R {
        let x = Q<S<T>>()
        fatalError()
    }
}
