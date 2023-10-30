// RUN: %target-typecheck-verify-swift

protocol HasSelfRequirements {
  func foo(_ x: Self)
  // expected-error@+3 {{use of protocol 'HasSelfRequirements' as a type must be prefixed with 'some' or 'any'}}
  // expected-note@+2 {{Replace with 'any HasSelfRequirements'}}
  // expected-note@+1 {{Replace with 'some HasSelfRequirements'}}
  func returnsOwnProtocol() -> HasSelfRequirements
}
protocol Bar {
  // init() methods should not prevent use as an existential.
  init()

  func bar() -> Bar
}

func useBarAsType(_ x: Bar) {}

protocol Pub : Bar { }

func refinementErasure(_ p: Pub) {
  useBarAsType(p)
}

typealias Compo = HasSelfRequirements & Bar

struct CompoAssocType {
  typealias Compo = HasSelfRequirements & Bar
}

func useAsRequirement<T: HasSelfRequirements>(_ x: T) { }
func useCompoAsRequirement<T: HasSelfRequirements & Bar>(_ x: T) { }
func useCompoAliasAsRequirement<T: Compo>(_ x: T) { }
func useNestedCompoAliasAsRequirement<T: CompoAssocType.Compo>(_ x: T) { }

func useAsWhereRequirement<T>(_ x: T) where T: HasSelfRequirements {}
func useCompoAsWhereRequirement<T>(_ x: T) where T: HasSelfRequirements & Bar {}
func useCompoAliasAsWhereRequirement<T>(_ x: T) where T: Compo {}
func useNestedCompoAliasAsWhereRequirement<T>(_ x: T) where T: CompoAssocType.Compo {}

func useAsType(_: any HasSelfRequirements,
               _: any HasSelfRequirements & Bar,
               _: any Compo,
               _: any CompoAssocType.Compo) { }

struct TypeRequirement<T: HasSelfRequirements> {}
struct CompoTypeRequirement<T: HasSelfRequirements & Bar> {}
struct CompoAliasTypeRequirement<T: Compo> {}
struct NestedCompoAliasTypeRequirement<T: CompoAssocType.Compo> {}

struct CompoTypeWhereRequirement<T> where T: HasSelfRequirements & Bar {}
struct CompoAliasTypeWhereRequirement<T> where T: Compo {}
struct NestedCompoAliasTypeWhereRequirement<T> where T: CompoAssocType.Compo {}

struct Struct1<T> { }
struct Struct2<T : Pub & Bar> { }
struct Struct3<T : Pub & Bar & P3> { } // expected-error {{cannot find type 'P3' in scope}}
struct Struct4<T> where T : Pub & Bar {}

struct Struct5<T : protocol<Pub, Bar>> { } // expected-error {{'protocol<...>' composition syntax has been removed; join the type constraints using '&'}}
struct Struct6<T> where T : protocol<Pub, Bar> {} // expected-error {{'protocol<...>' composition syntax has been removed; join the type constraints using '&'}}

typealias T1 = Pub & Bar
typealias T2 = protocol<Pub , Bar> // expected-error {{'protocol<...>' composition syntax has been removed; join the type constraints using '&'}}

// rdar://problem/20593294
protocol HasAssoc {
  associatedtype Assoc
  func foo()
}

do {
  enum MyError : Error {
    case bad(Any)
  }

  func checkIt(_ js: Any) throws {
    switch js {
    // expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
    // expected-note@+2 {{Replace with 'any HasAssoc'}}
    // expected-note@+1 {{Replace with 'some HasAssoc'}}
    case let dbl as HasAssoc:
      throw MyError.bad(dbl)

    default:
      fatalError("wrong")
    }
  }
}
// expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any HasAssoc'}}
// expected-note@+1 {{Replace with 'some HasAssoc'}}
func testHasAssoc(_ x: Any, _: HasAssoc) {
  if let p = x as? any HasAssoc {
    p.foo() // don't crash here.
  }

  struct ConformingType : HasAssoc {
    typealias Assoc = Int
    func foo() {}
    // expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
    // expected-note@+2 {{Replace with 'any HasAssoc'}}
    // expected-note@+1 {{Replace with 'some HasAssoc'}}
    func method() -> HasAssoc {}
  }
}

// https://github.com/apple/swift/issues/42661
// expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any HasAssoc'}}
// expected-note@+1 {{Replace with 'some HasAssoc'}}
var b: HasAssoc

// Further generic constraint error testing - typealias used inside statements
protocol P {}
typealias MoreHasAssoc = HasAssoc & P
func testHasMoreAssoc(_ x: Any) {
  if let p = x as? any MoreHasAssoc {
    p.foo() // don't crash here.
  }
}

struct Outer {
  typealias Any = Int // expected-error {{keyword 'Any' cannot be used as an identifier here}} expected-note {{if this name is unavoidable, use backticks to escape it}} {{13-16=`Any`}}
  typealias `Any` = Int
  static func aa(a: `Any`) -> Int { return a }
}

typealias X = Struct1<Pub & Bar>
_ = Struct1<Pub & Bar>.self

typealias AliasWhere<T> = T
// expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any HasAssoc'}}
// expected-note@+1 {{Replace with 'some HasAssoc'}}
where T : HasAssoc, T.Assoc == HasAssoc 

struct StructWhere<T>
where T : HasAssoc,
      T.Assoc == any HasAssoc {}
// expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any HasAssoc'}}
// expected-note@+1 {{Replace with 'some HasAssoc'}}
protocol ProtocolWhere where T == HasAssoc {
  associatedtype T

  associatedtype U : HasAssoc
    where U.Assoc == any HasAssoc
}
// expected-error@+3 {{use of protocol 'HasAssoc' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any HasAssoc'}}
// expected-note@+1 {{Replace with 'some HasAssoc'}}
extension HasAssoc where Assoc == HasAssoc {}

func FunctionWhere<T>(_: T)
where T : HasAssoc,
      T.Assoc == any HasAssoc {}

struct SubscriptWhere {
  subscript<T>(_: T) -> Int
  where T : HasAssoc,
        T.Assoc == any HasAssoc {
    get {}
    set {}
  }
}

struct OuterGeneric<T> {
  func contextuallyGenericMethod() where T == any HasAssoc {}
}
