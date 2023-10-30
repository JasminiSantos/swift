// RUN: %empty-directory(%t)
// RUN: %target-swift-frontend %s         -swift-version 5 -emit-module -DM -module-name M -emit-module-path %t/M.swiftmodule
// RUN: %target-swift-frontend %s -verify -swift-version 5 -typecheck -I %t -enable-upcoming-feature ExistentialAny

// Test that a protocol that requires 'any' *only* when the feature is enabled
// is diagnosed as expected when said protocol originates in a different module.
// In other words, test that deserialization does not affect 'any' migration
// diagnostics.

#if M
public protocol P {}
#else
import M
// expected-error@+3 {{use of protocol 'P' as a type must be prefixed with 'some' or 'any'}}
// expected-note@+2 {{Replace with 'any P'}}
// expected-note@+1 {{Replace with 'some P'}}
func test(_: P) {}
#endif
