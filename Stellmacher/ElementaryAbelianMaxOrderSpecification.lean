module

public import Stellmacher.ElementaryAbelianMaxOrder
import all Stellmacher.ElementaryAbelianMaxOrder

/-!
# Cardinality specification for the maximum elementary order

This internal extension publishes the cardinality specification of the opaque
maximum-order invariant, without exposing its choice-based implementation.
The deliberate `import all` accesses the existing private proof in the same
package; consumers need only the public specification below. Keeping this
bridge separate avoids rebuilding the shared maximum-order module.

The specification identifies rank-zero Thompson families in
Aschbacher–Smith, B.2.2, with the existing Stellmacher family.
-/

namespace Stellmacher

/-- Every member of the maximum-order family has the specified maximum order. -/
public theorem elementaryAbelianMaxSubgroups_card_eq
    {G : Type*} [Group G] [Finite G] (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    Nat.card A = elementaryAbelianMaxOrder S :=
  card_eq_elementaryAbelianMaxOrder S A hA

end Stellmacher
