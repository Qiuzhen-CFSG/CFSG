module
public import Theory.GroupTheory.SylowTwistedGeneratingPair
import all Theory.GroupTheory.SylowTwistedGeneratingPair

/-!
# The literal conjugacy-twist formula

This internal extension of the defining module exports its equation for
comparison with powers of the Sylow automorphism. The private import is
confined to proving this equation; clients retain the existing public
boundary and need not unfold the original definition.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 6.4, pp.53--54.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem twistedConjugacy_eq (S : Subgroup G) (α : MulAut S) (g : G) :
    twistedConjugacy S α g = α.trans ((MulAut.conj g).subgroupMap S) := by rfl

end Theory.GroupTheory
