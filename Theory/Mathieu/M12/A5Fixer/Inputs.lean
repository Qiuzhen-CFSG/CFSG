module

public import Theory.Mathieu.M12.Basic
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Model obligations for the M₁₂–A₅ fixer

The full abstract automorphism fixer can be bounded using its inner part
and its image in Out(M₁₂). To distinguish the four-group from the cyclic
group of order four, it suffices to exclude a factor five from the order
of the fixed subgroup of an automorphism of order four.

These definitions specify remaining concrete calculations; none is asserted
here. In particular, the existing Sylow-fixer calculation does not imply
the outer-index bound, and an involution table alone does not classify
fixed subgroups of automorphisms of order four.

Source context: Aschbacher–Smith 16.1.5(4), 16.1.7(3f), and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12A5Fixer
open Subgroup

/-- The centralizer inside M₁₂ of any actually embedded A₅ has order at most two. -/
def InnerCentralizerBound : Prop :=
  ∀ (P : Subgroup M12), Nonempty (P ≃* alternatingGroup (Fin 5)) →
    Nat.card (centralizer (P : Set M12)) ≤ 2

/-- The index of the actual inner automorphism group in the full abstract group. -/
def OuterIndexBound : Prop := (MulAut.innerSubgroup M12).index ≤ 2

/-- No abstract automorphism of order four fixes a subgroup of order five. -/
def OrderFourFixedFiveExclusion : Prop :=
  ∀ a : MulAut M12, orderOf a = 4 → ¬ 5 ∣ Nat.card a.fixedSubgroup

end Sporadic.Mathieu.M12A5Fixer
