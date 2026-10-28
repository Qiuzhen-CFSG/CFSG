module

public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The intrinsic automorphism input for the rank-one exclusion

The remaining model calculation on Aschbacher--Smith, combined manuscript
of 1 March 2004, printed p.1137, is that exponent-three subgroups of the
automorphism group of a three-rank-one simple group in Theorem C are abelian.
`CubicAutomorphismsAbelian` states just this intrinsic property, without a
classification certificate or a conclusion about the ambient group.

The proved transfer uses the injective action of automorphisms of a perfect
group on its actual central quotient. Thus the model workers need only the
simple carriers; no separate automorphism classification of central covers
is required. The property itself is not asserted for the model list here.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
universe u
variable {H : Type u} [Group H]

/-- Every subgroup of the actual automorphism group with exponent dividing
three is abelian. This contains no ambient component or rank-exclusion conclusion. -/
@[expose] def CubicAutomorphismsAbelian (S : Type*) [Group S] : Prop :=
  ∀ A : Subgroup (MulAut S), (∀ a : A, a ^ 3 = 1) → IsMulCommutative A

/-- The faithful action on the central quotient transfers the automorphism
property to every perfect central cover. -/
theorem cubic_of_central_quotient [Group.IsPerfect H]
    (ha : CubicAutomorphismsAbelian (H ⧸ center H)) : CubicAutomorphismsAbelian H := by
  intro A hA
  let q := quotientAut (center H)
  let D := A.map q
  have hD : ∀ d : D, d ^ 3 = 1 := by
    rintro ⟨d, a, haA, rfl⟩
    apply Subtype.ext
    exact (map_pow q a 3).symm.trans
      ((congrArg q (congrArg Subtype.val (hA ⟨a, haA⟩))).trans q.map_one)
  let := ha D hD
  have hf : Function.Injective (q.subgroupMap A) := fun x y h => Subtype.ext
    (MulAut.quotient_center_injective (congrArg Subtype.val h))
  exact IsMulCommutative.of_comm fun a b => hf (by simp only [map_mul, mul_comm])


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
