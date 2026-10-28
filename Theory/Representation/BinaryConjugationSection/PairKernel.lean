module
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# The kernel on a pair of subgroups in an abelian section

Subgroups above an abelian section's kernel normalize one another. The
relative-index product formula therefore applies to their literal join,
without ambient normality. Comparing with a second coordinate quotient
computes the kernel on that join from its projected image order.

These identities are used on the two original exterior spans in
Aschbacher--Smith, The Classification of Quasithin Groups, 13.8.30,
printed p.964, to isolate the kernel that projected movement must exclude.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W Z : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {H A N J B U : Subgroup G}
  {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) J Z}

private theorem normalizes_over_kernel
    (p : BinaryConjugationSection J B U σ)
    (S : Subgroup G) (hSB : S ≤ B) (hUS : U ≤ S) : B ≤ normalizer S := by
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro b hb s hs
  apply hUS
  apply (p.coordinates_eq_one_iff (⁅(⟨b,hb⟩ : B),(⟨s,hSB hs⟩ : B)⁆)).mp
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- Relative indices of two subgroups in an abelian section satisfy the
product formula without an ambient normality assumption. -/
theorem pair_relativeIndex
    (p : BinaryConjugationSection J B U σ)
    (S R V : Subgroup G) (hSB : S ≤ B) (hRB : R ≤ B) (hUS : U ≤ S)
    (hVS : V ≤ S) (hVR : V ≤ R) :
    V.relIndex (S ⊔ R) * V.relIndex (S ⊓ R) =
      V.relIndex S * V.relIndex R := by
  have hn : R ≤ normalizer S := hRB.trans (normalizes_over_kernel p S hSB hUS)
  let C := S ⊔ R
  let : (S.subgroupOf C).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le S.le_normalizer hn)
  have hi : S.relIndex C = (S ⊓ R).relIndex R := by
    have hh := relIndex_sup_left (R.subgroupOf C) (S.subgroupOf C)
    rw [←subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at hh
    exact hh.trans (inf_relIndex_right S R).symm
  have hS := relIndex_mul_relIndex V S C hVS le_sup_left
  have hR := relIndex_mul_relIndex V (S ⊓ R) R (le_inf hVS hVR) inf_le_right
  rw [←hS,hi,←hR]
  ac_rfl

/-- Index identity for the kernel on the join of two subgroups in a second
abelian section. It retains both original coordinate kernels. -/
theorem pair_kernel_index
    (q : BinaryConjugationSection H A N ρ)
    (p : BinaryConjugationSection J B U σ)
    (S R V : Subgroup G) (hSA : S ≤ A) (hRA : R ≤ A)
    (hSB : S ≤ B) (hRB : R ≤ B) (hUS : U ≤ S)
    (hVS : V ≤ S) (hVR : V ≤ R) (hVN : V ≤ N) :
    V.relIndex ((S ⊔ R) ⊓ N) * Nat.card (q.imageSpace (S ⊔ R)) *
      V.relIndex (S ⊓ R) = V.relIndex S * V.relIndex R := by
  have hleft := relIndex_mul_relIndex V ((S ⊔ R) ⊓ N) (S ⊔ R)
    (le_inf (hVS.trans le_sup_left) hVN) inf_le_left
  rw [inf_relIndex_left,←q.imageSpace_card_eq_relIndex (S ⊔ R) (sup_le hSA hRA)] at hleft
  rw [hleft]
  exact pair_relativeIndex p S R V hSB hRB hUS hVS hVR
end Representation.BinaryConjugationSection
