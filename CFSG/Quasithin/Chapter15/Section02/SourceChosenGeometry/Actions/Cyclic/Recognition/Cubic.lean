module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Inputs
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.CubicObstruction

/-!
# Excluding cubic centralizers in the cyclic source branch

The source involution image fixes its commutator plane. The ambient cubic
obstruction and the elementary pointwise kernel therefore exclude every
three-subgroup of its centralizer, including the central cubic factor in
the S₃ × C₃ row of 15.2.1.

Source: Aschbacher--Smith 15.2.13, printed pp.1111--1112, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

namespace Cyclic
/-- No nontrivial three-subgroup centralizes a literal offender image. -/
theorem Preceding.three_centralizer_eq_bot {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H)
    (C : Subgroup (internalActionImage M V h.prepared.normalized))
    (hp : IsPGroup 3 C)
    (hC : C ≤ centralizer (actor M V B h.prepared.normalized : Set _)) : C = ⊥ := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hAc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hAt : zpowers t = A := ht
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (hAc ▸ pow_card_eq_one' (x := (⟨t,htA⟩ : A)))
  have hpE := (d.planes B hB).2.2
  apply three_image_centralizer_eq_bot h hpE.1 hpE.2.1 hpE.2.2.2.1 hpE.2.2.2.2.1
    (d.residual_eq ▸ d.residual_centralizes) t ht2 _ C hp
    (hC.trans (centralizer_le (Set.singleton_subset_iff.mpr htA)))
  rw [hAt, ambientSpace_fixed _ ((d.actor_le_sylow hB).trans h.maximal.1.2)]
  exact ambient_fixed_eq_commutator h ((d.actor_le_sylow hB).trans h.maximal.1.2)
    (d.planes B hB).1 (d.planes B hB).2.1

/-- The S₃ × C₃ row contradicts the literal plane normalizer obstruction. -/
theorem Preceding.not_symmetric_three_cubic {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    ¬ Nonempty (internalActionImage M V h.prepared.normalized ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) := by
  rintro ⟨e⟩
  obtain ⟨B,hB⟩ := d.nonempty
  let c := e.symm (1, Multiplicative.ofAdd (1 : ZMod 3))
  have hc3 : c ^ 3 = 1 := by
    apply e.injective
    simp [c, ← map_pow]
    decide
  have hcne : c ≠ 1 := by
    intro he
    have hh := congrArg e he
    simp [c] at hh
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hcne
  have hp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hco]; rfl)
  have hC : zpowers c ≤ centralizer
      (actor M V B h.prepared.normalized : Set _) := by
    apply zpowers_le.mpr
    intro a ha
    apply e.injective
    simp only [map_mul, c, e.apply_symm_apply, Prod.mul_def, one_mul, mul_one]
    exact Prod.ext rfl (mul_comm _ _)
  have hz := d.three_centralizer_eq_bot hB (zpowers c) hp hC
  exact hcne (mem_bot.mp (show c ∈ (⊥ : Subgroup _) from hz ▸ mem_zpowers c))
end Cyclic
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
