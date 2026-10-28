module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
/-!
# Cubic divisibility of the actual C.2.7 component quotient

Every group in the proved star catalogue has order divisible by three.
Use the actual classical matrix quotients, the octonion-model order, and
the cubic center of the triple cover. The source comparison from J/O₂(J)
onto J* then lifts divisibility to the literal two-core quotient. No
identification of these two quotients is assumed.

This supplies component normality in the plane normalizer in original
13.3.12. Source: Aschbacher--Smith C.2.7, pp.145--147, and13.3.12, p.889.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private theorem sl_three_dvd (F : ChapterB.QuasisimpleSource.BinaryField)
    {n : ℕ} (hn : 2 ≤ n) : 3 ∣ Nat.card SL(n,F.Carrier) := by
  have hd := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F.Carrier) (i := (⟨0,by omega⟩ : Fin n)) (j := (⟨1,by omega⟩ : Fin n))
    (by simp)
  exact (hd.trans (card_subgroup_dvd_card _)).trans
    (card_quotient_dvd_card (center SL(n,F.Carrier)))

private theorem alternating_three_dvd (n : ℕ) (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hd : 3 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    exact Nat.dvd_factorial (by decide) hn
  exact (Nat.prime_three.dvd_mul.mp hd).resolve_left (by decide)

/-- Every actual group in the C.2.7 star catalogue contains a cubic. -/
theorem StarModels.Model.three_dvd {A : Type*} [Group A] (h : StarModels.Model A) :
    3 ∣ Nat.card A := by
  cases h with
  | linearTwo F e => rw [Nat.card_congr e.toEquiv]; exact sl_three_dvd F (by decide)
  | linearThree F e => rw [Nat.card_congr e.toEquiv]; exact sl_three_dvd F (by decide)
  | symplectic F _ e =>
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_sp4_commutator.trans
      (card_subgroup_dvd_card _)
  | g2 F _ e =>
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model]
    have hq : ¬ 3 ∣ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
    have hm : Nat.card F.Carrier % 3 = 1 ∨ Nat.card F.Carrier % 3 = 2 := by omega
    have hs : (Nat.card F.Carrier ^ 2) % 3 = 1 := by
      rcases hm with hm | hm <;> simp [pow_two, Nat.mul_mod, hm]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
  | alternating n hn e =>
    rw [Nat.card_congr e.toEquiv]
    exact alternating_three_dvd n (by rcases hn with h | h | h | h <;> omega)
  | linearFiveTwo e =>
    rw [Nat.card_congr e.toEquiv]
    exact sl_three_dvd ChapterB.QuasisimpleSource.BinaryField.two (by decide)
  | tripleSix e _ =>
    have hc : Nat.card (center A) = 3 := (Nat.card_congr e.toEquiv).trans (by simp)
    exact hc ▸ card_subgroup_dvd_card (center A)

/-- The cubic survives in the actual two-core quotient of the source component. -/
theorem coreQuotient_three_dvd_from_source {G : Type*} [Group G] [Finite G]
    {H K R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K) :
    3 ∣ Nat.card (K ⧸ pCore 2 K) :=
  (star_model_from_source h).three_dvd.trans
    (card_dvd_of_surjective (coreToStar h.normalizes) (coreToStar_surjective h.normalizes))
end CFSG.Quasithin.ChapterC.C27Source
