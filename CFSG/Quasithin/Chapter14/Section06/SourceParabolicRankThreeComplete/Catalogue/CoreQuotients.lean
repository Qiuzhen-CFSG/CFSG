module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.AlternatingSixMS
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.SpecificGroups.G2.BinaryCentralCore
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# Recovering the intrinsic quotients of the selected C.2.7 component

The actual map from the two-core quotient onto the star image is a perfect
central cover. Cyclic odd Sylows remove its kernel in binary SL₂; the
existing perfect-cover theorems do the same for SL₃(2) and G₂(2)′.
For the triple-six model only the central quotient is recovered. In
particular this argument never discards the possible central cover of A₆.

Source: Aschbacher--Smith C.2.7(3), pp.146--147, and the catalogue
comparison in original 14.6.10(5), p.1029; perfect covers use I.1.2--3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H R M K : Subgroup G}

private noncomputable def starCover (h : Input KnownSimple.IsKnownSimple H R M K)
    {A : Type*} [Group A] (e : starImage K R K ≃* A) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) A := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  exact {
    toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
    surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact coreToStar_ker_central_from_source h }

/-- The binary rank-one star marking already identifies the full two-core
quotient; in particular no cubic kernel can be hidden by this marking. -/
theorem binary_two_core_quotient (h : Input KnownSimple.IsKnownSimple H R M K)
    (F : BinaryField) (e : starImage K R K ≃* SL(2,F.Carrier)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) := by
  let f := starCover h e
  have hnot : ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
    f.not_dvd_card_multiplier_of_odd_of_primeRank_le_one (by decide : Odd 3)
      (Matrix.SL2.binary_odd_primeRank_le_one (F := F.Carrier) (by decide : Odd 3))
  have hd := card_dvd_of_le f.ker_le_center
  have hc : Nat.card f.toMonoidHom.ker = 1 := by
    rcases coreQuotient_center_card_from_source h with hz | hz
    · rw [hz] at hd
      exact Nat.dvd_one.mp hd
    · rw [hz] at hd
      exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_right
        (fun he => hnot (by simpa only [he] using (dvd_refl 3)))
  have hk : f.toMonoidHom.ker = ⊥ := (Subgroup.card_eq_one.mp hc)
  exact ⟨MulEquiv.ofBijective f.toMonoidHom ⟨f.toMonoidHom.ker_eq_bot_iff.mp hk,f.surjective⟩⟩

/-- The perfect-cover theorem recovers the binary linear-three quotient. -/
theorem binary_three_core_quotient (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* SL(3,ZMod 2)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* SL(3,ZMod 2)) :=
  ⟨Matrix.PSL3Two.centralCoverEquiv (starCover h e) (pCore_quotient_pCore_eq_bot 2)⟩

/-- The ternary unitary cover theorem removes the actual G₂ star kernel. -/
theorem g2_core_quotient (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  let f := starCover h e
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  have hb : f.toMonoidHom.ker = ⊥ := bot_unique
    ((show f.toMonoidHom.ker ≤ pCore 2 (K ⧸ pCore 2 K) from
      le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2))
  exact ⟨MulEquiv.ofBijective f.toMonoidHom ⟨f.toMonoidHom.ker_eq_bot_iff.mp hb,f.surjective⟩⟩

/-- A triple-six star model identifies precisely the central-core quotient.
The cubic center is retained, not assumed to disappear. -/
theorem triple_six_central_quotient (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : (starImage K R K ⧸ center (starImage K R K)) ≃* alternatingGroup (Fin 6)) :
    Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : IsQuasisimple (starImage K R K) := (star_fitting_quasisimple (source_join_input h)).2
  let : IsSimpleGroup (starImage K R K ⧸ center (starImage K R K)) := IsQuasisimple.simple
  let : Nontrivial (starImage K R K) := (QuotientGroup.mk'_surjective (center _)).nontrivial
  exact ⟨(centralPreimageQuotientEquiv (pCore 2 K)).trans
    ((IsQuasisimple.centralQuotientEquiv (coreToStar h.normalizes)
      (coreToStar_surjective h.normalizes)).trans e)⟩

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
