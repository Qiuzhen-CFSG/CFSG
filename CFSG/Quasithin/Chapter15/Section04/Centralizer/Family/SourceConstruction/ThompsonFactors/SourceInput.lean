module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.SourceLift
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.Selection
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.MovedRank
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonSource

/-!
# Constructing the original module input from solvable Thompson factors

The selected alternating cubic product is transported through the literal
centralizer quotient to M/O₂(M), then lifted by the two-residual. Its actual
Sylow irreducibility gives source-family membership, and the same marked
quotient identifies the elementary quotient of order 3^s. The original
commutator module has rank 2s by the natural factor action.

This constructs a genuine ModuleStructure.Input for every noncentral
maximal local. Noncentrality is source 15.4.11(3), proved by the independent
minimal-parabolic application, and B.2.16 remains its full earlier theorem.
Source: Aschbacher--Smith, 15.4.12, printed pp.1160--1161.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource ModuleStructure
open CentralizerWitness.SupercriticalNineSource
open LocalSetup.TwoFactors.SourceFactors.Permutation
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem irreducible_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (R U : Subgroup A)
    (hirr : ∀ D : Subgroup A, D ≤ R → U ≤ normalizer (D : Set A) → D = ⊥ ∨ D = R) :
    ∀ C : Subgroup B, C ≤ R.map e.toMonoidHom →
      U.map e.toMonoidHom ≤ normalizer (C : Set B) → C = ⊥ ∨ C = R.map e.toMonoidHom := by
  intro C hCR hn
  let D := C.comap e.toMonoidHom
  have hDR : D ≤ R := by
    simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] using comap_mono (f := e.toMonoidHom) hCR
  have hUD : U ≤ normalizer (D : Set A) := by
    apply le_normalizer_iff.mpr
    intro u hu d hd
    change e (u*d*u⁻¹) ∈ C
    simpa only [map_mul,map_inv] using
      le_normalizer_iff.mp hn (e u) (mem_map_of_mem e.toMonoidHom hu) (e d) hd
  have hmap : D.map e.toMonoidHom = C := map_comap_eq_self_of_surjective e.surjective C
  rcases hirr D hDR hUD with hb | ht
  · left
    simpa only [hb, Subgroup.map_bot] using hmap.symm
  · right
    exact hmap.symm.trans (congrArg (map e.toMonoidHom) ht)

/-- The actual exceptional datum constructs a member and every field of the
original source module input; no family witness or rank premise is assumed. -/
theorem source_input_of_exceptional {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hsol : Group.IsSolvable M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmoved : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))]
    (d : Exceptional (T.subtype hTM)) (hc : d.count = 1 ∨ d.count = 2) :
    ∃ X : Subgroup G, ∃ s : ℕ, Input κ T M X s := by
  obtain ⟨I, hI, hRN, hirr⟩ := exists_irreducible_cubicProduct d hc
  let R := cubicProduct d I
  let e := ThompsonSource.coreQuotientEquiv T M hTM hC
  let A := R.map e.toMonoidHom
  let : R.Normal := hRN
  let : A.Normal := hRN.map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 3 R := cubicProduct_elementary d I hI
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.of_surjective
    (R.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (R.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have hAc : Nat.card A = 3^I.card := by
    rw [show A = R.map e.toMonoidHom from rfl,card_map_of_injective e.injective]
    exact cubicProduct_card d I hI
  have hq : e.toMonoidHom.comp (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure
      (T.subtype hTM))) = quotientMap M := by
    ext m
    exact ThompsonSource.coreQuotientEquiv_apply T M hTM hC m
  have hS : (sylowStar (S := T.subtype hTM)).map e.toMonoidHom = image M (T : Subgroup G) := by
    change ((T.subtype hTM : Subgroup M).map _).map _ = _
    rw [map_map,hq]
    rfl
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
    (sSup_le fun _ h => h.1).trans hTM
  have hJ : elementaryAbelianMaxJ (T.subtype hTM : Subgroup M) =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [← elementaryAbelianMaxJ_map_injective _ M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,map_subgroupOf_eq_of_le hJM]
  have hJq : (sylowImage (S := T.subtype hTM)).map e.toMonoidHom =
      image M (elementaryAbelianMaxJ (T : Subgroup G)) := by
    change ((elementaryAbelianMaxJ (T.subtype hTM : Subgroup M)).map
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)))).map e.toMonoidHom = _
    rw [map_map,hq,hJ]
    rfl
  have hAi : ∀ C : Subgroup (CoreQuotient M), C ≤ A →
      image M (T : Subgroup G) ≤ normalizer (C : Set (CoreQuotient M)) → C = ⊥ ∨ C = A := by
    rw [← hS]
    exact irreducible_map_equiv e R (sylowStar (S := T.subtype hTM)) hirr
  have hAj : ⁅A,image M (elementaryAbelianMaxJ (T : Subgroup G))⁆ = A := by
    rw [← hJq,show A = R.map e.toMonoidHom from rfl,← map_commutator]
    exact congrArg (map e.toMonoidHom) (selected_commutator d I hRN)
  have hEC := hG.evenCharacteristic T M hM hTM
  have hY := normal_elementary_lift_mem_Y T M hTM hEC A hI hAc hAi hAj
  have hAp : IsPPerfect 2 A := by
    apply (pResidual_eq_top_iff 2 A).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      (((IsElementaryAbelian.isPGroup 3 A).orderOf_coprime (by decide : Nat.Coprime 3 2) x).symm)
  obtain ⟨f,hf⟩ := normal_lift_quotient M A hAp
  have hstar : (residualPreimage (quotientMap M) A).map
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))) = R := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_map,hq]
    exact residualPreimage_image (quotientMap M) (QuotientGroup.mk'_surjective _) A hAp
  have hr := actual_moved_rank_map d I hI (residualPreimage (quotientMap M) A)
    hstar M.subtype M.subtype_injective
  rw [ThompsonSource.closure_eq_internalModule] at hr
  refine ⟨lift M A, I.card, ⟨hG,hM,hTM,hsol,hC,hmoved,hY,lift_le M A,
    lift_normal M A inferInstance,hI,?_,?_,hr⟩⟩
  · exact IsElementaryAbelian.of_surjective f.symm.toMonoidHom f.symm.surjective
  · exact (Nat.card_congr f.toEquiv).trans hAc

/-- The actual B.2.16 application and its checked quotient/factor construction
supply a source member in every noncentral maximal local overgroup. -/
theorem source_input_of_noncentral {κ : GroupClass}
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hsol : Group.IsSolvable M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmoved : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥) :
    ∃ X : Subgroup G, ∃ s : ℕ, Input κ T M X s := by
  obtain ⟨hE,d,hc⟩ := ThompsonSource.exceptional hB hG T M hM hTM hsol hC hmoved
  let := hE
  exact source_input_of_exceptional hG T M hM hTM hsol hC hmoved d hc

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
