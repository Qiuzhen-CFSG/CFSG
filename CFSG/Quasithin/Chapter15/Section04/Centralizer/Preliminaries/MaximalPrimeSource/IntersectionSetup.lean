module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.CoreContainment
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The normalizer residual and the intersection alternative

For K = O₂,F(M), the quotient of Y = O²(N_K(X)) is exactly N_F(M*)(X*).
The Fitting subgroup has odd order and is nilpotent, giving the relative
subnormality and centralizer containment needed for case (b) of A.4.4.
No normality of X in M is asserted.

Source: Aschbacher–Smith, printed p.1157, proof of 15.4.3(1).
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterG.Section08
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

private theorem nilpotent_subnormal {D : Type*} [Group D] [Finite D]
    [Group.IsNilpotent D] (A : Subgroup D) : A.IsSubnormal := by
  classical
  refine (measure (fun B : Subgroup D => Nat.card D - Nat.card B)).wf.induction A ?_
  intro B ih
  by_cases ht : B = ⊤
  · simp [ht]
  · have hlt : B < normalizer (B : Set D) :=
      Group.normalizerCondition_of_isNilpotent B (lt_top_iff_ne_top.mpr ht)
    have hcard : Nat.card B < Nat.card (normalizer (B : Set D)) := by
      exact Set.Finite.card_lt_card (Set.toFinite _) hlt
    have hbound : Nat.card (normalizer (B : Set D)) ≤ Nat.card D := card_le_card_group _
    exact IsSubnormal.step B _ hlt.le (ih _ (by change Nat.card D - _ < Nat.card D - _; omega)) inferInstance

/-- Taking the two-residual commutes with the literal quotient image. -/
theorem quotientImage_residual {M A : Subgroup G} (hAM : A ≤ M) :
    quotientImage M ((pResidual 2 A).map A.subtype) =
      (pResidual 2 (quotientImage M A)).map (quotientImage M A).subtype := by
  have he : ((pResidual 2 A).map A.subtype).subgroupOf M =
      (pResidual 2 (A.subgroupOf M)).map (A.subgroupOf M).subtype := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hAM),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hAM]
  unfold quotientImage
  rw [he, map_embedded_pResidual]

@[expose] def fittingNormalizer (M X : Subgroup G) : Subgroup G :=
  twoFittingPreimage M ⊓ normalizer (X : Set G)

@[expose] def normalizerResidual (M X : Subgroup G) : Subgroup G :=
  (pResidual 2 (fittingNormalizer M X)).map (fittingNormalizer M X).subtype

omit [Finite G] in
/-- The intrinsic normalizer inside the actual Fitting quotient. -/
theorem quotientImage_fittingNormalizer (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    quotientImage M (fittingNormalizer M X) =
      fittingSubgroup (M ⧸ pCore 2 M) ⊓ normalizer (quotientImage M X : Set _) := by
  let q := QuotientGroup.mk' (pCore 2 M)
  have he : (fittingNormalizer M X).subgroupOf M =
      (fittingSubgroup (M ⧸ pCore 2 M) ⊓ normalizer (quotientImage M X : Set _)).comap q := by
    rw [comap_inf, (xi_quotient_normalizers T hX hXM).1,
      ← subgroupOf_normalizer_eq (le_sup_left.trans hXM)]
    rw [fittingNormalizer, subgroupOf, comap_inf]
    congr 1
    exact comap_map_eq_self_of_injective M.subtype_injective _
  change ((fittingNormalizer M X).subgroupOf M).map q = _
  rw [he, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- K* has odd order, so passing to O² leaves the quotient normalizer unchanged. -/
theorem quotientImage_normalizerResidual (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    quotientImage M (normalizerResidual M X) =
      fittingSubgroup (M ⧸ pCore 2 M) ⊓ normalizer (quotientImage M X : Set _) := by
  have hNM : fittingNormalizer M X ≤ M := inf_le_left.trans (map_subtype_le _)
  rw [normalizerResidual, quotientImage_residual hNM, quotientImage_fittingNormalizer T hX hXM]
  have ho : Odd (Nat.card ↥(fittingSubgroup (M ⧸ pCore 2 M) ⊓
      normalizer (quotientImage M X : Set (M ⧸ pCore 2 M)))) :=
    (fitting_odd_of_twoCore_eq_bot (pCore_quotient_pCore_eq_bot 2)).of_dvd_nat
      (card_dvd_of_le inf_le_left)
  have ht : pResidual 2 ↥(fittingSubgroup (M ⧸ pCore 2 M) ⊓
      normalizer (quotientImage M X : Set (M ⧸ pCore 2 M))) = ⊤ := by
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime (ho.coprime_two_left.of_dvd_right
      (_root_.orderOf_dvd_natCard x))
  rw [ht, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
/-- The source subgroup Y contains X and lies in the intersection. -/
theorem normalizerResidual_bounds (T : Sylow 2 G) {X M H : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXF : X ≤ twoFittingPreimage M)
    (hNH : normalizer (X : Set G) ≤ H) :
    X ≤ normalizerResidual M X ∧ normalizerResidual M X ≤ M ⊓ H := by
  have hXN : X ≤ fittingNormalizer M X := le_inf hXF X.le_normalizer
  have hx : (pResidual 2 X).map X.subtype = X := by
    rw [(pResidual_eq_top_iff 2 X).mpr hX.2.1, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨?_, (map_subtype_le _).trans ?_⟩
  · exact hx.symm.le.trans (embedded_pResidual_mono 2 hXN)
  · exact le_inf (inf_le_left.trans (map_subtype_le _)) (inf_le_right.trans hNH)

/-- The literal case (b) input to A.4.4. The only containment used here
is the proved placement of X in the quotient Fitting subgroup. -/
theorem normalizerResidual_intersectionAlternative (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (hs : Group.IsSolvable M) (hXF : X ≤ twoFittingPreimage M) :
    ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage M
        (normalizerResidual M X ⊔ M.pCoreIn 2)) := by
  let Q := M ⧸ pCore 2 M
  have hYM : normalizerResidual M X ≤ M :=
    (map_subtype_le _).trans (inf_le_left.trans (map_subtype_le _))
  have he : ChapterA.Section04.twoCoreQuotientImage M
      (normalizerResidual M X ⊔ M.pCoreIn 2) = quotientImage M (normalizerResidual M X) := by
    unfold ChapterA.Section04.twoCoreQuotientImage quotientImage
    rw [subgroupOf_sup hYM (pCoreIn_le 2 M), Subgroup.map_sup]
    have hc : (M.pCoreIn 2).subgroupOf M = pCore 2 M :=
      comap_map_eq_self_of_injective M.subtype_injective _
    rw [hc, QuotientGroup.map_mk'_self, sup_bot_eq]
  rw [he, quotientImage_normalizerResidual T hX hXM]
  let : Group.IsSolvable M := hs
  have hf : generalizedFitting Q = fittingSubgroup Q := by
    have e := congrArg (quotientImage M) (twoFittingPreimage_eq_generalized M hs)
    rw [quotientImage_twoFittingPreimage] at e
    exact (e.trans (ChapterA.Section04.twoCoreQuotientImage_fittingPreimage M)).symm
  refine Or.inr ⟨inf_le_left.trans_eq hf.symm, ?_, ?_⟩
  · rw [hf]
    exact nilpotent_subnormal _
  · apply (closure_le _).mpr
    intro x hx
    have hXX : quotientImage M X ≤ fittingSubgroup Q ⊓
        normalizer (quotientImage M X : Set _) := by
      refine le_inf ?_ le_normalizer
      have hm := map_mono (f := QuotientGroup.mk' (pCore 2 M)) (comap_mono (f := M.subtype) hXF)
      exact hm.trans_eq (quotientImage_twoFittingPreimage M)
    refine ⟨hf ▸ hx.1.1, ?_⟩
    exact Subgroup.centralizer_le_normalizer _ ((centralizer_le hXX) hx.1.2)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
