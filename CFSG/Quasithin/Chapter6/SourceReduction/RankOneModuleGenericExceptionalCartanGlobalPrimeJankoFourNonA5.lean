module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddTernaryNonA5
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourSections

/-!
# Completing the smaller changed-Sylow exclusion

The literal selected right image is a local component normalized by the full
Sylow intersection with its ordinary J₄ container. The native recognition
therefore makes its intrinsic two-core quotient PSL₂(4), contrary to the
already proved A₅ exclusion. The selected pair now has only zero-core or
strictly larger changed-Sylow alternatives. The latter retains the original
component/parabolic distinction, Hall markings and field parameter.
The zero-core, larger-Sylow and higher-field normalization obligations remain.

Source: Aschbacher–Smith5.2.2, printed pp.648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The literal J₄ containing image forces the same selected right quotient to be PSL₂(4). -/
theorem LocalData.source_overcomponent_janko_four_right_four
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (_hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hm : let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      Nonempty (I ≃* Janko4.Model)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map π
  let Kbar := (K.subgroupOf X).map π
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map π)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map π ≤ _
    rw [heS]
    apply (map_mono (f := π) ?_).trans (le_normalizer_map π)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlocalbar hRKbar (hK.map_quotient (pCore 2 X)).subnormal
  let U := Rbar.subgroupOf Kbar
  have hnU : (Q : Subgroup Kbar) ≤ normalizer (U : Set Kbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hRKbar]
    exact comap_mono hn
  let r := π.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (π.subgroupMap_surjective _) hr
  let b := (subgroupOfEquivOfLe hRKbar).symm
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let eR : (R ⧸ pCore 2 R) ≃* (U ⧸ pCore 2 U) := e₁.trans (e₂.trans e₃)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := d.selected_right_simple h hH c hd hz hs
  let : IsSimpleGroup (U ⧸ pCore 2 U) := eR.symm.isSimpleGroup
  exact (JankoFourSections.right_quotient_four hm.some Q U hU hnU
    (d.right_quotient.of_equiv eR.symm)).of_mulEquiv eR

/-- The original prime pair has only the zero-core and strictly larger
changed-Sylow branches. Every smaller-Sylow container has been excluded. -/
theorem source_prime_pair_zero_or_largerSylow
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧ RemainingLargerSource H R p n)) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_janko_containing_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm,hp,hn⟩ | ⟨U,hU,hlt,hr⟩
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact (hn (d.source_overcomponent_janko_four_right_four h hH c hd hz hs hSyl
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK.le hK hm.2.2.2)).elim
  · exact .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hr⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
