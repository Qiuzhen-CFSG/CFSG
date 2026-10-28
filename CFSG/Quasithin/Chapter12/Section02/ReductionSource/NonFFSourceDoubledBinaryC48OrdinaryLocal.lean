module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryModels
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The two original normalizers in the ordinary C.3.5 quotient

The full center of the selected ordinary component is its two-core and lies
in the original radical. The intersection of that radical with the component
therefore descends to a nontrivial radical subgroup of the central quotient.
Its normalizer lifts exactly. Separately, perfect central descent identifies
the full normalizer of the original residual image with the original local
intersection. The two normalizers are retained separately: source C.3.5 must
still establish their required relationship using the actual parabolic models.

Source: Aschbacher--Smith C.3.5, printed p.150, with the literal original
reciprocal witness in the Chapter 12 doubled-binary application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual radical intersection and residual have separately marked
normalizers in the full central quotient of the original ordinary component. -/
theorem sourceOrbit_binary_witness_ordinary_local_normalizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let X := (LH.subgroupOf H).subgroupOf K
    let R := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
    let M := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    center K ≤ R ∧ IsPRadical 2 (R.map q) ∧
      (normalizer (R.map q : Set (K ⧸ center K))).comap q = normalizer (R : Set K) ∧
      (normalizer (X.map q : Set (K ⧸ center K))).comap q = M ∧
      normalizer (X.map q : Set (K ⧸ center K)) = M.map q ∧
      X.map q ≤ normalizer (R.map q : Set (K ⧸ center K)) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let X := (LH.subgroupOf H).subgroupOf K
  let R := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
  let M₀ := H ⊓ normalizer (L : Set G)
  let M := (M₀.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLK : LH.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH M₀ = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  have hZR : center K ≤ R := by
    intro z hzmem
    have hp : (z : H) ∈ pCore 2 H :=
      (pCoreIn_le_of_subnormal 2 hK.1)
        (mem_map_of_mem K.subtype (hz ▸ hzmem))
    exact hc.ambient_core_le_radical (mem_map_of_mem H.subtype hp)
  have hk : q.ker ≤ R := by simpa only [q,QuotientGroup.ker_mk'] using hZR
  have hR := hc.ordinary_radical_intersection_isRadical K hK
  have hlocal := hc.ordinary_quotient_local_data K hK
  rw [hspan] at hlocal
  have hrad : IsPRadical 2 (R.map q) :=
    ⟨hlocal.2.2.1,map_normalizer_core_of_p_kernel R hR.isPGroup hR.2
      q (QuotientGroup.mk'_surjective _) hk⟩
  have hNR : (normalizer (R.map q : Set (K ⧸ center K))).comap q =
      normalizer (R : Set K) := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq_self hk]
  have hNX : normalizer (X : Set K) = M := by
    dsimp only [X,M]
    rw [←subgroupOf_normalizer_eq hLK,←subgroupOf_normalizer_eq hLH]
    have he := hc.normalizer_span_eq
    rw [hspan] at he
    change H ⊓ normalizer (LH : Set G) = M₀ at he
    rw [←he]
    ext k
    exact ⟨fun hk => ⟨(k : H).property,hk⟩,fun hk => hk.2⟩
  have hpLH : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let := hpLH
  let e : X ≃* LH := (subgroupOfEquivOfLe hLK).trans (subgroupOfEquivOfLe hLH)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hNQ : (normalizer (X.map q : Set (K ⧸ center K))).comap q = M := by
    rw [comap_normalizer_map_eq_of_perfect q (by rw [QuotientGroup.ker_mk']) X,hNX]
  refine ⟨hZR,hrad,hNR,hNQ,?_,hlocal.2.2.2.1⟩
  change normalizer (X.map q : Set (K ⧸ center K)) = M.map q
  rw [←hNQ,map_comap_eq_self]
  rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact le_top

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
