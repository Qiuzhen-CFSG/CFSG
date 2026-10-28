module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Quotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Local
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeJoinCore

/-!
# The odd ternary core reduction on the original marked source pair

The original characteristic subgroup gives the literal normalizer quotient.
Restrict its original full Sylow to the containing component, retaining the
actual intersection and normalization. For an explicit special-linear or
special-unitary containing carrier, A.3.21 makes the entire local join's
two-core trivial and identifies the smaller quotient image's Fitting subgroup
with its defining-prime core. No marked case-(10) consequence is used.

The containing-carrier witness remains explicit. Choosing it (or lifting a
projective carrier), constructing the elementary kernel and marking its SL₂
quotient remain separate source obligations.

Source: Aschbacher--Smith A.3.21, printed pp.55--56, applied to the pair from
Proposition 1.3.8, printed pp.512--513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem actual_local_pair
    {p : ℕ} {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData KnownSimple.IsKnownSimple p 5 L T C K) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
    let D := quotientImage K N
    ∃ S : Sylow 2 (XiQuotient N),
      (S : Subgroup (XiQuotient N)) =
        ((T : Subgroup G).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) ∧
      B ∈ localCComponents S ∧
      (S : Subgroup (XiQuotient N)) ≤ normalizer (B : Set (XiQuotient N)) ∧
      B < D ∧ ¬ IsQuasisimple (B ⧸ pCore 2 B) := by
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  let q := QuotientGroup.mk' (pCore 2 N)
  let := h.characteristic
  have hstrict : Y < K := lt_of_le_of_ne h.contains_Y (by
    intro he
    apply h.nonnormal_xi
    rw [←he]
    exact xi_normal_in_intermediate p (normalizerResidual_le L R))
  have hTN : (T : Subgroup G) ≤ N :=
    (t_le_normalizer_radicalCore p L T).trans
      (normalizer_le_normalizer_characteristic_image R C)
  have hYN : Y ≤ N := h.contains_Y.trans h.component.1
  let S : Sylow 2 N := T.subtype hTN
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN,h.local_Y⟩
  let := pCore_isNilpotent (p := 2) (G := N)
  have hlocal : (Y.subgroupOf N).map q ∈ localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))) := by
    simpa only [Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hYL
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hYN]
    exact comap_mono (t_le_normalizer_Y p h.invariant)
  obtain ⟨hs,hn⟩ := Alternatives.actual_image_strict_and_not_quasisimple
    T hTN h.local_Y h.component.1 h.component.2 hstrict h.nonsimple_Y
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N)),rfl,hlocal,?_,hs,hn⟩
  exact (map_mono (f := q) hSY).trans ((Y.subgroupOf N).le_normalizer_map q)

/-- On the actual marked source pair, a genuine signed odd ternary containing
model gives the zero two-core of the full restricted Sylow join and identifies
the Fitting subgroup of the literal quotient image. -/
theorem actual_oddThree_core_and_fitting
    {p q : ℕ} [Fact q.Prime] (hq : Odd q)
    {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData KnownSimple.IsKnownSimple p 5 L T C K)
    (hm : let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
      let D := quotientImage K N
      Nonempty (D ≃* SL(3,ZMod q)) ∨ Nonempty (D ≃* RankThreeSU q)) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
    let D := quotientImage K N
    ∃ S : Sylow 2 D,
      (S : Subgroup D) =
        (((T : Subgroup G).subgroupOf N).map
          (QuotientGroup.mk' (pCore 2 N))).subgroupOf D ∧
      B.subgroupOf D ∈ localCComponents S ∧
      (S : Subgroup D) ≤ normalizer (B.subgroupOf D : Set D) ∧
      pCore 2 (B.subgroupOf D ⊔ (S : Subgroup D) : Subgroup D) = ⊥ ∧
      fittingSubgroup B = pCore q B := by
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
  let D := quotientImage K N
  obtain ⟨Tbar,hTbar,hl,hTB,hBD,hn⟩ := actual_local_pair h
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := h.component.2.map_quotient (pCore 2 N)
  obtain ⟨S,hS,hlS,hnS⟩ := SourceEmbeddings.exists_local_sylow_normalizing
    Tbar hl hD.subnormal hBD.le hTB
  let e : B.subgroupOf D ≃* B := subgroupOfEquivOfLe hBD.le
  have hn' : ¬ IsQuasisimple ((B.subgroupOf D) ⧸ pCore 2 (B.subgroupOf D)) := by
    intro hh
    let := hh
    exact hn (IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)))
  have hDQ : IsSQTK KnownSimple.IsKnownSimple D :=
    (characteristic_normalizer_quotient_sqtk h.ambient p L T C h.nontrivial).subgroup D
  have hout : pCore 2 (B.subgroupOf D ⊔ (S : Subgroup D) : Subgroup D) = ⊥ ∧
      fittingSubgroup (B.subgroupOf D) = pCore q (B.subgroupOf D) := by
    change Nonempty (D ≃* SL(3,ZMod q)) ∨ Nonempty (D ≃* RankThreeSU q) at hm
    rcases hm with hh | hh
    · obtain ⟨k⟩ := hh
      exact SourceEmbeddings.rankThree_local_core_and_fitting hDQ hq
        (sl3_local_structure q hq) k.toMonoidHom k.injective S hlS hn'
    · obtain ⟨k⟩ := hh
      exact SourceEmbeddings.rankThree_local_core_and_fitting hDQ hq
        (su3_local_structure q hq) k.toMonoidHom k.injective S hlS hn'
  refine ⟨S,hS.trans (congrArg (fun X : Subgroup (XiQuotient N) => X.subgroupOf D) hTbar),
    hlS,hnS,hout.1,?_⟩
  have hf := congrArg (map e.toMonoidHom) hout.2
  rw [map_fitting_equiv e, pCore_map_iso q e] at hf
  exact hf

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
