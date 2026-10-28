module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Models
public import Theory.GroupTheory.CComponent.BinaryRankTwo
public import Theory.GroupTheory.CComponent.NormalPair
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Terminal components and residuals from their individual models

Assume the solvable radical is the two-core, the three-rank is at most two,
and every C-component has actual two-core quotient L₃(2) or A₆. Pass to the
radical-free quotient. Independent component ranks leave one component, or
two L₃(2) components. Multiplication gives an actual isomorphism of the layer
with L₃(2), A₆, or L₃(2) × L₃(2). Its outer group is a two-group, so it is
the solvable residual; this equality lifts through the original two-core.

If a component in the pair is not normal, its normalizer has index two.
An actual Sylow two-element therefore exchanges the components. Otherwise
both components are normal. The exported alternatives retain set products
and conjugation by the inverse of the chosen Sylow element.

These prove the rank/structure implication in Aschbacher--Smith 14.6.21 and
the model input to 14.6.23(1), printed pp.1037--1038. The individual model
classification in 14.6.20 is still an explicit premise, discharged by the
assembly owner qt-e-suitable-component-supports.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
variable {G : Type*} [Group G] [Finite G]

/-- Actual isomorphisms transport the intrinsic two-core model alternatives. -/
theorem ComponentQuotientModels.transport {A B : Type*} [Group A] [Group B]
    (h : ComponentQuotientModels A) (e : A ≃* B) : ComponentQuotientModels B := by
  let f := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rcases h with h | h
  · exact Or.inl ⟨f.symm.trans (Classical.choice h)⟩
  · exact Or.inr ⟨f.symm.trans (Classical.choice h)⟩

private theorem model_rank_pos {D : Type*} [Group D] [Finite D]
    (hm : Nonempty (D ≃* Matrix.PSL3Two.SL) ∨ Nonempty (D ≃* alternatingGroup (Fin 6))) :
    0 < primeRank 3 D := by
  rcases hm with hm | hm
  · let e := Classical.choice hm
    rw [primeRank_congr 3 e]
    apply Nat.pos_of_ne_zero
    intro hz
    have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [Matrix.PSL3Two.card_SL] at hn
    exact hn (by decide)
  · let e := Classical.choice hm
    have hb := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
    rw [primeRank_congr 3 e]
    omega

private theorem pair_models_linear
    (hR : solvableRadical G = ⊥) (hr : primeRank 3 G ≤ 2)
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : Nonempty (B ≃* Matrix.PSL3Two.SL) ∨ Nonempty (B ≃* alternatingGroup (Fin 6)))
    (hc : Nonempty (C ≃* Matrix.PSL3Two.SL) ∨ Nonempty (C ≃* alternatingGroup (Fin 6))) :
    Nonempty (B ≃* Matrix.PSL3Two.SL) ∧ Nonempty (C ≃* Matrix.PSL3Two.SL) := by
  have hadd := hB.primeRank_pair_le (p := 3) hR hC hne
  have hbp := model_rank_pos hb
  have hcp := model_rank_pos hc
  have ha := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
  constructor
  · rcases hb with hb | hb
    · exact hb
    · rw [← primeRank_congr 3 (Classical.choice hb)] at ha
      omega
  · rcases hc with hc | hc
    · exact hc
    · rw [← primeRank_congr 3 (Classical.choice hc)] at ha
      omega

private theorem radicalFree_layer_models
    (hR : solvableRadical G = ⊥) (hr : primeRank 3 G ≤ 2)
    (hm : ∀ B : Subgroup G, B.IsCComponent →
      Nonempty (B ≃* Matrix.PSL3Two.SL) ∨ Nonempty (B ≃* alternatingGroup (Fin 6)))
    (K : Subgroup G) (hK : K.IsCComponent) :
    ResidualQuotientModels (cComponentLayer G) := by
  classical
  by_cases hu : ∀ D : Subgroup G, D.IsCComponent → D = K
  · have he : cComponentLayer G = K := le_antisymm
      (sSup_le fun D hD => (hu D hD).le) (le_cComponentLayer hK)
    rcases hm K hK with hs | hs
    · exact Or.inl ⟨(MulEquiv.subgroupCongr he).trans (Classical.choice hs)⟩
    · exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr he).trans (Classical.choice hs)⟩)
  · push Not at hu
    obtain ⟨C,hC,hCK⟩ := hu
    have hall (D : Subgroup G) (hD : D.IsCComponent) :=
      hK.eq_or_eq_of_rank_two (p := 3) hR hr
        (fun D hD => model_rank_pos (hm D hD)) hC hCK.symm hD
    have he := cComponentLayer_eq_sup_of_pair hK hC hall
    obtain ⟨⟨a⟩,⟨b⟩⟩ := pair_models_linear hR hr hK hC hCK.symm (hm K hK) (hm C hC)
    obtain ⟨f,_⟩ := hK.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR
      (hK.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hC hCK.symm)
    exact Or.inr (Or.inr ⟨(MulEquiv.subgroupCongr he).trans
      (f.symm.trans (a.prodCongr b))⟩)

/-- Individual component models determine the full residual quotient and its component generation. -/
theorem component_models_residual
    (hR : solvableRadical G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (hm : ∀ B : Subgroup G, B.IsCComponent → ComponentQuotientModels B)
    (K : Subgroup G) (hK : K.IsCComponent) :
    cComponentLayer G = solvableResidual G ∧
      ResidualQuotientModels (solvableResidual (G ⧸ pCore 2 G)) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hQ : solvableRadical Q = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hrQ : primeRank 3 Q ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr
  have hmQ (B : Subgroup Q) (hB : B.IsCComponent) :
      Nonempty (B ≃* Matrix.PSL3Two.SL) ∨ Nonempty (B ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨D,hD,rfl⟩ := hB.exists_map_quotient_eq (pCore 2 G)
    rcases hm D hD with hs | hs
    · exact Or.inl ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans (Classical.choice hs)⟩
    · exact Or.inr ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans (Classical.choice hs)⟩
  have hmod := radicalFree_layer_models hQ hrQ hmQ (K.map q) (hK.map_quotient _)
  let : Group.IsPerfect (cComponentLayer Q) := cComponentLayer_isPerfect
  have he := cComponentLayer_eq_residual_of_radical_eq_bot_of_outer_two hQ hmod.outer_isTwoGroup
  exact ⟨cComponentLayer_eq_residual_of_quotient (pCore 2 G) he, he ▸ hmod⟩

/-- Two distinct components exhaust the family and both have binary linear-three quotient. -/
theorem component_pair_models
    (hR : solvableRadical G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (hm : ∀ B : Subgroup G, B.IsCComponent → ComponentQuotientModels B)
    {K C : Subgroup G} (hK : K.IsCComponent) (hC : C.IsCComponent) (hne : K ≠ C) :
    (∀ D : Subgroup G, D.IsCComponent → D = K ∨ D = C) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.SL) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hQ : solvableRadical Q = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hrQ : primeRank 3 Q ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr
  have hmQ (B : Subgroup Q) (hB : B.IsCComponent) :
      Nonempty (B ≃* Matrix.PSL3Two.SL) ∨ Nonempty (B ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨D,hD,rfl⟩ := hB.exists_map_quotient_eq (pCore 2 G)
    rcases hm D hD with hs | hs
    · exact Or.inl ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans (Classical.choice hs)⟩
    · exact Or.inr ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans (Classical.choice hs)⟩
  have hKq := hK.map_quotient (pCore 2 G)
  have hCq := hC.map_quotient (pCore 2 G)
  have hneq : K.map q ≠ C.map q := fun he => hne (hK.eq_of_map_quotient_eq hC _ he)
  have hall (D : Subgroup Q) (hD : D.IsCComponent) :=
    hKq.eq_or_eq_of_rank_two (p := 3) hQ hrQ
      (fun D hD => model_rank_pos (hmQ D hD)) hCq hneq hD
  obtain ⟨⟨a⟩,⟨b⟩⟩ := pair_models_linear hQ hrQ hKq hCq hneq
    (hmQ _ hKq) (hmQ _ hCq)
  refine ⟨?_,⟨(cComponentTwoCoreQuotientEquiv hK).trans a⟩,
    ⟨(cComponentTwoCoreQuotientEquiv hC).trans b⟩⟩
  intro D hD
  rcases hall _ (hD.map_quotient (pCore 2 G)) with h | h
  · exact Or.inl (hD.eq_of_map_quotient_eq hK _ h)
  · exact Or.inr (hD.eq_of_map_quotient_eq hC _ h)

omit [Finite G] in
private theorem normal_partner_of_normal
    {K C : Subgroup G} (hC : C.IsCComponent) (hne : K ≠ C) [K.Normal]
    (hall : ∀ D : Subgroup G, D.IsCComponent → D = K ∨ D = C) : C.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  rcases hall _ (hC.map_equiv (MulAut.conj g)) with he | he
  · exfalso
    have hk : K.map (MulAut.conj g).toMonoidHom = K :=
      normal_iff_map_conj_eq.mp inferInstance g
    exact hne ((map_injective (MulAut.conj g).injective) (hk.trans he.symm))
  · exact he

open scoped Pointwise in
/-- The source one-component, exchanged-pair and relatively normal pair alternatives. -/
theorem component_models_alternatives
    (hR : solvableRadical G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (hm : ∀ B : Subgroup G, B.IsCComponent → ComponentQuotientModels B)
    (S : Sylow 2 G) (K : Subgroup G) (hK : K.IsCComponent) :
    (solvableResidual G = K ∧ ComponentQuotientModels K) ∨
      (Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
        ∃ t ∈ (S : Subgroup G), t ∉ normalizer (K : Set G) ∧
          (solvableResidual G : Set G) =
            (K : Set G) * (K.map (MulAut.conj t⁻¹).toMonoidHom : Set G)) ∨
      (Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
        ∃ C : Subgroup G, C.IsCComponent ∧ C ≠ K ∧ K.Normal ∧ C.Normal ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.SL) ∧
          (solvableResidual G : Set G) = (K : Set G) * (C : Set G)) := by
  classical
  have hl := (component_models_residual hR hr hm K hK).1
  by_cases hu : ∀ C : Subgroup G, C.IsCComponent → C = K
  · have he : cComponentLayer G = K := le_antisymm
      (sSup_le fun C hC => (hu C hC).le) (le_cComponentLayer hK)
    exact Or.inl ⟨hl.symm.trans he,hm K hK⟩
  · push Not at hu
    obtain ⟨C,hC,hCK⟩ := hu
    obtain ⟨hall,hkm,hcm⟩ := component_pair_models hR hr hm hK hC hCK.symm
    have he : solvableResidual G = K ⊔ C :=
      hl.symm.trans (cComponentLayer_eq_sup_of_pair hK hC hall)
    have hp : (solvableResidual G : Set G) = (K : Set G) * (C : Set G) :=
      (congrArg (fun A : Subgroup G => (A : Set G)) he).trans
        (coe_mul_of_right_le_normalizer_left K C
          ((le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hK)))
    by_cases hn : K.Normal
    · let := hn
      exact Or.inr (Or.inr ⟨hkm,C,hC,hCK,hn,normal_partner_of_normal hC hCK.symm hall,hcm,hp⟩)
    · have hg : ∃ g : G, K ≠ K.conjBy g := by
        by_contra hh
        apply hn
        exact normal_iff_map_conj_eq.mpr (fun g => (not_exists.mp hh g |> not_not.mp).symm)
      obtain ⟨g,hg⟩ := hg
      have hgc : K.conjBy g = C := (hall _ (hK.map_equiv (MulAut.conj g))).resolve_left hg.symm
      have hnormal : (K ⊔ K.conjBy g).Normal := by
        rw [hgc,←he]
        infer_instance
      let := hnormal
      have hi := hK.normalizer_index_two_of_normal_pair g hg
      have hnot : ¬ (S : Subgroup G) ≤ normalizer (K : Set G) := by
        intro hh
        have hd := index_dvd_of_le hh
        rw [hi] at hd
        exact S.not_dvd_index hd
      obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hnot
      have hnti : t⁻¹ ∉ normalizer (K : Set G) := fun hh => hnt (inv_mem_iff.mp hh)
      have htc : K.map (MulAut.conj t⁻¹).toMonoidHom = C :=
        (hall _ (hK.map_equiv (MulAut.conj t⁻¹))).resolve_left
          (fun hh => hnti (mem_normalizer_iff_map_conj_eq.mpr hh))
      exact Or.inr (Or.inl ⟨hkm,t,ht,hnt,by rw [htc]; exact hp⟩)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
