module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpaces
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateCentralizers

/-!
# Uniqueness over the distinguished natural plane

The displacement formula for a natural Sylow shows that an invariant
four-subgroup is its fixed field line. For an arbitrary plane whose
normalizer contains an ambient Sylow, the ordinary-centralizer alternative
puts that normalizer inside M, so the same calculation applies. The field
alternative is impossible: its arranged normalizer Sylow is proper in an
ambient Sylow. Thus such a plane is an L-conjugate of Z_S.

Apply this to the inverse conjugate of Z_S inside the original layer.
The resulting transporter normalizes Z_S, hence normalizes the layer by
6.2.1. This proves LocalAnalysis.plane_unique without assuming the record.
The Chapter 12 companion discharges E.6.1 and the normalizer factorization.

Source: Aschbacher--Smith, 6.2.4(2), 6.2.5(3--4), printed pp.680--681.
Only the central-type part of the fusion assertion in (3) is needed here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_invariant_plane (L B U : Subgroup G) (hnat : IsNaturalModule L B 2)
    (hUB : U ≤ B) (hU : Nat.card U = 4) (S : Sylow 2 L)
    (hSU : (S : Subgroup L).map L.subtype ≤ normalizer (U : Set G)) :
    U = B ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
  let C := B ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)
  have hCcard : Nat.card C = 4 := (hnat.sylow_fixed_geometry S).1
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnat
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  obtain ⟨W, _, hWfix, _, hWonto⟩ :=
    Representation.SpecialLinearTwo.sylow_fixed_line_displacements 2 P
  have hfix (v : B) : (f v).toAdd ∈ W ↔ (v : G) ∈ C := by
    rw [hWfix]
    constructor
    · intro hv
      refine ⟨v.property, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have hh := hf s v
      have hfv := hv (q s) (mem_map.mpr ⟨s, hs, rfl⟩)
      change (Representation.specialLinearNatural 2 (q s)) (f v).toAdd = (f v).toAdd at hfv
      rw [show e (QuotientGroup.mk' (pCore 2 L) s) = q s from rfl,
        hfv, ofAdd_toAdd, f.symm_apply_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    · intro hv g hg
      obtain ⟨s, hs, rfl⟩ := hg
      have hh := hf s v
      have hc := hv.2 s (mem_map_of_mem L.subtype hs)
      have he : (s : G) * (v : G) * (s : G)⁻¹ = v := by
        rw [hc, mul_inv_cancel_right]
      rw [he] at hh
      have he' : f.symm (Multiplicative.ofAdd
          (Matrix.SpecialLinearGroup.toLin' (q s) (f v).toAdd)) = v := Subtype.ext hh
      have he'' := congrArg (fun b => (f b).toAdd) he'
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using he''
  apply eq_of_le_of_card_ge ?_ (by rw [hU, hCcard])
  by_contra hUC
  obtain ⟨u, hu, huC⟩ := SetLike.not_le_iff_exists.mp hUC
  have huW : (f ⟨u, hUB hu⟩).toAdd ∉ W := by simpa only [hfix] using huC
  have hCU : C ≤ U := by
    intro w hw
    obtain ⟨a, ha, haw⟩ := hWonto (f ⟨u, hUB hu⟩).toAdd huW
      (f ⟨w, hw.1⟩).toAdd ((hfix _).mpr hw)
    obtain ⟨s, hs, rfl⟩ := ha
    have he : ⁅(s : G), u⁆ = w := by
      have hh := hf s ⟨u, hUB hu⟩
      have ha' : Matrix.SpecialLinearGroup.toLin' (q s) (f ⟨u, hUB hu⟩).toAdd =
          (f ⟨w, hw.1⟩).toAdd + (f ⟨u, hUB hu⟩).toAdd := sub_eq_iff_eq_add.mp haw
      change (f.symm (Multiplicative.ofAdd
        (Matrix.SpecialLinearGroup.toLin' (q s) (f ⟨u, hUB hu⟩).toAdd)) : G) = _ at hh
      simp only [ha', ofAdd_add, ofAdd_toAdd, map_mul, MulEquiv.symm_apply_apply] at hh
      change w * u = (s : G) * u * (s : G)⁻¹ at hh
      change (s : G) * u * (s : G)⁻¹ * u⁻¹ = w
      rw [← hh, mul_inv_cancel_right]
    rw [← he]
    exact U.mul_mem ((mem_normalizer_iff.mp (hSU (mem_map_of_mem L.subtype hs)) u).mp hu)
      (U.inv_mem hu)
  have heq : C = U := eq_of_le_of_card_ge hCU (by rw [hCcard, hU])
  exact huC (heq.ge hu)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem normalizer_layer_centralizer_le
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R)) :
    normalizer (centralizer (layer L R : Set G) : Set G) ≤ M := by
  let B := layer L R
  let C := centralizer (B : Set G)
  let Q := C.pCoreIn 2
  let := hE.elementary
  have hBQ : B ≤ Q := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 B) B.le_centralizer (Subgroup.centralizer_le_normalizer _)
  have hQN := normalizer_le_normalizer_characteristic_image C (pCore 2 C)
  apply hQN.trans
  apply normalizer_le_of_unique_maximalTwoLocal hE.unique (isPGroup_pCoreIn 2 C)
  · intro he
    exact hE.nontrivial (bot_unique (hBQ.trans_eq he))
  · exact (inf_le_left.trans inf_le_right).trans
      ((normalizer_le_normalizer_centralizer B).trans hQN)

private theorem field_plane_no_full_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    {U : Subgroup G} (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUne : U ≠ ⊥) (P : Sylow 2 G) : ¬ (P : Subgroup G) ≤ normalizer (U : Set G) := by
  let := h.layer_elementary
  have hML := (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  obtain ⟨Q, _, hBQ, hQL, hQB, _, hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L M (layer L R) U n h.sylow_normalizes_layer hE.normalizer_le hML hE.ti
      hnat hfield hUne
  obtain ⟨_, _, ⟨S, hS⟩, _⟩ := field_fixedSpace_sylow_control hE
    (by have := h.n_gt_one; omega) hnat hML hfield hUne Q hBQ hQB hSyl
  intro hPN
  have hcS : Nat.card S = Nat.card (P.subtype hPN) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hc : Nat.card ((Q : Subgroup G) ⊓ normalizer (U : Set G) : Subgroup G) = Nat.card Q := by
    rw [← hS, card_map_of_injective (normalizer (U : Set G)).subtype_injective, hcS]
    change Nat.card ((P : Subgroup G).subgroupOf (normalizer (U : Set G))) = Nat.card Q
    rw [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv,
      Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hQN : (Q : Subgroup G) ≤ normalizer (U : Set G) :=
    (eq_of_le_of_card_ge (show (Q : Subgroup G) ⊓ normalizer (U : Set G) ≤ Q from inf_le_left)
      hc.ge).symm.le.trans inf_le_right
  obtain ⟨S₀, hS₀⟩ := NormalSylowQuotientAction.intersection_sylow Q L hQL
  apply field_fixedSpace_not_normalized_by_sylow hnat hfield hUne S₀
  rw [hS₀, subgroupOf_map_subtype]
  exact inf_le_left.trans hQN

/-- A plane whose normalizer contains a full ambient Sylow is of central type. -/
theorem local_plane_of_sylow_normalizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    {U : Subgroup G} (hUB : U ≤ layer L R) (hUcard : Nat.card U = 4)
    (P : Sylow 2 G) (hPN : (P : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ l ∈ L, U = (ZS (T : Subgroup G) L R).map (MulAut.conj l).toMonoidHom := by
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  have hUne : U ≠ ⊥ := by intro he; rw [he, card_bot] at hUcard; omega
  have hcor : ChapterE.subgroupCorank (layer L R) U = n := by
    have hc := (U.subgroupOf (layer L R)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv,
      hnatural.2.1.card, hUcard] at hc
    have hi : U.relIndex (layer L R) = 4 := by
      change 4 * U.relIndex (layer L R) = 16 at hc
      omega
    simp only [ChapterE.subgroupCorank, hi, hnatural.1]
    decide
  rcases fixedSpaceAlternatives_of_natural h hnat hE U hUB hUne hcor with hC | hline | hfield
  · have hCN := source_ordinary_fixed_space_centralizer h hE
      (natural_layer_rank_bounds h hnat hE).1 hUne hUB hC
    have hCM := hCN.trans hE.normalizer_le
    rw [inf_eq_right.mpr hCM, inf_eq_right.mpr hE.centralizer_le] at hC
    have hNM : normalizer (U : Set G) ≤ M := by
      apply (normalizer_le_normalizer_centralizer U).trans
      rw [hC]
      exact normalizer_layer_centralizer_le hE
    have hPL : (P : Subgroup G) ≤ normalizer (L : Set G) :=
      (hPN.trans hNM).trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
    obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow P L hPL
    have hSN : (S : Subgroup L).map L.subtype ≤ normalizer (U : Set G) := by
      rw [hS, subgroupOf_map_subtype]
      exact inf_le_left.trans hPN
    have he := sylow_invariant_plane L (layer L R) U hnatural.2.1 hUB hUcard S hSN
    obtain ⟨l, hl, hline⟩ := NaturalAction.sylow_line_orbit T h.sylow_normalizes_L
      (normalizer_commutator_ge_right R L) S
    exact ⟨l, hl, he.trans hline⟩
  · exact hline
  · exact (field_plane_no_full_sylow h hnat hE hfield hUne P hPN).elim
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Source 6.2.5(4): the distinguished plane belongs to a unique conjugate layer. -/
theorem local_plane_unique
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G) (hg : ZS (T : Subgroup G) L R ≤
      (layer L R).map (MulAut.conj g).toMonoidHom) :
    (layer L R).map (MulAut.conj g).toMonoidHom = layer L R := by
  let Z := ZS (T : Subgroup G) L R
  let B := layer L R
  let U := Z.map (MulAut.conj g⁻¹).toMonoidHom
  have hUB : U ≤ B := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rwa [fusion_map_conj_inverse] at hh
  have hUcard : Nat.card U = 4 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact (h.natural_ZS_geometry hnatural).2.1
  let P : Sylow 2 G := g⁻¹ • T
  have hPN : (P : Subgroup G) ≤ normalizer (U : Set G) := by
    change (T : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h.sylow_normalizes_ZS
    rwa [map_equiv_normalizer_eq] at hh
  obtain ⟨l, hl, hUl⟩ := local_plane_of_sylow_normalizer h hnatural hE hUB hUcard P hPN
  have hgl : Z.map (MulAut.conj (g * l)).toMonoidHom = Z := by
    rw [← fusion_map_conj_mul, ← hUl]
    simpa only [inv_inv] using fusion_map_conj_inverse Z g⁻¹
  have hglB : B.map (MulAut.conj (g * l)).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp
      (local_normalizer_plane h hnatural hE hfactor (mem_normalizer_iff_map_conj_eq.mpr hgl))
  have hlB : B.map (MulAut.conj l).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hl)
  rwa [← fusion_map_conj_mul, hlB] at hglB
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
