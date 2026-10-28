module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanks
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple
public import Theory.Representation.SL2BinaryHyperplanes

/-!
# The global rank of the original natural layer

A two-group fixes a nonzero binary dual vector, so B has a Sylow-normal
hyperplane. E.6.13 controls its ambient centralizer. The actual SL₂ quotient
marking carries every binary hyperplane to this one, excluding r(G,B)=1.
For subgroups of corank less than n, semilinearity gives C_M(U)=C_M(B),
and the proved E.6.12 implication then gives r(G,B)≥n. Together with the
local computation this yields m=s=n, including the n=2 case.

This specialized route has no Held-cover premise and requires no contained
centralizer hypothesis. Source: Aschbacher--Smith, 6.1.10(1--2), printed p.670,
using E.6.12--13, printed p.250. The Chapter 12 companion applies the result
to the literal original layer and its weak-closure conclusions.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
noncomputable section
variable {G : Type*} [Group G] [Finite G] {L B : Subgroup G}
  [IsElementaryAbelian 2 B]

private def binarySpace (U : Subgroup G) : Submodule (ZMod 2) (Additive B) :=
  AddSubgroup.toZModSubmodule 2 (U.subgroupOf B).toAddSubgroup

private theorem binarySpace_finrank (U : Subgroup G) :
    Module.finrank (ZMod 2) (binarySpace (B := B) U) + ChapterE.subgroupCorank B U =
      Module.finrank (ZMod 2) (Additive B) := by
  have hc := (U.subgroupOf B).card_mul_index
  have hU : Nat.card (U.subgroupOf B) =
      2 ^ Module.finrank (ZMod 2) (binarySpace (B := B) U) := by
    change Nat.card (binarySpace (B := B) U) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hB : Nat.card B = 2 ^ Module.finrank (ZMod 2) (Additive B) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive B)
    change Nat.card B = _ at hh
    simpa only [Nat.card_zmod] using hh
  have hi : (U.subgroupOf B).index = 2 ^ ChapterE.subgroupCorank B U := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact B.relIndex_eq_two_pow_quotient_finrank U
  rw [hU, hi, hB, ← pow_add] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

private theorem natural_hyperplane_conjugacy {n : ℕ}
    (hnatural : IsNaturalModule L B n) {U W : Subgroup G}
    (hUB : U ≤ B) (hWB : W ≤ B)
    (hU : ChapterE.subgroupCorank B U = 1)
    (hW : ChapterE.subgroupCorank B W = 1) :
    ∃ l ∈ L, U.map (MulAut.conj l).toMonoidHom = W := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  have hm : IsConjugationModel L B (Representation.specialLinearNatural (k := F) 2) :=
    ⟨e, f, hf⟩
  let E : Additive B ≃ₗ[ZMod 2] (Fin 2 → F) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  let A := (binarySpace U).map E.toLinearMap
  let D := (binarySpace W).map E.toLinearMap
  have hdim (Y : Subgroup G) (hY : ChapterE.subgroupCorank B Y = 1) :
      Module.finrank (ZMod 2) ((binarySpace Y).map E.toLinearMap) + 1 =
        Module.finrank (ZMod 2) (Fin 2 → F) := by
    rw [E.finrank_map_eq, ← E.finrank_eq, ← hY]
    exact binarySpace_finrank Y
  obtain ⟨g, hg⟩ := Representation.SL2BinaryHyperplanes.transitive_hyperplanes
    A D (hdim U hU) (hdim W hW)
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm g)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = g := by rw [hl, e.apply_symm_apply]
  have hact (v : B) :
      E (Additive.ofMul (B.normalizerMonoidHom ⟨l, hm.normalizes l.property⟩ v)) =
        Representation.SL2BinaryHyperplanes.action g (E (Additive.ofMul v)) := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (f (B.normalizerMonoidHom ⟨l, hm.normalizes l.property⟩ v)) : G) = _
    rw [f.symm_apply_apply]
    change (l : G) * (v : G) * (l : G)⁻¹ =
      (f.symm (Multiplicative.ofAdd (g.val.mulVec (f v).toAdd)) : G)
    rw [← hel]
    exact (hf l v).symm
  refine ⟨l, l.property, ?_⟩
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    let b : B := ⟨v, hUB hv⟩
    have hb : E (Additive.ofMul b) ∈ A := ⟨Additive.ofMul b, hv, rfl⟩
    have hh : Representation.SL2BinaryHyperplanes.action g (E (Additive.ofMul b)) ∈ D := by
      rw [← hg]
      exact ⟨_, hb, rfl⟩
    rw [← hact] at hh
    obtain ⟨y, hy, he⟩ := hh
    have he' := E.injective he
    have hh' : Additive.ofMul (B.normalizerMonoidHom ⟨l, hm.normalizes l.property⟩ b) ∈
        binarySpace (B := B) W := he' ▸ hy
    exact hh'
  · intro x hx
    have hxD : E (Additive.ofMul (⟨x, hWB hx⟩ : B)) ∈ D :=
      ⟨Additive.ofMul ⟨x, hWB hx⟩, hx, rfl⟩
    rw [← hg] at hxD
    obtain ⟨z, ⟨v, hv, rfl⟩, he⟩ := hxD
    have he' : Representation.SL2BinaryHyperplanes.action g (E (Additive.ofMul v.toMul)) =
        E (Additive.ofMul ⟨x, hWB hx⟩) := he
    rw [← hact] at he'
    have hh := congrArg (fun y : Additive B => (y.toMul : G)) (E.injective he')
    exact ⟨v.toMul, hv, hh⟩

private theorem exists_normal_hyperplane (T : Sylow 2 G)
    (hBT : B ≤ T) (hTN : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hB : B ≠ ⊥) :
    ∃ W : Subgroup G, W ≤ B ∧ ChapterE.subgroupCorank B W = 1 ∧
      (W.subgroupOf (T : Subgroup G)).Normal := by
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
  let q : T →* ChapterE.Automizer B :=
    B.normalizerMonoidHom.rangeRestrict.comp (inclusion hTN)
  let ρ := (ChapterE.automizerRepresentation B).comp q
  obtain ⟨X, hX, hinv⟩ := Representation.exists_invariant_binary_hyperplane ρ T.isPGroup'
  let W := X.toAddSubgroup.toSubgroup'.map B.subtype
  have hWB : W ≤ B := map_subtype_le _
  have hWX : binarySpace (B := B) W = X := by
    ext v
    change (v.toMul : G) ∈ W ↔ v ∈ X
    constructor
    · rintro ⟨w, hw, he⟩
      have he' := B.subtype_injective he
      change Additive.ofMul w ∈ X at hw
      rw [he'] at hw
      exact hw
    · intro hv
      exact ⟨v.toMul, hv, rfl⟩
  have hcor : ChapterE.subgroupCorank B W = 1 := by
    have hh := binarySpace_finrank (B := B) W
    rw [hWX] at hh
    omega
  refine ⟨W, hWB, hcor, ?_⟩
  apply (normal_subgroupOf_iff_le_normalizer (hWB.trans hBT)).mpr
  apply le_normalizer_iff.mpr
  intro t ht w hw
  let v : Additive B := Additive.ofMul ⟨w, hWB hw⟩
  have hv : v ∈ X := by rw [← hWX]; exact hw
  have hh := hinv ⟨t, ht⟩ v hv
  rw [← hWX] at hh
  exact hh

/-- E.6.13 and hyperplane transitivity exclude global rank one for natural layers. -/
theorem natural_one_lt_globalR {T : Sylow 2 G} {M : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hLM : L ≤ M)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B) :
    1 < ChapterE.globalR B := by
  have hm := natural_localM_eq hnatural hNL
  obtain ⟨W, hWB, hW, hWT⟩ := exists_normal_hyperplane T hE.le_sylow
    hE.sylow_le_normalizer hE.nontrivial
  have hWsmall : ChapterE.subgroupCorank B W < ChapterE.localM B := by rw [hW, hm]; exact hn
  have hWC := ChapterE.Section06.InvariantSubspaces.centralizer_le_of_normal_in_sylow_knownSimple
    hE (ChapterE.Section06.nontrivial_of_corank_lt_localM hWsmall) hWB
    (hE.oddCentralizerCondition_of_small hWB hWsmall) hWT
  have hplanes (U : Subgroup G) (hUB : U ≤ B) (hU : ChapterE.subgroupCorank B U = 1) :
      centralizer (U : Set G) ≤ M := by
    obtain ⟨l, hl, he⟩ := natural_hyperplane_conjugacy hnatural hUB hWB hU hW
    intro x hx
    have hx' : l * x * l⁻¹ ∈ centralizer (W : Set G) := by
      rw [← he]
      exact map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj l).toMonoidHom
        (mem_map_of_mem _ hx)
    have hh := M.mul_mem (M.mul_mem (M.inv_mem (hLM hl)) (hWC hx')) (hLM hl)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  apply lt_of_le_of_ne (ChapterE.one_le_globalR B)
  intro he
  obtain ⟨U, hUB, hescape, hcor⟩ := ChapterE.Section06.globalR_attained
    (by rw [← he]; exact ENat.one_ne_top)
  have hU : ChapterE.subgroupCorank B U = 1 := by exact_mod_cast hcor.trans he.symm
  exact hescape ((hE.centralizer_le_iff
    (ChapterE.Section06.nontrivial_of_corank_lt_localM (by rw [hU, hm]; exact hn)) hUB).mp
      (hplanes U hUB hU))

/-- The natural local minimum bounds the full global centralizer parameter. -/
theorem natural_globalR_ge {T : Sylow 2 G} {M : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G)) (hLM : L ≤ M)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B) :
    (n : ℕ∞) ≤ ChapterE.globalR B :=
  natural_globalR_ge_of_one_lt hnatural hNL hE
    (natural_one_lt_globalR hn hnatural hNL hLM hE)

omit [IsElementaryAbelian 2 B] in
/-- Source 6.1.10(1--2), with all rank premises discharged. -/
theorem natural_layer_rank_bounds {T : Sylow 2 G} {M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V)) :
    letI := h.layer_elementary
    (n : ℕ∞) ≤ ChapterE.globalR (layer L V) ∧
      ChapterE.localM (layer L V) = n ∧ ChapterE.globalS (layer L V) = n := by
  let := h.layer_elementary
  have hr := natural_globalR_ge h.n_gt_one hnatural
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal))
    h.L_le hE
  have hm := natural_layer_localM_eq h hnatural hE
  refine ⟨hr, hm, ?_⟩
  rw [ChapterE.globalS, hm]
  exact min_eq_right hr

end
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
