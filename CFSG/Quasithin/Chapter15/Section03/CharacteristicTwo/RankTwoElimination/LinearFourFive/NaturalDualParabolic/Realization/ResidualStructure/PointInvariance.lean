module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Sylow

/-!
# Invariance of the actual point parabolic

The image of S∩L is Sylow in the marked binary linear group and fixes a
unique nonzero vector. An inner automorphism induced by S preserves this
Sylow image, so its conjugating element fixes the same vector. Transport
through the actual quotient of L.normalizerMonoidHom shows that S
normalizes the pulled-back point stabilizer.

The theta specialization obtains relative normalization and the Sylow
intersection from L = theta(I); point normalization is a conclusion.
Both choices of Hypothesis 15.3.10 are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(1), 15.3.17(2), and 15.3.24, printed pp.1123,1126,1129.
-/

public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {L I : Subgroup G}

private theorem linear_normalizer_fixes (T : Sylow 2 (LinearGroup 4))
    {x : Space 4} (hx : x ≠ 0) (hT : (T : Subgroup (LinearGroup 4)) ≤ pointStabilizer x) :
    normalizer (T : Set (LinearGroup 4)) ≤ pointStabilizer x := by
  obtain ⟨y, hy, he⟩ := linear_sylow_fixed_line (V := Space 4) (by
    simp only [Space, Module.finrank_pi, Fintype.card_fin]; omega) T
  have hxy : x ∈ Submodule.span (ZMod 2) {y} := he ▸ (show x ∈ BinaryLinear.fixedSpace T from hT)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxy
  have ha0 : a ≠ 0 := by intro h0; exact hx (by simpa [h0] using ha.symm)
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  have hyx : y = x := by simpa [ha1] using ha
  rw [hyx] at he
  have hn := BinaryLinear.normalizer_le_parabolic_fixedSpace (T : Subgroup (LinearGroup 4))
  rwa [he, parabolic_line_eq hx] at hn

/-- The inner quotient action of S preserves every point parabolic over S∩L. -/
theorem point_normalized_of_inner (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hn : d.S ≤ normalizer (L : Set G))
    (hSL : Chapter1.IsSylowIn 2 (d.S ⊓ L) L)
    (hi : Preparation.IsInnerOnComponent d L hn)
    (hSP : d.S ⊓ L ≤ point h x) :
    d.S ≤ normalizer (point h x : Set G) := by
  let f := linearAction (by decide : 0 < 4) h.model
  let e := h.model.trans (projectiveEquivLinear (by decide : 0 < 4))
  obtain ⟨T, hT⟩ := hSL
  have hT' : (T : Subgroup L) = d.S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hT, subgroupOf_map_subtype]
  let U := T.mapSurjective (linearAction_surjective (by decide) h.model)
  have hUP : (U : Subgroup (LinearGroup 4)) ≤ pointStabilizer x := by
    rintro _ ⟨l, hl, rfl⟩
    exact (mem_point h x l).mp (hSP ⟨(show l ∈ d.S.subgroupOf L from hT' ▸ hl), l.property⟩)
  have hstable (s : d.S) : ∀ l : L,
      let a := L.normalizerMonoidHom ⟨s, hn s.property⟩
      l ∈ (T : Subgroup L) ↔ a l ∈ (T : Subgroup L) := by
    intro l
    rw [hT']
    exact d.S.le_normalizer s.property l
  have hconj (s : d.S) : ∃ g : LinearGroup 4,
      g ∈ pointStabilizer x ∧ ∀ l : L,
        f (L.normalizerMonoidHom ⟨s, hn s.property⟩ l) = g * f l * g⁻¹ := by
    obtain ⟨q, hq⟩ := hi s
    let g := e q
    let a := L.normalizerMonoidHom ⟨s, hn s.property⟩
    have hf : ∀ l : L, f (a l) = g * f l * g⁻¹ := by
      intro l
      have hh := congrArg e (DFunLike.congr_fun hq (QuotientGroup.mk' (pCore 2 L) l))
      rw [Preparation.sylowCoreAction_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at hh
      exact hh.symm
    have hg : g ∈ normalizer (U : Set (LinearGroup 4)) := by
      intro k
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨a l, (hstable s l).mp hl, hf l⟩
      · intro hk
        obtain ⟨l, hl, he⟩ := hk
        refine ⟨a.symm l, (hstable s (a.symm l)).mpr (by change a (a.symm l) ∈ (T : Subgroup L); rw [a.apply_symm_apply]; exact hl), ?_⟩
        apply (MulAut.conj g).injective
        change g * f (a.symm l) * g⁻¹ = g * k * g⁻¹
        rw [← hf, a.apply_symm_apply]
        exact he
    exact ⟨g, linear_normalizer_fixes U hx hUP hg, hf⟩
  have hforward (s : d.S) (p : G) (hp : p ∈ point h x) :
      (s : G) * p * (s : G)⁻¹ ∈ point h x := by
    let l : L := ⟨p, point_le h x hp⟩
    obtain ⟨g, hg, hf⟩ := hconj s
    apply (mem_point h x (L.normalizerMonoidHom ⟨s, hn s.property⟩ l)).mpr
    change f (L.normalizerMonoidHom ⟨s, hn s.property⟩ l) ∈ pointStabilizer x
    rw [hf]
    exact (pointStabilizer x).mul_mem
      ((pointStabilizer x).mul_mem hg ((mem_point h x l).mp hp))
      ((pointStabilizer x).inv_mem hg)
  intro s hs p
  constructor
  · exact hforward ⟨s, hs⟩ p
  · intro hp
    have hh := hforward (⟨s, hs⟩ : d.S)⁻¹ (s * p * s⁻¹) hp
    change p ∈ point h x
    simpa only [coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
/-- In the source setup, L = theta(I) supplies S-normalization of L and
its Sylow intersection; the displayed quotient innerness then normalizes P. -/
theorem point_normalized_of_theta (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : L = theta I)
    (hi : Preparation.IsInnerOnComponent d L
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)))
    (hSP : d.S ⊓ L ≤ point h x) :
    d.S ≤ normalizer (point h x : Set G) :=
  point_normalized_of_inner h hx _ (sylow_intersection_of_eq_theta d hS hθ) hi hSP

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
