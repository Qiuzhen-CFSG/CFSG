module

public import Stellmacher.Recognition.NormalEightExoticExtension256FixedPoints
public import Theory.SpecificGroups.ExoticTwoGroup.QuarterTurnSplit
public import Theory.Frattini.BinarySquares
import Mathlib.Tactic

/-!
# Excluding the split quarter-turn extension

The elementary sixteen supplies commuting involutory lifts of the two inner
actions. A quarter-turn would then make every square in the four-centralizer
belong to the omega four. The centralizer's Frattini subgroup, however, is the
whole C₄-square base, a contradiction. This isolates the split obstruction
without assuming a swap or an order-three automorphism.

Source: MacWilliams, Trans. AMS 150 (1970), §4 (xx)–(xxii), printed p.399;
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

open Subgroup C4SquareExtension ExoticTwoGroup.ActionModel
namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- The Frattini identity alone excludes a quarter-turn when the inner
four has commuting involutory lifts. -/
public theorem no_quarter_turn_of_frattini
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W D B : Subgroup P) [W.Normal] [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* Model)
    (hcard : Nat.card P = 256)
    (hPhi : D = (frattini (centralizer (W : Set P))).map
      (centralizer (W : Set P)).subtype)
    (h₁ : inner₁ ∈ ((modelAction D e).comp B.subtype).range)
    (h₂ : inner₂ ∈ ((modelAction D e).comp B.subtype).range)
    (t : P) (ht₁ : modelAction D e t u = v)
    (ht₂ : modelAction D e t v = u⁻¹) : False := by
  let F := modelAction D e
  let ι : Model →* P := D.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective ι := D.subtype_injective.comp e.symm.injective
  have hir : ι.range = D := by
    ext d
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).property
    · intro hd
      exact ⟨e ⟨d, hd⟩, by simp [ι]⟩
  have hker : F.ker = ι.range := (modelAction_ker D hDC e).trans hir.symm
  have hconj (s : P) (x : Model) : s * ι x * s⁻¹ = ι (F s x) := by
    change s * (e.symm x : P) * s⁻¹ =
      (e.symm (e (MulAut.conjNormal (H := D) s (e.symm x))) : P)
    rw [e.symm_apply_apply]
    rfl
  have hsmall (d : Model) (hd : d ^ 2 = 1) : ι d ∈ W := by
    rw [← hDO]
    refine ⟨e.symm d, subset_closure ?_, rfl⟩
    change (e.symm d) ^ 2 = 1
    rw [← map_pow, hd, map_one]
  have hfix (x : P) (hx : x ∈ centralizer (W : Set P))
      (d : Model) (hd : d ^ 2 = 1) : F x d = d := by
    apply hi
    rw [← hconj, ← hx _ (hsmall d hd), mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨h, hh⟩ := h₂
  have hg2 : (g : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (g : P) g.property
  have hh2 : (h : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (h : P) h.property
  have hgh : Commute (g : P) (h : P) := setLike_mul_comm g.property h.property
  have ht : F t = ExoticTwoGroup.QuarterTurn.rotation :=
    aut_ext (ht₁.trans ExoticTwoGroup.QuarterTurn.rotation_u.symm)
      (ht₂.trans ExoticTwoGroup.QuarterTurn.rotation_v.symm)
  have hsquare (x : P) (hx : x ∈ centralizer (W : Set P)) : x ^ 2 ∈ W := by
    exact ExoticTwoGroup.QuarterTurn.square_mem_of_fix_squares W ι hi F hker hconj
      hsmall (card_modelAction_range D hDC e hcard) g h t hg hh ht hg2 hh2 hgh x
      (hfix x hx (u ^ 2) (by rw [← pow_mul]; exact u_four))
      (hfix x hx (v ^ 2) (by rw [← pow_mul]; exact v_four))
  have hDW : D ≤ W := by
    rw [hPhi, map_le_iff_le_comap,
      (hP.to_subgroup (centralizer (W : Set P))).frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact hsquare x x.property
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hc := card_le_of_le hDW
  rw [hD, hW] at hc
  omega

/-- A quarter-turn lift is impossible for the order-256 Sylow branch with
fused involutions and the supplied inner-action memberships. -/
public theorem no_quarter_turn
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hcard : Nat.card S = 256)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B]
    (_hB : Nat.card B = 16) (_hWB : W ≤ B)
    (_hnorm : Subgroup.normalizer (S : Set G) =
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : Subgroup.centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* Model)
    (h₁ : inner₁ ∈ ((modelAction D e).comp B.subtype).range)
    (h₂ : inner₂ ∈ ((modelAction D e).comp B.subtype).range)
    (t : S) (ht₁ : modelAction D e t u = v)
    (ht₂ : modelAction D e t v = u⁻¹) : False := by
  have htrans := fixedPoints_centralizer_transitive S hZ hno W hW hunique hfused
  have hPhi := base_eq_frattini_centralizer S.isPGroup' hcard hZ hno W hW
    htrans D hWD hDC hDO ⟨e⟩
  exact no_quarter_turn_of_frattini S.isPGroup' W D B hW hDC hDO e hcard hPhi
    h₁ h₂ t ht₁ ht₂

end Stellmacher.Recognition.NormalEightExoticExtension256
