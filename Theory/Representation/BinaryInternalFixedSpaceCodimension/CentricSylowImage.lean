module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.ElementaryAbelian.EightQuotientRank
public import Mathlib.GroupTheory.Sylow

/-!
# The exact Sylow quotient of a self-centralizing internal binary module

When the full ambient centralizer of W equals W, the conjugation map of
N_G(W) has precisely the original W as kernel. The actual Sylow image has
order |T|/|W|. This retains the full kernel rather than just a quotient bound.
-/

public section
namespace Representation.BinaryInternalFixedSpaceCodimension
open Subgroup BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem centric_sylow_image_card
    (T : Sylow 2 G) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hC : centralizer (W : Set G) = W) :
    let I := normalizer (W : Set G)
    let ρ := representation W I le_rfl
    (actionHom ρ).ker = W.subgroupOf I ∧
      ∀ S : Sylow 2 (actionImage ρ), Nat.card W * Nat.card S = Nat.card T := by
  let I := normalizer (W : Set G)
  let ρ := representation W I le_rfl
  let q := actionHom ρ
  have hker : q.ker = W.subgroupOf I := by
    ext x
    change q x = 1 ↔ (x : G) ∈ W
    rw [actionHom_eq_one_iff]
    constructor
    · intro hx
      apply hC.le
      intro w hw
      have he := congrArg (fun v : Additive W => (v.toMul : G))
        (hx (Additive.ofMul (⟨w,hw⟩ : W)))
      change (x : G)*w*(x : G)⁻¹=w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hx w
      have hx := hC.ge hx
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x : G)*(w.toMul : G)*(x : G)⁻¹=(w.toMul : G)
      rw [← hx w.toMul w.toMul.property, mul_inv_cancel_right]
  refine ⟨hker, ?_⟩
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let Q := T.subtype hTW
  let P := Q.mapSurjective (f := q) hq
  have hPc : Nat.card W * Nat.card P = Nat.card T := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (Q : Subgroup I) q
    have hWQ : W.subgroupOf I ≤ (Q : Subgroup I) := subgroupOf_mono I hWT
    rw [hker, inf_eq_right.mpr hWQ] at hh
    change Nat.card (W.subgroupOf I) * Nat.card P = Nat.card Q at hh
    have hQc : Nat.card Q = Nat.card T :=
      Nat.card_congr (subgroupOfEquivOfLe hTW).toEquiv
    rwa [Nat.card_congr (subgroupOfEquivOfLe W.le_normalizer).toEquiv,
      hQc] at hh
  intro S
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (actionImage ρ) P S
  have he := congrArg Sylow.toSubgroup hg
  change (P : Subgroup (actionImage ρ)).map (MulAut.conj g).toMonoidHom =
    (S : Subgroup (actionImage ρ)) at he
  rw [← he, card_map_of_injective (MulAut.conj g).injective]
  exact hPc

end Representation.BinaryInternalFixedSpaceCodimension
