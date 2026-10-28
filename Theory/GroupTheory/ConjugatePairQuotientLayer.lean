module

public import Theory.GroupTheory.ConjugatePairCommutatorLayer
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.ElementaryAbelian.Join
import Mathlib.Tactic.Group

/-!
# The literal quotient of an almost-special generating pair

The normal bottom layer V=[V,G] splits over a normalized generating pair.
This prevents new intersections when quotienting by (U∩W)V. The commutator
layer then has disjoint elementary factors in that exact quotient, each
centralized by its corresponding generator.

Source: Aschbacher--Smith, the argument after (12.7.18), printed pp.845--846.
The quotient homomorphism is retained, and no perfectness or Sylow premise
on the generated group is needed.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The common intersection is central modulo the invariant derived bound,
so its join with that bound is an actual normal quotient layer. -/
theorem almost_special_pair_layer_normal (U W V : Subgroup G) [V.Normal]
    (hgen : U ⊔ W = ⊤) (hU : ⁅U,U⁆ ≤ V) (hW : ⁅W,W⁆ ≤ V) :
    ((U ⊓ W) ⊔ V).Normal := by
  apply commutator_top_right_le_iff.mp
  apply le_trans _ (show V ≤ (U ⊓ W) ⊔ V from le_sup_right)
  apply commutator_sup_le_of_relative_normal ⊤ (U ⊓ W) V ⊤ V
    le_normalizer_of_normal le_top le_top
  · simpa only [hgen] using intersection_commutator_sup_le hU hW le_normalizer_of_normal
  · exact commutator_le_left V ⊤

/-- A bottom layer splitting across the two generators introduces no new
intersection in their images modulo the common intersection and that layer. -/
theorem disjoint_pair_images_of_split_kernel (q : G →* H) (U W V : Subgroup G)
    [V.Normal] (hker : q.ker = (U ⊓ W) ⊔ V)
    (hV : (V : Set G) = (V ⊓ U : Subgroup G) * (V ⊓ W : Subgroup G)) :
    Disjoint (U.map q) (W.map q) := by
  apply disjoint_def.mpr
  rintro y ⟨u, hu, rfl⟩ ⟨w, hw, he⟩
  have huv : u * w⁻¹ ∈ (U ⊓ W) ⊔ V := by
    rw [← hker]
    change q (u * w⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc, v, hv, hcv⟩ := mem_sup_of_normal_right.mp huv
  have hvp : v ∈ ((V ⊓ U : Subgroup G) : Set G) *
      ((V ⊓ W : Subgroup G) : Set G) := by rw [← hV]; exact hv
  obtain ⟨a, ha, b, hb, hab⟩ := hvp
  have hprod : u * w⁻¹ = c * (a * b) := hcv.symm.trans (congrArg (c * ·) hab.symm)
  have hd : (c * a)⁻¹ * u ∈ U ⊓ W := by
    refine ⟨U.mul_mem (U.inv_mem (U.mul_mem hc.1 ha.2)) hu, ?_⟩
    have heq : (c * a)⁻¹ * u = b * w := by
      calc
        (c * a)⁻¹ * u = (c * a)⁻¹ * (u * w⁻¹) * w := by group
        _ = b * w := by rw [hprod]; group
    rw [heq]
    exact W.mul_mem hb.2 hw
  have huN : u ∈ (U ⊓ W) ⊔ V := by
    have hh := mul_mem (mul_mem (mem_sup_left hc) (mem_sup_right ha.1))
      (mem_sup_left hd)
    simpa only [mul_inv_cancel_left] using hh
  have huk : u ∈ q.ker := hker.symm ▸ huN
  exact huk

private theorem elementary_image_of_squares (q : G →* H) (U : Subgroup G)
    (hsq : ∀ u ∈ U, u ^ 2 ∈ q.ker) : IsElementaryAbelian 2 (U.map q) := by
  have hp (x : U.map q) : x ^ 2 = 1 := by
    obtain ⟨u, hu, he⟩ := x.property
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [← he, ← map_pow]
    exact hsq u hu
  exact {
    is_comm.comm := fun x y =>
      (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_iff_pow_eq_one.mpr (hp x)) x y).eq
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

/-- The actual commutator layer in the supplied quotient is the direct sum
of its two elementary intersection images. The factors are fixed by their
respective generators. -/
theorem normalized_pair_commutator_quotient (q : G →* H)
    (U W Q V : Subgroup G) [Q.Normal] [V.Normal]
    (hgen : U ⊔ W = ⊤) (hQU : Q ≤ normalizer (U : Set G))
    (hQW : Q ≤ normalizer (W : Set G)) (hVQ : V ≤ Q)
    (hV : ⁅V, (⊤ : Subgroup G)⁆ = V)
    (hker : q.ker = (U ⊓ W) ⊔ V)
    (hUU : ⁅U,U⁆ ≤ V) (hWW : ⁅W,W⁆ ≤ V)
    (hsqU : ∀ u ∈ U, u ^ 2 ∈ V) (hsqW : ∀ w ∈ W, w ^ 2 ∈ V) :
    let P := ⁅Q, (⊤ : Subgroup G)⁆
    let A := (P ⊓ U).map q
    let B := (P ⊓ W).map q
    A ⊔ B = P.map q ∧ Disjoint A B ∧ IsElementaryAbelian 2 (P.map q) ∧
      A ≤ centralizer (U.map q : Set H) ∧ B ≤ centralizer (W.map q : Set H) := by
  dsimp only
  let P := ⁅Q, (⊤ : Subgroup G)⁆
  let A := (P ⊓ U).map q
  let B := (P ⊓ W).map q
  have hPQ : P ≤ Q := commutator_le_left Q ⊤
  have hkerV : V ≤ q.ker := hker.symm ▸ le_sup_right
  have hsplit : A ⊔ B = P.map q := by
    rw [← map_sup]
    exact congrArg (fun C : Subgroup G => C.map q)
      (commutator_eq_sup_intersections_of_normalizes_generators U W Q hgen hQU hQW).symm
  have hdis : Disjoint A B :=
    (disjoint_pair_images_of_split_kernel q U W V hker
      (self_commutator_eq_product_intersections U W V hgen
        (hVQ.trans hQU) (hVQ.trans hQW) hV)).mono
      (map_mono inf_le_right) (map_mono inf_le_right)
  have hcross : ⁅P ⊓ W, P ⊓ U⁆ ≤ q.ker := by
    apply le_trans _ (show U ⊓ W ≤ q.ker from hker.symm ▸ le_sup_left)
    refine le_inf ?_ ?_
    · exact (commutator_mono (inf_le_left.trans hPQ) inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp hQU)
    · rw [commutator_comm]
      exact (commutator_mono (inf_le_left.trans hPQ) inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp hQW)
  have hBA : B ≤ centralizer (A : Set H) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr hcross
  let : IsElementaryAbelian 2 A := elementary_image_of_squares q (P ⊓ U)
    (fun u hu => hkerV (hsqU u hu.2))
  let : IsElementaryAbelian 2 B := elementary_image_of_squares q (P ⊓ W)
    (fun w hw => hkerV (hsqW w hw.2))
  have he : IsElementaryAbelian 2 (A ⊔ B : Subgroup H) :=
    IsElementaryAbelian.sup_of_le_centralizer hBA
  refine ⟨hsplit, hdis,
    (congrArg (fun C : Subgroup H => IsElementaryAbelian 2 C) hsplit).mp he, ?_, ?_⟩
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr ((commutator_mono inf_le_right le_rfl).trans
      (hUU.trans hkerV))
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr ((commutator_mono inf_le_right le_rfl).trans
      (hWW.trans hkerV))

end Subgroup
