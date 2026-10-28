module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryContracts
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.SourceRelations
public import Theory.GroupTheory.CentralCoprimeCardLift
import Mathlib.Tactic.Group

/-!
# Lifting the marked Held involutions through a binary central kernel

Squares are constant on the fibers of a central cover with kernel of order
two. Thus any lift of an involution conjugate to an involution with a known
square-one lift also squares to one. A second lemma lifts commutation when
one image has order dividing three. The source commutator in HeG1-P1 gives
the commutation needed to reach the second involution class.

These elementary arguments keep the literal cover and presentation map.
They use no faithfulness or multiplier assertion. Source: John Bray's
`Held/Model/Source/HeG1-P1.M`, commutator relator.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
open PerfectCentralCovering Subgroup.CosetWordCertificate
variable {E : Type*} [Group E]

def sourceV {G : Type*} [Group G] (a b : G) : G := b * a * b * a * b⁻¹ * a * b * a * b

def positive {G : Type*} [Group G] (g : Fin 3 → G) (w : List (Fin 3)) : G := (w.map g).prod

theorem positive_eval {G : Type*} [Group G] (g : Fin 3 → G) (w : List (Fin 3)) :
    positive g w = eval g (w.map (fun i => (i, true))) := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [positive, List.map_cons, List.prod_cons, eval_cons,
      ↓reduceIte] using congrArg (g i * ·) ih

theorem map_positive {G H : Type*} [Group G] [Group H] (f : G →* H)
    (g : Fin 3 → G) (w : List (Fin 3)) : f (positive g w) = positive (f ∘ g) w := by
  simp only [positive, map_list_prod, List.map_map, Function.comp_def]

theorem square_eq_of_image_eq (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (s t : E) (he : f.toMonoidHom s = f.toMonoidHom t) : s ^ 2 = t ^ 2 := by
  have hk : s * t⁻¹ ∈ f.toMonoidHom.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hs : (s * t⁻¹) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨s * t⁻¹, hk⟩ : f.toMonoidHom.ker))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have hcomm : Commute (s * t⁻¹) t := (Subgroup.mem_center_iff.mp (f.ker_le_center hk) t).symm
  calc
    s ^ 2 = ((s * t⁻¹) * t) ^ 2 := by simp
    _ = (s * t⁻¹) ^ 2 * t ^ 2 := hcomm.mul_pow 2
    _ = t ^ 2 := by rw [hs, one_mul]

theorem square_eq_one_of_image_conjugate (f : Cover E He)
    (hc : Nat.card f.toMonoidHom.ker = 2) (s t : E) (ht : t ^ 2 = 1)
    (c : He) (he : f.toMonoidHom s = c⁻¹ * f.toMonoidHom t * c) : s ^ 2 = 1 := by
  obtain ⟨d, hd⟩ := f.surjective c
  rw [square_eq_of_image_eq f hc s (d⁻¹ * t * d) (by
    rw [map_mul, map_mul, map_inv, hd, he])]
  calc
    (d⁻¹ * t * d) ^ 2 = d⁻¹ * t ^ 2 * d := by simp only [pow_two]; group
    _ = 1 := by rw [ht]; group

theorem image_x (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap) : f.toMonoidHom (h x) = a := by
  have hh := DFunLike.congr_fun ht x
  simpa only [MonoidHom.comp_apply, x, presentationMap_of, generator] using hh

theorem sourceV_commute : Commute x (sourceV x y) := by
  change x * sourceV x y = sourceV x y * x
  have hh : x⁻¹ * (sourceV x y)⁻¹ * x * sourceV x y = 1 := presentation_relations 3
  have hc : (sourceV x y)⁻¹ * x * sourceV x y = x := by
    have he := congrArg (x * ·) hh
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using he
  have he := congrArg (sourceV x y * ·) hc
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he

theorem presentationMap_sourceV : presentationMap (sourceV x y) = sourceV a b := by
  simp only [sourceV, map_mul, map_inv, x, y, presentationMap_of, generator]

/-- Commutation in the image lifts when one image has odd order. -/
theorem commute_of_image_cube (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (s t : E) (hp : f.toMonoidHom s ^ 3 = 1)
    (he : Commute (f.toMonoidHom s) (f.toMonoidHom t)) : Commute s t := by
  have hcop : (Nat.card f.toMonoidHom.ker).Coprime 3 := by rw [hc]; decide
  obtain ⟨s₀, hs₀, hp₀⟩ := f.toMonoidHom.exists_pow_eq_one_lift_of_central_coprime_ker
    f.surjective f.ker_le_center hcop (f.toMonoidHom s) hp
  have hcomm := f.toMonoidHom.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
    f.ker_le_center hcop hp₀ (hs₀.symm ▸ he)
  have hk : s * s₀⁻¹ ∈ f.toMonoidHom.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hs₀, mul_inv_cancel]
  have hck : Commute (s * s₀⁻¹) t :=
    (Subgroup.mem_center_iff.mp (f.ker_le_center hk) t).symm
  simpa only [inv_mul_cancel_right] using hck.mul_left hcomm

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
