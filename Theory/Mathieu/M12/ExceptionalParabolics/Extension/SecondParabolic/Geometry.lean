module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Overlap

/-!
# The second parabolic and its marked movement geometry

The generating actor's three translates of the whole overlap are distinct,
as detected by conjugation of the marked involution. They attain the bound
384, proving generation of the fixed normalizer. Together with the literal
four action equations, this constructs the full SecondGeometry witness.
Source: Aschbacher--Smith, F.1.12(I)(13), p.263, and 14.2.21, p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem overlap_conjugates_z (g : overlap) : (g : Carrier) * z * (g : Carrier)⁻¹ = z := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp g.property.1
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

def threeCosets (K : Subgroup Carrier) (hT : overlap ≤ K) (hy : secondActor ∈ K)
    (n : Fin 3 × overlap) : K :=
  ⟨secondActor ^ n.1.val * n.2, K.mul_mem (K.pow_mem hy _) (hT n.2.property)⟩

theorem threeCosets_injective (K : Subgroup Carrier) (hT : overlap ≤ K) (hy : secondActor ∈ K) :
    Function.Injective (threeCosets K hT hy) := by
  have hc (i : Fin 3) (g : overlap) :
      (secondActor ^ i.val * g) * z * (secondActor ^ i.val * g)⁻¹ = secondActor ^ i.val * z * (secondActor ^ i.val)⁻¹ := by
    rw [mul_inv_rev]
    calc
      _ = secondActor ^ i.val * ((g : Carrier) * z * (g : Carrier)⁻¹) * (secondActor ^ i.val)⁻¹ := by group
      _ = _ := by rw [overlap_conjugates_z]
  rintro ⟨i,g⟩ ⟨j,h⟩ he
  have he' : secondActor ^ i.val * (g : Carrier) = secondActor ^ j.val * (h : Carrier) :=
    congrArg Subtype.val he
  have ha := congrArg (fun x : Carrier => x * z * x⁻¹) he'
  rw [hc, hc] at ha
  have hi : ∀ i j : Fin 3,
      secondActor ^ i.val * z * (secondActor ^ i.val)⁻¹ = secondActor ^ j.val * z * (secondActor ^ j.val)⁻¹ → i = j := by
    decide +kernel
  obtain rfl := hi i j ha
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel he'))

theorem card_secondParabolic (m : InnerModel) : Nat.card secondParabolic = 384 := by
  have h := Nat.card_le_card_of_injective
    (threeCosets secondParabolic inf_le_right secondActor_mem_secondParabolic)
    (threeCosets_injective secondParabolic inf_le_right secondActor_mem_secondParabolic)
  rw [Nat.card_prod, Nat.card_fin, card_overlap m] at h
  exact Nat.le_antisymm (card_secondParabolic_le m) h

theorem second_span (m : InnerModel) : secondParabolic = overlap ⊔ Subgroup.zpowers secondActor := by
  apply (Subgroup.eq_of_le_of_card_ge
    (sup_le inf_le_right (Subgroup.zpowers_le.mpr secondActor_mem_secondParabolic)) ?_).symm
  have h := Nat.card_le_card_of_injective
    (threeCosets (overlap ⊔ Subgroup.zpowers secondActor) le_sup_left
      (show secondActor ∈ overlap ⊔ Subgroup.zpowers secondActor from Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    (threeCosets_injective (overlap ⊔ Subgroup.zpowers secondActor) le_sup_left
      (show secondActor ∈ overlap ⊔ Subgroup.zpowers secondActor from Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  rw [Nat.card_prod, Nat.card_fin, card_overlap m] at h
  simpa only [card_secondParabolic m, overlap] using h

def secondGeometry (m : InnerModel) : MarkedSylow.SecondGeometry movement overlap secondParabolic where
  toGeometry := geometry m
  y := secondActor
  span := second_span m
  action_zero := actor_action_zero
  action_one := actor_action_one
  action_two := actor_action_two
  action_three := actor_action_three

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
