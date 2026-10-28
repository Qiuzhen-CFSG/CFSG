module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Movement
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.InnerBounds
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The whole Sylow overlap in compatible quaternion coordinates

The quaternion-swap image and its extra-involution coset lie in the fixed
intersection. Injectivity gives 128 distinct elements, attaining the bound
from the inner model. Thus these are the whole overlap, which is a Sylow
two-subgroup of the fixed carrier. This constructs the literal Geometry
witness used by the existing Thompson-subgroup deductions.
Source: Aschbacher--Smith, 14.2.21, printed p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem mem_natural (g : Carrier) :
    g ∈ natural ↔ g = 1 ∨ g = z ∨ g = v ∨ g = z * v := by
  exact Subgroup.mem_closure_pair_iff z v (by decide +kernel)
    (by decide +kernel) (show Commute z v from by change z*v=v*z; decide +kernel) g

theorem mem_secondParabolic_iff (g : Carrier) :
    g ∈ secondParabolic ↔ g * z * g⁻¹ ∈ natural ∧ g * v * g⁻¹ ∈ natural := by
  constructor
  · intro hg
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp (Subgroup.subset_closure (by simp)),
      (Subgroup.mem_normalizer_iff.mp hg v).mp (Subgroup.subset_closure (by simp))⟩
  · intro hg
    apply Subgroup.mem_normalizer_fintype
    have h : natural ≤ natural.comap (MulAut.conj g).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro x (rfl | rfl)
      · exact hg.1
      · exact hg.2
    exact h

theorem movement_mem_overlap (q : QH) : movement q ∈ overlap := by
  constructor
  · change movement q ∈ firstParabolic
    rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff, ← movement_z,
      ← map_mul, ← map_mul]
    apply congrArg movement
    exact Subgroup.mem_center_iff.mp
      ((Subgroup.central_of_normal_card_two Z card_Z)
        ((mem_Z QuaternionSwapModel.z).mpr (Or.inr rfl))) q
  · change movement q ∈ Subgroup.normalizer (natural : Set Carrier)
    rw [← movement_plane]
    exact Subgroup.le_normalizer_map movement ⟨q,MarkedCubic.conjugate_plane q,rfl⟩

theorem rawMap_mem_overlap (w : Raw) : rawMap w ∈ overlap :=
  movement_mem_overlap (projection w)

theorem extra_mem_overlap : extra ∈ overlap := by
  constructor
  · change extra ∈ firstParabolic
    rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
    decide +kernel
  · change extra ∈ secondParabolic
    rw [mem_secondParabolic_iff, mem_natural, mem_natural]
    decide +kernel

theorem secondActor_mem_secondParabolic : secondActor ∈ secondParabolic := by
  rw [mem_secondParabolic_iff, mem_natural, mem_natural]
  decide +kernel

def overlapWord (n : QH × Bool) : Carrier := movement n.1 * (if n.2 then extra else 1)

theorem overlapWord_injective : Function.Injective overlapWord := by
  have hn (x y : QH) : movement x ≠ movement y * extra := by
    intro h
    apply extra_outside
    refine ⟨y⁻¹ * x, ?_⟩
    rw [map_mul, map_inv, h, inv_mul_cancel_left]
  rintro ⟨x,b⟩ ⟨y,c⟩ h
  cases b <;> cases c <;>
    simp only [overlapWord, Bool.false_eq_true, ↓reduceIte, mul_one,
      mul_right_cancel_iff] at h
  · exact Prod.ext (movement_injective h) rfl
  · exact (hn x y h).elim
  · exact (hn y x h.symm).elim
  · exact Prod.ext (movement_injective h) rfl

def overlapElement (n : QH × Bool) : overlap := ⟨overlapWord n, by
  apply overlap.mul_mem (movement_mem_overlap _)
  cases n.2
  · exact overlap.one_mem
  · exact extra_mem_overlap⟩

theorem overlapElement_injective : Function.Injective overlapElement :=
  fun _ _ h => overlapWord_injective (congrArg Subtype.val h)

theorem card_overlap (m : InnerModel) : Nat.card overlap = 128 := by
  have h := Nat.card_le_card_of_injective overlapElement overlapElement_injective
  rw [Nat.card_prod, card_QH, (show Nat.card Bool = 2 from by simp [Nat.card_eq_fintype_card])] at h
  exact Nat.le_antisymm (card_overlap_le m) h

theorem overlapElement_surjective (m : InnerModel) : Function.Surjective overlapElement := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr ⟨overlapElement_injective, ?_⟩).2
  rw [Nat.card_prod, card_QH, (show Nat.card Bool = 2 from by simp [Nat.card_eq_fintype_card]), card_overlap m]

def geometry (m : InnerModel) : MarkedSylow.Geometry movement overlap where
  injective := movement_injective
  t := extra
  square := extra_square
  outside := extra_outside
  conjugation := extra_conjugation
  cover g := by
    constructor
    · intro hg
      obtain ⟨⟨q,b⟩,h⟩ := overlapElement_surjective m ⟨g,hg⟩
      exact ⟨q,b,(congrArg Subtype.val h).symm⟩
    · rintro ⟨q,b,rfl⟩
      exact (overlapElement (q,b)).property

noncomputable def commonSylow (m : InnerModel) : Sylow 2 Carrier :=
  Sylow.ofCard overlap (by rw [card_overlap m, m.card_carrier]; decide +kernel)

theorem commonSylow_coe (m : InnerModel) : (commonSylow m : Subgroup Carrier) = overlap := rfl

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
