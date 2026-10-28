module
public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.Coordinates
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The Thompson subgroup of a compatible whole Sylow overlap

The hypotheses specify an injective quaternion-swap map, the extra
involution's conjugation equation and the two cosets filling the overlap.
They do not assume anything about the Thompson subgroup. The finite census
bounds elementary subgroups containing an involution outside the displayed
sixteen. Hence the sixteen is the unique elementary subgroup of maximum
order, and its image is the actual elementary Thompson subgroup.

Source: Aschbacher--Smith, proof of 14.2.21, printed p.988 (PDF p.1005).
The compatible Aut(M12) pair owner must instantiate these normal forms;
the order-64 swap subgroup is not asserted to be O2 of a parabolic.
-/

@[expose] public section
open QuaternionSwapModel
namespace QuaternionSwapModel.MarkedSylow

variable {G : Type*} [Group G] (f : QH →* G)

/-- The whole-overlap normal forms. The involution is the extra Sylow
coordinate, with a central twist on the factor swap. -/
structure Geometry (T : Subgroup G) where
  injective : Function.Injective f
  t : G
  square : t * t = 1
  outside : t ∉ f.range
  conjugation : ∀ w : Raw, t * f (projection w) * t⁻¹ = f (projection (twist w))
  cover : ∀ g : G, g ∈ T ↔ ∃ x : QH, ∃ b : Bool, g = f x * (if b then t else 1)

namespace Geometry
variable {f} {T : Subgroup G} (d : Geometry f T)

def word (x : QH) (b : Bool) : G := f x * (if b then d.t else 1)
def evaluate (n : Coordinates) : G := d.word (projection (raw n.1)) n.2

private theorem word_eq_iff (x y : QH) (b c : Bool) :
    d.word x b = d.word y c ↔ x = y ∧ b = c := by
  have hn (x y : QH) : f x ≠ f y * d.t := by
    intro h
    apply d.outside
    refine ⟨y⁻¹ * x, ?_⟩
    rw [map_mul, map_inv, h, inv_mul_cancel_left]
  cases b <;> cases c <;>
    simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one, and_true,
      and_false, reduceCtorEq, mul_right_cancel_iff]
  · exact d.injective.eq_iff
  · exact iff_false_intro (hn x y)
  · exact iff_false_intro (Ne.symm (hn y x))
  · exact d.injective.eq_iff

private theorem raw_projection_injective :
    Function.Injective (fun n : CoreCoordinates => projection (raw n)) := by
  intro n m h
  rw [projection_eq_iff] at h
  exact raw_injective n m h

private theorem raw_projection_surjective :
    Function.Surjective (fun n : CoreCoordinates => projection (raw n)) := by
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  obtain ⟨n, hn⟩ := raw_surjective w
  exact ⟨n, (projection_eq_iff _ _).mpr hn⟩

theorem evaluate_injective : Function.Injective d.evaluate := by
  intro n m h
  have he := (d.word_eq_iff _ _ _ _).mp h
  exact Prod.ext (raw_projection_injective he.1) he.2

theorem evaluate_cover (x : G) : x ∈ T ↔ ∃ n : Coordinates, d.evaluate n = x := by
  rw [d.cover]
  constructor
  · rintro ⟨q,b,rfl⟩
    obtain ⟨n,rfl⟩ := raw_projection_surjective q
    exact ⟨(n,b),rfl⟩
  · rintro ⟨n,rfl⟩
    exact ⟨projection (raw n.1),n.2,rfl⟩

private theorem evaluate_mul (n m : Coordinates) :
    d.evaluate n * d.evaluate m =
      f (projection (productRaw n m)) * (if xor n.2 m.2 then d.t else 1) := by
  have hc (w : Raw) : d.t * f (projection w) = f (projection (twist w)) * d.t := by
    rw [← d.conjugation w]
    group
  rcases n with ⟨n,b⟩
  rcases m with ⟨m,c⟩
  cases b <;> cases c <;>
    simp only [evaluate, word, productRaw, Bool.false_eq_true, ↓reduceIte,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      map_mul, mul_one]
  · rw [mul_assoc]
  · rw [mul_assoc, hc, ← mul_assoc]
  · rw [mul_assoc, ← mul_assoc d.t, hc, mul_assoc, d.square, mul_one]

-- Predicate reflection retains the literal maps, rather than an abstract tag.
theorem evaluate_square (n : Coordinates) : d.evaluate n ^ 2 = 1 ↔ Square n := by
  rw [pow_two, d.evaluate_mul]
  simp only [Bool.xor_self, Bool.false_eq_true, ↓reduceIte, mul_one]
  rw [← f.map_one, d.injective.eq_iff]
  exact QuotientGroup.eq_one_iff _

theorem evaluate_commute (n m : Coordinates) :
    d.evaluate n * d.evaluate m = d.evaluate m * d.evaluate n ↔ Commutes n m := by
  rw [d.evaluate_mul, d.evaluate_mul, Bool.xor_comm n.2 m.2, mul_right_cancel_iff,
    d.injective.eq_iff, projection_eq_iff]
  rfl

theorem evaluate_mem_A (n : Coordinates) : d.evaluate n ∈ A.map f ↔ InA n := by
  constructor
  · rintro ⟨x,hx,he⟩
    have he' : d.word x false = d.word (projection (raw n.1)) n.2 := by
      simpa only [evaluate, word, Bool.false_eq_true, ↓reduceIte, mul_one] using he
    obtain ⟨rfl,hb⟩ := (d.word_eq_iff _ _ _ _).mp he'
    exact ⟨hb.symm,hx⟩
  · rintro ⟨hb,hA⟩
    refine ⟨projection (raw n.1),hA,?_⟩
    simp only [evaluate, word, hb, Bool.false_eq_true, ↓reduceIte, mul_one]

include d in
theorem A_le : A.map f ≤ T := by
  rintro _ ⟨x,hx,rfl⟩
  exact (d.cover (f x)).mpr ⟨x,false,by simp⟩

open scoped IsMulCommutative

include d in
theorem large_elementary_le [Finite G] (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hET : E ≤ T) (hcard : 16 ≤ Nat.card E) : E ≤ A.map f := by
  intro x hx
  by_contra hn
  obtain ⟨n, rfl⟩ := (d.evaluate_cover x).mp (hET hx)
  have hns : Square n := (d.evaluate_square n).mp
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx)
  have hnA : ¬ InA n := fun h => hn ((d.evaluate_mem_A n).mpr h)
  choose r hr using fun y : E => (d.evaluate_cover y).mp (hET y.property)
  let R : E → {m : Coordinates // Square m ∧ Commutes n m} := fun y =>
    ⟨r y, (d.evaluate_square _).mp (by
      rw [hr]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ y.property),
      (d.evaluate_commute _ _).mp (by
        rw [hr]
        exact congrArg Subtype.val (mul_comm (⟨d.evaluate n,hx⟩ : E) y))⟩
  have hi : Function.Injective R := by
    intro y z he
    have h := congrArg (fun a : {m : Coordinates // Square m ∧ Commutes n m} =>
      d.evaluate a.val) he
    exact Subtype.ext ((hr y).symm.trans (h.trans (hr z)))
  have hle := Nat.card_le_card_of_injective R hi
  have hlt : Nat.card {m : Coordinates // Square m ∧ Commutes n m} < 16 := by
    simpa only [Nat.card_eq_fintype_card] using census n hns hnA
  omega

include d in
theorem max_elementary_family [Finite G] :
    Stellmacher.elementaryAbelianMaxSubgroups T = {A.map f} := by
  have he : IsElementaryAbelian 2 (A.map f) :=
    (inferInstance : IsElementaryAbelian 2 A).map f
  have hc : Nat.card (A.map f) = 16 := by
    rw [Subgroup.card_map_of_injective d.injective,card_A]
  ext E
  constructor
  · intro hE
    let _ : IsElementaryAbelian 2 E := hE.2.1
    have hn : 16 ≤ Nat.card E := by
      rw [← hc]
      exact hE.2.2 (A.map f) d.A_le he
    exact Subgroup.eq_of_le_of_card_ge (d.large_elementary_le E hE.1 hn)
      (by simpa only [hc] using hn)
  · rintro rfl
    refine ⟨d.A_le,he,?_⟩
    intro E hET hE
    let _ : IsElementaryAbelian 2 E := hE
    by_cases hn : 16 ≤ Nat.card E
    · exact Subgroup.card_le_of_le (d.large_elementary_le E hET hn)
    · rw [hc]
      omega

include d in
theorem thompson_eq [Finite G] :
    Stellmacher.elementaryAbelianMaxJ T = A.map f := by
  rw [Stellmacher.elementaryAbelianMaxJ,d.max_elementary_family,sSup_singleton]

end Geometry
end QuaternionSwapModel.MarkedSylow
