module

public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PCoreSurjective

/-!
# Squares over a central orbit in a perfect central extension

In a perfect central extension with kernel of exponent two, squares of
lifts agree whenever their images are conjugate and their squares map to
central elements. The preimage of the target center is central, and the
central kernel disappears on squaring.

Consequently a single nonempty orbit of square roots of a central involution
in the target two-core produces a unique square above that involution in the
source two-core. Comparing a root with its inverse proves that the square
itself is an involution. This does not assume involution lifting.

Source application: Aschbacher–Smith, I.2.2(5), J₂ calculation,
printed pp.411–412 / PDF pp.422–423 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {E B : Type*} [Group E] [Group B]

theorem square_eq_of_map_eq (f : E →* B) (hc : f.ker ≤ center E)
    (h2 : ∀ z ∈ f.ker, z ^ 2 = 1) {x y : E} (h : f x = f y) :
    x ^ 2 = y ^ 2 := by
  have hz : x⁻¹ * y ∈ f.ker := by simp [MonoidHom.mem_ker, h]
  have hcomm : Commute x (x⁻¹ * y) := mem_center_iff.mp (hc hz) x
  calc
    x ^ 2 = x ^ 2 * (x⁻¹ * y) ^ 2 := by rw [h2 _ hz, mul_one]
    _ = (x * (x⁻¹ * y)) ^ 2 := (hcomm.mul_pow 2).symm
    _ = y ^ 2 := by simp

theorem Cover.square_eq_of_isConj (f : Cover E B)
    (h2 : ∀ z ∈ f.toMonoidHom.ker, z ^ 2 = 1)
    {x y : E} (hx : f.toMonoidHom (x ^ 2) ∈ center B)
    (hxy : IsConj (f.toMonoidHom x) (f.toMonoidHom y)) : x ^ 2 = y ^ 2 := by
  have hxC : x ^ 2 ∈ center E := by
    rw [← f.comap_center]
    exact hx
  obtain ⟨b, hb⟩ := isConj_iff.mp hxy
  obtain ⟨g, rfl⟩ := f.surjective b
  have he := square_eq_of_map_eq f.toMonoidHom f.ker_le_center h2
    (x := g * x * g⁻¹) (y := y) (by simpa only [map_mul, map_inv] using hb)
  have hc : g * x ^ 2 * g⁻¹ = x ^ 2 := by
    rw [mem_center_iff.mp hxC g]
    group
  change (MulAut.conj g x) ^ 2 = y ^ 2 at he
  rw [← map_pow] at he
  exact hc.symm.trans he

theorem Cover.unique_core_square [Finite E] [Finite B] (f : Cover E B)
    (hk : IsPGroup 2 f.toMonoidHom.ker)
    (h2 : ∀ z ∈ f.toMonoidHom.ker, z ^ 2 = 1)
    (t : B) (ht : t ∈ center B)
    (hex : ∃ r ∈ pCore 2 B, r ^ 2 = t)
    (horbit : ∀ r ∈ pCore 2 B, ∀ s ∈ pCore 2 B,
      r ^ 2 = t → s ^ 2 = t → IsConj r s) :
    ∃! v : E, f.toMonoidHom v = t ∧ ∃ x ∈ pCore 2 E, x ^ 2 = v := by
  obtain ⟨r, hr, hr2⟩ := hex
  obtain ⟨x, rfl⟩ := f.surjective r
  have hx : x ∈ pCore 2 E := by
    rw [← f.toMonoidHom.comap_pCore_of_ker_isPGroup f.surjective hk]
    exact hr
  refine ⟨x ^ 2, ⟨by rwa [map_pow], x, hx, rfl⟩, ?_⟩
  rintro v ⟨hv, y, hy, rfl⟩
  have hyB : f.toMonoidHom y ∈ pCore 2 B := by
    change y ∈ (pCore 2 B).comap f.toMonoidHom
    rwa [f.toMonoidHom.comap_pCore_of_ker_isPGroup f.surjective hk]
  apply f.square_eq_of_isConj h2
  · rwa [hv]
  · exact horbit _ hyB _ hr (by rwa [← map_pow]) hr2

theorem Cover.core_square_order_two [Finite E] [Finite B] (f : Cover E B)
    (hk : IsPGroup 2 f.toMonoidHom.ker)
    (h2 : ∀ z ∈ f.toMonoidHom.ker, z ^ 2 = 1)
    (t : B) (ht : t ∈ center B) (ht2 : orderOf t = 2)
    (hex : ∃ r ∈ pCore 2 B, r ^ 2 = t)
    (horbit : ∀ r ∈ pCore 2 B, ∀ s ∈ pCore 2 B,
      r ^ 2 = t → s ^ 2 = t → IsConj r s) :
    ∃ v : E, orderOf v = 2 ∧ f.toMonoidHom v = t ∧
      (∃ x ∈ pCore 2 E, x ^ 2 = v) ∧
      ∀ w : E, f.toMonoidHom w = t → (∃ x ∈ pCore 2 E, x ^ 2 = w) → w = v := by
  obtain ⟨v, ⟨hv, x, hx, hx2⟩, huniq⟩ := f.unique_core_square hk h2 t ht hex horbit
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by
    have hp := pow_orderOf_eq_one t
    simpa only [ht2, pow_two] using hp)
  have hvinv : v⁻¹ = v := huniq _ ⟨by rw [map_inv, hv, htinv],
    x⁻¹, (pCore 2 E).inv_mem hx, by rw [inv_pow, hx2]⟩
  have hv2 : v ^ 2 = 1 := by
    calc
      v ^ 2 = v⁻¹ * v := by rw [hvinv, pow_two]
      _ = 1 := inv_mul_cancel v
  have hvne : v ≠ 1 := by
    intro h
    have htone : t = 1 := by rw [← hv, h, map_one]
    simp [htone] at ht2
  exact ⟨v, orderOf_eq_prime hv2 hvne, hv, ⟨x, hx, hx2⟩,
    fun w hw hroot => huniq w ⟨hw, hroot⟩⟩
end PerfectCentralCovering
