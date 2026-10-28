module
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Prime dihedral actions and involutive shears

Suppose a prime-order automorphism group P acts on K, and W together with
one P-conjugate generates K. An involution normalizing P and fixing W is
either trivial or a specified inverter of P fixing W. The proof restricts
the involution to P, where it is identity or inversion, and then uses the
two generating subgroups.

Source application: Aschbacher--Smith, original 12.2.25, printed p.805,
the pointwise hyperplane stabilizer in the automorphism group of U.
-/

public section
open Subgroup

namespace MulAut
variable {K : Type*} [Group K] [Finite K]
theorem prime_involutive (hp : (Nat.card K).Prime) (a : MulAut K)
    (ha : Function.Involutive a) : a = 1 ∨ ∀ k, a k = k⁻¹ := by
  classical
  by_cases h : a = 1
  · exact Or.inl h
  right
  apply congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive ?_ ha)
  intro k hk
  by_contra hk1
  let : Fact (Nat.card K).Prime := ⟨hp⟩
  have hgen := zpowers_eq_top_of_prime_card (G := K) rfl hk1
  apply h
  ext x
  have hx : x ∈ zpowers k := hgen ▸ mem_top x
  obtain ⟨i,rfl⟩ := hx
  simp only [map_zpow, hk, MulAut.one_apply]
end MulAut

namespace MulAut
variable {K : Type*} [Group K]
private theorem eq_one_of_fixed_generating_pair (W : Subgroup K) (g a : MulAut K)
    (hgen : W ⊔ W.map g.toMonoidHom = ⊤)
    (hfix : ∀ w ∈ W, a w = w) (hc : Commute a g) : a = 1 := by
  let F : Subgroup K := MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id K)
  have hWF : W ≤ F := hfix
  have hgF : W.map g.toMonoidHom ≤ F := by
    rintro _ ⟨w,hw,rfl⟩
    change a (g w) = g w
    have hh := congrArg (fun b : MulAut K => b w) hc.eq
    change a (g w) = g (a w) at hh
    rw [hh,hfix w hw]
  have hF : (⊤ : Subgroup K) ≤ F := hgen ▸ sup_le hWF hgF
  ext x
  exact hF (mem_top x)

/-- An involutive automorphism fixing a generating half of a prime dihedral
module is either trivial or the marked inverter. -/
theorem prime_dihedral_shear [Finite K]
    (P : Subgroup (MulAut K)) (hP : (Nat.card P).Prime)
    (W : Subgroup K) (g : MulAut K) (hg : g ∈ P)
    (hgen : W ⊔ W.map g.toMonoidHom = ⊤)
    (v : MulAut K) (hv : v ^ 2 = 1)
    (hvW : ∀ w ∈ W, v w = w)
    (hvinv : ∀ p ∈ P, v * p * v⁻¹ = p⁻¹)
    (a : MulAut K) (ha : a ^ 2 = 1)
    (haN : a ∈ normalizer (P : Set (MulAut K)))
    (haW : ∀ w ∈ W, a w = w) : a = 1 ∨ a = v := by
  let b := P.normalizerMonoidHom ⟨a,haN⟩
  have hb : Function.Involutive b := by
    intro p
    apply Subtype.ext
    change a * (a * (p : MulAut K) * a⁻¹) * a⁻¹ = p
    calc
      _ = a ^ 2 * (p : MulAut K) * (a ^ 2)⁻¹  := by simp only [pow_two]; group
      _ = p := by rw [ha]; simp
  rcases prime_involutive hP b hb with hid | hinv
  · left
    apply eq_one_of_fixed_generating_pair W g a hgen haW
    have he := congrArg Subtype.val (congrArg (fun c : MulAut P => c ⟨g,hg⟩) hid)
    change a * g * a⁻¹ = g at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · right
    have hgInv : a * g * a⁻¹ = g⁻¹ := congrArg Subtype.val (hinv ⟨g,hg⟩)
    have hav : a * v = 1 := by
      apply eq_one_of_fixed_generating_pair W g (a*v) hgen
      · intro w hw
        change a (v w) = w
        rw [hvW w hw,haW w hw]
      · have he : (a*v)*g*(a*v)⁻¹ = g := by
          calc
            _ = a*(v*g*v⁻¹)*a⁻¹ := by group
            _ = a*g⁻¹*a⁻¹ := by rw [hvinv g hg]
            _ = (a*g*a⁻¹)⁻¹ := by group
            _ = g := by rw [hgInv,inv_inv]
        exact mul_inv_eq_iff_eq_mul.mp he
    have hvv : v * v = 1 := by simpa only [pow_two] using hv
    calc
      a = a * (v*v) := by rw [hvv,mul_one]
      _ = (a*v)*v := by group
      _ = v := by rw [hav,one_mul]
end MulAut
