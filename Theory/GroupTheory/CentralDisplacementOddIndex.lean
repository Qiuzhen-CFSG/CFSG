module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Group

/-!
# Central displacement detected on a subgroup of odd index

For an automorphism whose right displacement g⁻¹ α(g) lies in a central
subgroup Z, that displacement is a homomorphism into Z. If Z has order
dividing two and the automorphism fixes a subgroup of odd index, the
homomorphism is trivial: its image order divides both two and that index.
Thus the automorphism is the identity.

This elementary argument supplies the unsquared displacement step in the
Janko max1-centralizer amalgam, independently of any particular group model.
-/

@[expose] public section

namespace MonoidHom
theorem eq_one_of_odd_index_kernel {G P : Type*} [Group G] [Group P]
    (f : G →* P) (D : Subgroup G) (hD : D ≤ f.ker)
    (hi : ¬ 2 ∣ D.index) (hP : Nat.card P ∣ 2) (g : G) : f g = 1 := by
  have hdiv : f.ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_subgroup_dvd_card f.range).trans hP
  have hone : f.ker.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact h
    · exact False.elim (hi (h ▸ Subgroup.index_dvd_of_le hD))
  have hk := Subgroup.index_eq_one.mp hone
  exact show g ∈ f.ker from hk ▸ Subgroup.mem_top g
end MonoidHom

namespace MulAut
def centralDisplacement {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) (alpha : MulAut G)
    (hd : ∀ g, g⁻¹ * alpha g ∈ Z) : G →* Z where
  toFun g := ⟨g⁻¹ * alpha g, hd g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    apply Subtype.ext
    change (g * h)⁻¹ * alpha (g * h) =
      (g⁻¹ * alpha g) * (h⁻¹ * alpha h)
    have hc := Subgroup.mem_center_iff.mp (hZ (hd g)) h⁻¹
    simp only [map_mul, mul_inv_rev]
    calc
      _ = h⁻¹ * (g⁻¹ * alpha g) * alpha h := by group
      _ = (g⁻¹ * alpha g) * h⁻¹ * alpha h := by rw [← hc]
      _ = _ := by group

theorem eq_one_of_central_displacement_of_odd_index
    {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1)
    (hc : z ∈ Subgroup.center G) (alpha : MulAut G)
    (hd : ∀ g, g⁻¹ * alpha g ∈ Subgroup.zpowers z)
    (D : Subgroup G) (hi : ¬ 2 ∣ D.index)
    (hfix : ∀ g ∈ D, alpha g = g) : alpha = 1 := by
  let d := centralDisplacement (Subgroup.zpowers z) (Subgroup.zpowers_le.mpr hc) alpha hd
  have hD : D ≤ d.ker := by
    intro g hg
    apply Subtype.ext
    change g⁻¹ * alpha g = 1
    rw [hfix g hg, inv_mul_cancel]
  have hcard : Nat.card (Subgroup.zpowers z) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hz
  ext g
  have he := congrArg Subtype.val
    (MonoidHom.eq_one_of_odd_index_kernel d D hD hi hcard g)
  change g⁻¹ * alpha g = 1 at he
  exact (inv_mul_eq_one.mp he).symm
end MulAut
