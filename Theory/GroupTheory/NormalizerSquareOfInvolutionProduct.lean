module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# The square line in a commuting involution-cyclic product

If t is an involution commuting with y, every square in ⟨t,y⟩ lies in
⟨y²⟩. A normalizer of ⟨t,y⟩ consequently normalizes ⟨y²⟩. This elementary
square calculation is the Frattini-line argument used to identify y²
with the marked central involution in Aschbacher--Smith 2.5.15, p.559.
-/
public section
namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_square_line_of_involution_product
    (t y : G) (ht : t^2=1) (hcomm : Commute t y) :
    normalizer ((zpowers t ⊔ zpowers y : Subgroup G) : Set G) ≤ normalizer (zpowers (y^2) : Set G) := by
  let C := zpowers t ⊔ zpowers y
  have hn : zpowers y ≤ normalizer (zpowers t : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro a ha
    obtain ⟨n,rfl⟩ := ha
    exact (hcomm.zpow_right n).symm.eq
  have hs : ∀ a ∈ C, a^2 ∈ zpowers (y^2) := by
    intro a ha
    have hm : a ∈ (zpowers t : Set G) * (zpowers y : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
      exact ha
    obtain ⟨u,hu,v,hv,rfl⟩ := hm
    obtain ⟨m,rfl⟩ := hu
    obtain ⟨n,rfl⟩ := hv
    rw [((hcomm.zpow_left m).zpow_right n).mul_pow]
    have hp (a : G) (n : ℤ) : (a^n)^2=(a^2)^n := by
      simpa only [zpow_ofNat] using zpow_comm a n (2 : ℤ)
    have ht' : (t^m)^2=1 := by rw [hp,ht,one_zpow]
    rw [ht',one_mul,hp]
    exact zpow_mem_zpowers (y^2) n
  have hpres (g : G) (hg : g ∈ normalizer (C : Set G)) :
      ∀ a ∈ zpowers (y^2), g*a*g⁻¹ ∈ zpowers (y^2) := by
    have hyC : y ∈ C := mem_sup_right (mem_zpowers y)
    have hy' : g*y*g⁻¹ ∈ C := (mem_normalizer_iff.mp hg y).mp hyC
    have hh := hs _ hy'
    have he : (g*y*g⁻¹)^2 = g*y^2*g⁻¹ := by simp only [pow_two,mul_assoc,inv_mul_cancel_left]
    rw [he] at hh
    have hle : (zpowers (y^2)).map (MulAut.conj g).toMonoidHom ≤ zpowers (y^2) := by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hh
    intro a ha
    exact hle (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  intro x hx a
  constructor
  · exact hpres x hx a
  · intro ha
    have hh := hpres x⁻¹ ((normalizer (C : Set G)).inv_mem hx) _ ha
    change a ∈ zpowers (y^2)
    simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hh
end Subgroup
