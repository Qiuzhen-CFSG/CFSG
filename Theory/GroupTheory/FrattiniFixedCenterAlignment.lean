module
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Fixed-center alignment through a Frattini quotient

A conjugate elementary center either equals the fixed center or is disjoint
from it. In the disjoint case the two equal-order elementary subgroups span a
maximal plane. Its centralizer acts trivially on the plane modulo the fixed
center, and the given quotient-action kernel forces its Frattini subgroup
into that center. This contradicts disjointness.

Source: Aschbacher–Smith, the single linear block terminal argument, p.539.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem eq_fixed_center_of_frattini_quotient_kernel
    (P U V Z I J K : Subgroup G)
    (hIP : I≤P) (hJU : J≤U) (hZU : Z≤U) (hUV : U⊓V=Z)
    (hZcent : Z≤centralizer (U:Set G)) (hZn : P≤normalizer (Z:Set G))
    (hIJ : I≤centralizer (J:Set G))
    (hper : ∀a∈P,U.map (MulAut.conj a).toMonoidHom=U ∨ U.map (MulAut.conj a).toMonoidHom=V)
    (hTI : J=Z ∨ Disjoint Z J)
    (hcJ : Nat.card J=Nat.card Z) (hcU : Nat.card U=Nat.card Z^2)
    (hphiI : (frattini I).map I.subtype=J) (hK : IsPGroup 2 K)
    (hphiK : (frattini K).map K.subtype≤Z)
    (hkernel : ∀a∈P,a∈normalizer (U:Set G)→
      (∀u∈U,a*u*a⁻¹*u⁻¹∈Z)→a∈K) : J=Z := by
  rcases hTI with h | hd
  · exact h
  by_contra hn
  have hnot : ¬J≤Z := fun hj=>hn (eq_of_le_of_card_ge hj hcJ.ge)
  have hgen : Z⊔J=U := by
    apply eq_of_le_of_card_ge (sup_le hZU hJU)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z J
      ((hJU.trans (le_centralizer_iff.mp hZcent)).trans (Subgroup.centralizer_le_normalizer _)) hd,hcJ,hcU,pow_two]
  have hIK : I≤K := by
    intro a ha
    have hJmap : J≤U.map (MulAut.conj a).toMonoidHom := by
      intro j hj
      refine ⟨j,hJU hj,?_⟩
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hIJ ha)) j hj).symm
    have haU : a∈normalizer (U:Set G) := by
      rcases hper a (hIP ha) with he | he
      · exact mem_normalizer_iff_map_conj_eq.mpr he
      · exact False.elim (hnot (le_inf hJU (he ▸ hJmap) |>.trans hUV.le))
    apply hkernel a (hIP ha) haU
    intro u hu
    have hup : u∈(Z:Set G)*(J:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left Z J
        ((hJU.trans (le_centralizer_iff.mp hZcent)).trans (Subgroup.centralizer_le_normalizer _)),hgen]
      exact hu
    obtain ⟨z,hz,j,hj,rfl⟩ := hup
    have haj : a*j=j*a := ((mem_centralizer_iff.mp (hIJ ha)) j hj).symm
    have haz : a*z*a⁻¹∈Z := ((mem_normalizer_iff.mp (hZn (hIP ha))) z).mp hz
    have he : a*(z*j)*a⁻¹*(z*j)⁻¹=(a*z*a⁻¹)*z⁻¹ := by
      calc
        _ = a*z*(j*a⁻¹*j⁻¹)*z⁻¹ := by group
        _ = (a*z*a⁻¹)*z⁻¹ := by
          rw [show j*a⁻¹*j⁻¹=a⁻¹ from mul_inv_eq_iff_eq_mul.mpr (Commute.inv_left haj).symm.eq]
    rw [he]
    exact Z.mul_mem haz (Z.inv_mem hz)
  exact hnot (hphiI ▸ (frattini_image_le_of_le hIK hK).trans hphiK)
end Subgroup
