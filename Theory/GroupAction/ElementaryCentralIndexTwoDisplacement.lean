module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Elementary displacement of central index two

An automorphism preserving squares has central displacement if all its
displacements lie in an elementary two-subgroup U and the intersection of
U with the center has index two in U. No finiteness hypothesis is required.

Square preservation makes each input commute with its involutory
displacement. If one displacement u is noncentral, every other noncentral
displacement differs from u by a central element, so its input centralizes
u. An input with central displacement becomes an input with noncentral
displacement after multiplying by the chosen input. Thus all inputs
centralize u, a contradiction.

This is the elementary reason the small-case first residual-core action
in Stellmacher (10.1)(a3), printed p.61 before (8), has image in its
central line when its image was only known to lie in the neighboring
central plane. Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace MulAut

public theorem displacement_mem_center_of_elementary_central_index_two
    {R : Type*} [Group R] (U : Subgroup R) [IsElementaryAbelian 2 U]
    (hindex : ((Subgroup.center R).subgroupOf U).index = 2)
    (f : MulAut R) (hsquare : ∀ r : R, (f r)^2 = r^2)
    (hU : ∀ r : R, r⁻¹ * f r ∈ U) :
    ∀ r : R, r⁻¹ * f r ∈ Subgroup.center R := by
  classical
  let d : R → R := fun r => r⁻¹ * f r
  have hd2 (r : R) : d r * d r = 1 := by
    exact (pow_two (d r)) ▸ elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (A := U) (d r) (hU r)
  have hrd (r : R) : Commute r (d r) := by
    have hh : (r * d r) * (r * d r) = r * r := by
      simpa only [d, mul_inv_cancel_left, pow_two] using hsquare r
    change r * d r = d r * r
    calc
      r * d r = r⁻¹ * (r * r) * d r := by group
      _ = r⁻¹ * ((r * d r) * (r * d r)) * d r := by rw [hh]
      _ = (d r * r) * (d r * d r) := by group
      _ = d r * r := by rw [hd2 r,mul_one]
  intro t
  by_contra ht
  change d t ∉ Subgroup.center R at ht
  have hnoncentral (r : R) (hr : d r ∉ Subgroup.center R) : Commute r (d t) := by
    have hz : (d r)⁻¹ * d t ∈ Subgroup.center R := by
      have hh : (⟨d r,hU r⟩ : U)⁻¹ * ⟨d t,hU t⟩ ∈
          (Subgroup.center R).subgroupOf U := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        change (d r)⁻¹ ∈ Subgroup.center R ↔ d t ∈ Subgroup.center R
        simp only [Subgroup.inv_mem_iff, hr, ht]
      exact hh
    have hzcomm : Commute r ((d r)⁻¹ * d t) :=
      Subgroup.mem_center_iff.mp hz r
    simpa only [mul_inv_cancel_left] using (hrd r).mul_right hzcomm
  have hall (r : R) : Commute r (d t) := by
    by_cases hr : d r ∈ Subgroup.center R
    · have htr : d (t*r) ∉ Subgroup.center R := by
        intro hprod
        have hz := (inferInstance : (Subgroup.center R).Normal).conj_mem
          (d (t*r) * (d r)⁻¹)
          ((Subgroup.center R).mul_mem hprod ((Subgroup.center R).inv_mem hr)) r
        apply ht
        convert hz using 1
        dsimp only [d]
        rw [map_mul]
        group
      have hprod := hnoncentral (t*r) htr
      have htcomm := (hrd t).inv_left
      have hh := htcomm.mul_left hprod
      simpa only [inv_mul_cancel_left] using hh
    · exact hnoncentral r hr
  apply ht
  exact Subgroup.mem_center_iff.mpr (fun r => (hall r).eq)

end MulAut
