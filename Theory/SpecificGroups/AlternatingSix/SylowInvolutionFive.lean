module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry.Representatives

/-!
# Sylow-central involutions and five-cycles in A₆

In a two-subgroup of Aut(A₆) containing the inner Sylow and escaping the
natural S₆, every central involution is inner. The holomorph centralizer
calculation proves this without a new enumeration. Every A₆ involution
then inverts an element of order five, by involution conjugacy and the
explicit five-cycle inverter.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.2.17,
printed p.230, and the intrinsic Aut(A₆) Sylow calculations on pp.568–570.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal
open Identification SylowGeometry

theorem central_involution_mem_inner_of_escape (P : Sylow 2 AutA6)
    (S : Subgroup P) (hDS : sylowInner P ≤ S) (hout : ¬ S ≤ sylowNatural P)
    (v : P) (hv2 : v ^ 2 = 1) (hc : ∀ x ∈ S, x * v = v * x) :
    v ∈ sylowInner P := by
  have hZD : center P ≤ sylowInner P := by
    rw [center_eq]
    apply zpowers_le.mpr
    rw [← sylowEquiv_innerD P]
    apply mem_map_of_mem
    rw [show 4 = 2 * 2 from rfl, pow_mul]
    exact Subgroup.pow_mem _ (subset_closure (by simp)) _
  by_contra hvD
  have hvC : v ∈ centralizer (sylowInner P : Set P) := by
    intro x hx
    exact hc x (hDS hx)
  have hC := centralizer_innerCentralizer_involution P v hvC
    (fun h => hvD (hZD h)) hv2
  rw [centralizer_transposition] at hC
  apply hout
  intro x hx
  rw [← hC, mem_centralizer_singleton_iff]
  exact hc x hx

theorem involution_inverts_five (v : A6) (hv : orderOf v = 2) :
    ∃ r : A6, orderOf r = 5 ∧ v * r * v⁻¹ = r⁻¹ := by
  let i := GoldenClassGeometry.inverter
  have hi : orderOf i = 2 := by
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  have hif : i * GoldenClassGeometry.a5 * i⁻¹ = GoldenClassGeometry.a5⁻¹ := by
    decide +kernel
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj i v hi hv)
  let e := MulAut.conj g
  have hev : e i = v := hg
  refine ⟨e GoldenClassGeometry.a5, ?_, ?_⟩
  · rw [e.orderOf_eq]
    exact GoldenClassGeometry.rep_orders 5
  · rw [← hev, ← map_mul, ← map_inv, ← map_mul, hif, map_inv]
end AlternatingSix.ShadowLocal
