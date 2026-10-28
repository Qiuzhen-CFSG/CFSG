module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearNaturalSum
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.SpecificGroups.SL2.OddSylowCentralizer

/-!
# Odd fixed subgroups of the original linear-two pair

A nonidentity odd-order element in the marked SL₂ quotient centralizes no
nonidentity element of the Sylow image of V. Thus its fixed subgroup in V
lies in the original two-core P. The checked natural-sum coordinates on P/Z
then have no nonzero fixed vectors, giving C_V(x) = Z. Only the order of the
actual quotient image is used; the element need not have odd order upstairs.

This supplies the linear-two case of the torus fixed-space clause for the
literal selected Hermitian action, including the quotient over field four.
Source: Aschbacher–Smith E.2.14(3,9), printed pp.226–227, and 8.2.2(8),
printed p.715 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

/-- The original fixed subgroup is the central intersection whenever the
actual linear-two quotient image has nontrivial odd order. -/
theorem linear_pair_odd_centralizer
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 X} {V M : Subgroup X} {g : X}
    (h : TwoConjugate.Hypotheses T V M g)
    (hMN : M ≤ normalizer (V : Set X))
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ TwoConjugate.J M) ≃* SL(2,F))
    (R : Sylow 2 SL(2,F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) = R)
    (hMS : M.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))) =
      normalizer (R : Set SL(2,F)))
    (x : X) (ho : Odd (orderOf (ξ (QuotientGroup.mk' (TwoConjugate.J M) x))))
    (hne : ξ (QuotientGroup.mk' (TwoConjugate.J M) x) ≠ 1) :
    V ⊓ centralizer ({x} : Set X) = TwoConjugate.Z V g := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  let q := QuotientGroup.mk' (TwoConjugate.Z V g)
  let π := ξ.toMonoidHom.comp (QuotientGroup.mk' (TwoConjugate.J M))
  let U := (TwoConjugate.P V M g).map q
  obtain ⟨d,e,he⟩ := h.linear_pair_natural_coordinates hMN m hm hcard ξ R hVS hMS
  have hJP : TwoConjugate.J M = TwoConjugate.P V M g :=
    (h.J_eq_twoCore_of_linear_two m hm hcard ξ).trans
      (h.linear_pair_core_eq hMN m hm hcard ξ R hVS hMS)
  apply le_antisymm
  · intro v hv
    have hc : Commute v x := mem_centralizer_singleton_iff.mp hv.2
    have hvπ : π v = 1 := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
      R (π v) (π x) (by change π v ∈ (R : Subgroup _); rw [←hVS]; exact mem_map_of_mem π hv.1) hne ho (pow_orderOf_eq_one _) (hc.map π)
    have hvP : v ∈ TwoConjugate.P V M g := by
      rw [←hJP]
      exact (QuotientGroup.eq_one_iff v).mp (ξ.map_eq_one_iff.mp hvπ)
    let u : Additive U := Additive.ofMul ⟨q v,mem_map_of_mem q hvP⟩
    have hu : normalRepresentation U (q x) u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change q x * q v * (q x)⁻¹ = q v
      rw [←map_inv,←map_mul,←map_mul,hc.symm.eq,mul_assoc,mul_inv_cancel,mul_one]
    have heu : e u = 0 := by
      funext j
      apply Matrix.SL2.odd_power_fixed_eq_zero (π x) _ ho (pow_orderOf_eq_one _) hne
      exact (he x u j).symm.trans (congrArg (fun z => e z j) hu)
    have hu0 : u = 0 := e.injective (heu.trans e.map_zero.symm)
    exact (QuotientGroup.eq_one_iff v).mp (congrArg (fun z : Additive U => (z.toMul : X ⧸ TwoConjugate.Z V g)) hu0)
  · exact le_inf inf_le_left ((h.core_geometry.2.2.trans inf_le_right).trans (center_le_centralizer _))

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
