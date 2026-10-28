module
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Line
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A partial inverter in every Sylow two-subgroup of GL₂(3)

The matrix diag(-1,1) inverts the first coordinate generator and fixes the
second. Place its cyclic group in a Sylow subgroup, and conjugate that Sylow
to the prescribed one. Applying the same coordinate change to the generators
preserves generation of the entire ternary plane.

This is the concrete local input to the odd central-cover calculation of
Fong--Seitz I (4A)(c), printed p.19, in its degree-nine case.
-/

open Subgroup Matrix
open scoped Pointwise
namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
private abbrev V := Multiplicative (Fin 2 → ZMod 3)
private abbrev L := GL (Fin 2) (ZMod 3)

public theorem three_sylow_partial_inversion (S : Sylow 2 (GL (Fin 2) (ZMod 3))) :
    ∃ (x y : Multiplicative (Fin 2 → ZMod 3)) (r : S),
      closure ({x,y} : Set (Multiplicative (Fin 2 → ZMod 3))) = ⊤ ∧
      x ^ 3 = 1 ∧ planeAction 3 r x = x⁻¹ ∧ planeAction 3 r y = y := by
  let a : V := Multiplicative.ofAdd ![1,0]
  let b : V := Multiplicative.ofAdd ![0,1]
  have hab : closure ({a,b} : Set V) = ⊤ := by
    apply top_unique
    intro v _
    have hv : v = a ^ (v.toAdd 0).val * b ^ (v.toAdd 1).val := by
      have hh : ∀ v : V, v = a ^ (v.toAdd 0).val * b ^ (v.toAdd 1).val := by decide
      exact hh v
    rw [hv]
    exact (closure ({a,b} : Set V)).mul_mem
      ((closure ({a,b} : Set V)).pow_mem (subset_closure (by simp)) _)
      ((closure ({a,b} : Set V)).pow_mem (subset_closure (by simp)) _)
  let d : L := diagonalPair (ZMod 3) (-1,1)
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by decide) (by decide)
  have hdp : IsPGroup 2 (zpowers d) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hd2,pow_one])
  obtain ⟨T,hT⟩ := hdp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L T S
  have hr : g*d*g⁻¹ ∈ (S : Subgroup L) := by
    rw [←hg]
    exact smul_mem_pointwise_smul d (MulAut.conj g) (T : Subgroup L) (hT (mem_zpowers d))
  let c := planeAction 3 g
  refine ⟨c a,c b,⟨g*d*g⁻¹,hr⟩,?_,?_,?_,?_⟩
  · have hh := congrArg (fun H : Subgroup V => H.map c.toMonoidHom) hab
    rw [←MonoidHom.range_eq_map] at hh
    have hc : c.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr c.surjective
    rw [hc] at hh
    simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      MulEquiv.coe_toMonoidHom] using hh
  · rw [← map_pow,show a^3=1 by decide,map_one]
  · have hd : planeAction 3 d a = a⁻¹ := by decide
    change planeAction 3 (g*d*g⁻¹) (planeAction 3 g a) = _
    simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply_self]
    rw [hd,map_inv]
  · have hd : planeAction 3 d b = b := by decide
    change planeAction 3 (g*d*g⁻¹) (planeAction 3 g b) = _
    simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply_self]
    rw [hd]
end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
