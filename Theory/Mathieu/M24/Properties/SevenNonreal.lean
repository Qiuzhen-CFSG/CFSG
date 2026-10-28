module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Coordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives
public import Mathlib.LinearAlgebra.Trace
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.CyclicFusion

/-!
# Nonreal seven-elements of the native Mathieu group

The binary trace of the eleven-dimensional cocode separates every nonidentity
power of the marked seven-element from its inverse. The calculation uses only
11 diagonal entries of the literal coordinate action for each of six powers;
the Lean kernel checks them. Trace invariance and Sylow conjugacy then exclude
conjugacy to the inverse for every element of order seven in M24.

The representative words and Golay coordinates retain the attribution in the
imported modules. Source: ATLAS M24 classes 7A--7B; the application to J4 is the
ordinary-component exclusion in Aschbacher--Smith 12.1.1, printed p.788.
-/

public noncomputable section
open Sporadic.Mathieu MathieuCode CocodeOctad.Involutions
open scoped BigOperators
namespace Sporadic.Mathieu.SevenNonreal
private def character (g : M24) : ZMod 2 := LinearMap.trace (ZMod 2) Cocode (cocodeRepresentation g)

private theorem character_conj {x y : M24} (h : IsConj x y) : character x = character y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  unfold character
  rw [cocodeRepresentation.map_mul,cocodeRepresentation.map_mul,
    LinearMap.trace_mul_comm,←mul_assoc,←cocodeRepresentation.map_mul,
    inv_mul_cancel,cocodeRepresentation.map_one,one_mul]

private theorem character_point (g : M24) : character g = ∑ i : Fin 11,
    reduce (Pi.single (g.val (nonpivot i)) 1 + Pi.single (g.val 23) 1) i := by
  have he : coordinateEquiv.symm.toLinearMap = sectionMap := by
    apply LinearMap.ext
    intro v
    apply coordinateEquiv.injective
    exact (coordinateEquiv.apply_symm_apply v).trans
      (LinearMap.congr_fun coordinates_sectionMap v).symm
  have hs (x : Fin 24) : fullRepresentation g (Pi.single x 1) = Pi.single (g.val x) 1 := by
    ext k
    simp [fullRepresentation, Pi.single_apply, Equiv.symm_apply_eq]
  rw [character,←LinearMap.trace_conj' _ coordinateEquiv,
    LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 11))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,Pi.basisFun_apply,
    Pi.basisFun_repr,LinearEquiv.conj_apply,he,
    LinearMap.comp_apply,sectionMap_single]
  change reduce (fullRepresentation g (coordinateWord i).val) i = _
  simp only [coordinateWord,map_add,hs]

private def seven : M24 := M24OddCyclic.representative 1 ^ 3
private theorem seven_order : orderOf seven = 7 := by
  rw [seven,orderOf_pow,M24OddCyclic.representative_order]
  rfl

private theorem trace_separates : ∀ k : Fin 7, k ≠ 0 →
    (∑ i : Fin 11,
      reduce (Pi.single (((M24OddCyclic.representativePerm 1 ^ 3) ^ k.val) (nonpivot i)) 1 +
        Pi.single (((M24OddCyclic.representativePerm 1 ^ 3) ^ k.val) 23) 1) i) ≠
    (∑ i : Fin 11,
      reduce (Pi.single (((M24OddCyclic.representativePerm 1 ^ 3) ^ k.val)⁻¹ (nonpivot i)) 1 +
        Pi.single (((M24OddCyclic.representativePerm 1 ^ 3) ^ k.val)⁻¹ 23) 1) i) := by
  decide +kernel

/-- Every element of order seven in native M24 is not conjugate to its inverse. -/
theorem not_real (x : M24) (hx : orderOf x = 7) : ¬ IsConj x x⁻¹ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨n,hn⟩ := IsConj.of_order_eq_prime_power_generator seven_order hx
    (by rw [m24_order]; decide : ¬7*7 ∣ Nat.card M24)
  let k : Fin 7 := ⟨n%7,Nat.mod_lt _ (by decide)⟩
  have hp : seven ^ k.val = seven ^ n := by
    simpa only [seven_order] using pow_mod_orderOf seven n
  have hk : k ≠ 0 := by
    intro he
    have ho : orderOf x = orderOf (seven ^ n) := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hn
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq x).symm
    rw [←hp,he,Fin.val_zero,pow_zero,orderOf_one,hx] at ho
    omega
  intro hr
  have hinv : IsConj x⁻¹ (seven ^ n)⁻¹ := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hn
    refine isConj_iff.mpr ⟨g, ?_⟩
    rw [←hg]
    group
  have hr' := hn.symm.trans (hr.trans hinv)
  rw [←hp] at hr'
  have he := character_conj hr'
  rw [character_point,character_point] at he
  exact trace_separates k hk he
end Sporadic.Mathieu.SevenNonreal
