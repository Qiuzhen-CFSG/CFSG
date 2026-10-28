module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# The septic trace of a faithful six-dimensional representation

Let q have order seven and be conjugate both to its square and to its inverse.
Combining these conjugacies gives a conjugator acting by exponent five. Over an
algebraically closed field of characteristic two, the separable cyclic weight
decomposition and faithfulness supply a nontrivial seventh-root eigenvector.
Its six translates have distinct eigenvalues, since five generates the units
modulo seven. In dimension six they form a basis. Their eigenvalues sum to
minus one, which is one in characteristic two. Faithful scalar extension and
trace compatibility give the same result over every characteristic-two field.

The final theorem applies this calculation to the literal J₂ word `a * b`.
Its order, square conjugacy and inverse conjugacy remain explicit group inputs;
the calculation assumes neither eigenvalue multiplicities nor irreducibility.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected Table 2,
the characteristic-two degree-six J₂ entry. See ../Source.md. The eigenvector
orbit construction follows the existing SeventeenFrobeniusModule/Orbit.lean.
-/

open scoped IsMulCommutative TensorProduct
open Module
namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
variable {E G U : Type*} [Field E] [Group G]
  [AddCommGroup U] [Module E U] [FiniteDimensional E U]

private theorem root_eigenvector [IsAlgClosed E] (ρ : Representation E G U)
    (hf : Function.Injective ρ) (q : G) (hq : orderOf q = 7) (h7 : (7 : E) ≠ 0) :
    ∃ μ : E, orderOf μ = 7 ∧ ∃ v : U, Module.End.HasEigenvector (ρ q) μ v := by
  let K := Subgroup.zpowers q
  let a : K := ⟨q, Subgroup.mem_zpowers q⟩
  let σ := ρ.comp K.subtype
  have ha : a ≠ 1 := by
    intro h
    have he : q = 1 := congrArg Subtype.val h
    simp [he] at hq
  have horder : (Nat.card K : E) ≠ 0 := by simpa [K, Nat.card_zpowers, hq] using h7
  have hc : ∃ χ : CharacterWeight σ, χ.val a ≠ 1 := by
    by_contra! hn
    apply ha
    apply eq_of_characterWeight_values σ (hf.comp Subtype.val_injective) horder
    intro χ
    simp [hn χ]
  obtain ⟨χ, hχ⟩ := hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.property
  let μ : E := χ.val a
  have hμ : μ ≠ 1 := fun h => hχ (Units.ext h)
  have ha7 : a ^ 7 = 1 := by
    apply Subtype.ext
    exact hq ▸ pow_orderOf_eq_one q
  have hμ7 : μ ^ 7 = 1 := by
    change (↑(χ.val a) : E) ^ 7 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ha7, map_one, Units.val_one]
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine ⟨μ, orderOf_eq_prime hμ7 hμ, v, ?_, hv0⟩
  exact (Submodule.mem_iInf _).mp hv a

omit [FiniteDimensional E U] in
private theorem eigen_orbit (ρ : Representation E G U) (q r : G)
    (hrel : r * q * r⁻¹ = q ^ 5) {μ : E} {v : U}
    (hv : Module.End.HasEigenvector (ρ q) μ v) (n : ℕ) :
    Module.End.HasEigenvector (ρ q) (μ ^ (5 ^ n)) (ρ (r⁻¹ ^ n) v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hc : q * r⁻¹ = r⁻¹ * q ^ 5 := by
      rw [← hrel]
      group
    have hp : (ρ q) (ρ r⁻¹ (ρ (r⁻¹ ^ n) v)) =
        ρ r⁻¹ ((ρ q ^ 5) (ρ (r⁻¹ ^ n) v)) := by
      rw [← map_pow]
      change (ρ q * ρ r⁻¹) _ = (ρ r⁻¹ * ρ (q ^ 5)) _
      rw [← map_mul, ← map_mul, hc]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, hp, ih.pow_apply 5, map_smul]
      rw [← pow_mul, pow_succ]
    · intro hz
      apply ih.2
      have hh := congrArg (ρ r) hz
      simpa [pow_succ', ← Module.End.mul_apply, ← map_mul] using hh

private theorem eigenvalues_injective {μ : E} (hμ : orderOf μ = 7) :
    Function.Injective (fun i : Fin 6 => μ ^ (5 ^ i.val)) := by
  intro i j hij
  have hfin : IsOfFinOrder μ := orderOf_pos_iff.mp (by omega)
  have hm := hfin.pow_inj_mod.mp hij
  rw [hμ] at hm
  have hnumeric : Function.Injective (fun i : Fin 6 => 5 ^ i.val % 7) := by decide
  exact hnumeric hm

private theorem sum_eigenvalues {μ : E} (hμ : orderOf μ = 7) :
    (∑ i : Fin 6, μ ^ (5 ^ i.val)) = -1 := by
  have hp : μ ^ 7 = 1 := hμ ▸ pow_orderOf_eq_one μ
  have hn : μ ≠ 1 := by
    intro he
    simp [he] at hμ
  have hs : (∑ i ∈ Finset.range 7, μ ^ i) = 0 := by
    have h := geom_sum_mul μ 7
    rw [hp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hn)
  have hreindex : (∑ i : Fin 6, μ ^ (5 ^ i.val)) + 1 =
      ∑ i ∈ Finset.range 7, μ ^ i := by
    have hm (i : Fin 6) : μ ^ (5 ^ i.val) = μ ^ (5 ^ i.val % 7) :=
      pow_eq_pow_mod _ hp
    simp_rw [hm]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty]
    norm_num
    ring
  exact eq_neg_of_add_eq_zero_left (hreindex.trans hs)

private theorem conj_five (q : G) (hq : orderOf q = 7)
    (hsq : IsConj q (q ^ 2)) (hinv : IsConj q q⁻¹) :
    ∃ r : G, r * q * r⁻¹ = q ^ 5 := by
  have hp : q ^ 7 = 1 := hq ▸ pow_orderOf_eq_one q
  have he : q⁻¹ ^ 2 = q ^ 5 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add]
    exact hp
  exact isConj_iff.mp (he ▸ hsq.trans (hinv.pow 2))

/-- Over an algebraically closed characteristic-two field, the six distinct
nontrivial septic eigenvalues give trace one. Only the stated conjugacies of
an order-seven element and faithfulness in dimension six are required. -/
public theorem character_septic_algebraicallyClosed [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E G U) (hf : Function.Injective ρ)
    (hd : finrank E U = 6) (q : G) (hq : orderOf q = 7)
    (hsq : IsConj q (q ^ 2)) (hinv : IsConj q q⁻¹) : ρ.character q = 1 := by
  classical
  obtain ⟨r, hr⟩ := conj_five q hq hsq hinv
  have h7 : (7 : E) ≠ 0 := (CharP.cast_eq_zero_iff E 2 7).not.mpr (by decide)
  obtain ⟨μ, hμ, v, hv⟩ := root_eigenvector ρ hf q hq h7
  have hi := Module.End.eigenvectors_linearIndependent' (ρ q) _ (eigenvalues_injective hμ)
    _ (fun i : Fin 6 => eigen_orbit ρ q r hr hv i.val)
  let b : Basis (Fin 6) E U := basisOfLinearIndependentOfCardEqFinrank hi (by simp [hd])
  have hb (i : Fin 6) : ρ q (b i) = μ ^ (5 ^ i.val) • b i := by
    simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank] using
      (eigen_orbit ρ q r hr hv i.val).apply_eq_smul
  change LinearMap.trace E U (ρ q) = 1
  rw [LinearMap.trace_eq_matrix_trace E b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  simp_rw [hb, map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, mul_one]
  rw [sum_eigenvalues hμ]
  exact CharTwo.neg_eq _

/-- The septic trace calculation over an arbitrary characteristic-two field,
by faithful scalar extension to its algebraic closure and trace compatibility. -/
public theorem character_septic [CharP E 2]
    (ρ : Representation E G U) (hf : Function.Injective ρ)
    (hd : finrank E U = 6) (q : G) (hq : orderOf q = 7)
    (hsq : IsConj q (q ^ 2)) (hinv : IsConj q q⁻¹) : ρ.character q = 1 := by
  let C := AlgebraicClosure E
  have hfC : Function.Injective (extendScalars C ρ) :=
    (extendScalars_faithful_iff C ρ).mp hf
  have hdC : finrank C (C ⊗[E] U) = 6 := by
    simpa only [Module.finrank_baseChange] using hd
  have ht := character_septic_algebraicallyClosed (extendScalars C ρ) hfC hdC q hq hsq hinv
  apply (algebraMap E C).injective
  change algebraMap E C (LinearMap.trace E U (ρ q)) = algebraMap E C 1
  rw [← LinearMap.trace_baseChange, map_one]
  exact ht

/-- Conditional application to the literal standard-generator product in J₂.
This supplies the septic spectral input to the six-dimensional trace certificate;
the group-hypothesis producer must discharge all three displayed assumptions. -/
public theorem character_ab [CharP E 2]
    (ρ : Representation E Sporadic.LeechRelated.J2.Carrier U)
    (hf : Function.Injective ρ) (hd : finrank E U = 6)
    (horder : orderOf (Sporadic.LeechRelated.J2.GeneratorPair.a *
      Sporadic.LeechRelated.J2.GeneratorPair.b) = 7)
    (hsq : IsConj (Sporadic.LeechRelated.J2.GeneratorPair.a *
      Sporadic.LeechRelated.J2.GeneratorPair.b)
      ((Sporadic.LeechRelated.J2.GeneratorPair.a *
        Sporadic.LeechRelated.J2.GeneratorPair.b) ^ 2))
    (hinv : IsConj (Sporadic.LeechRelated.J2.GeneratorPair.a *
      Sporadic.LeechRelated.J2.GeneratorPair.b)
      (Sporadic.LeechRelated.J2.GeneratorPair.a *
        Sporadic.LeechRelated.J2.GeneratorPair.b)⁻¹) :
    ρ.character (Sporadic.LeechRelated.J2.GeneratorPair.a *
      Sporadic.LeechRelated.J2.GeneratorPair.b) = 1 :=
  character_septic ρ hf hd _ horder hsq hinv

end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
