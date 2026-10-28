module

public import Theory.Representation.SL2.BinaryNaturalTripleRecognition
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned

/-!
# The actual eight-dimensional binary SL₂(8) module

Irreducibility and dimension eight determine the actual action: its Schur
degree divides both three and eight, hence is one. The highest-weight digit
dimension formula then forces weight seven, with all three binary digits
present. The existing polynomial-to-tensor comparison descends this action
to the triple Frobenius tensor over GF(8).
-/

public noncomputable section
open scoped MatrixGroups MonoidAlgebra TensorProduct
namespace Representation.SL2.BinarySmall
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem eight_action_nontrivial
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 8) : ∃ g, ρ g ≠ 1 := by
  classical
  by_contra! htriv
  let b := Module.finBasis (ZMod 2) V
  let i : Fin (Module.finrank (ZMod 2) V) := ⟨0, by omega⟩
  let W : Subrepresentation ρ := {
    toSubmodule := Submodule.span (ZMod 2) {b i}
    apply_mem_toSubmodule := by
      intro g v hv
      simpa only [htriv, Module.End.one_apply] using hv }
  have hWne : W ≠ ⊥ := by
    intro hW
    have hv : b i ∈ W := Submodule.subset_span (Set.mem_singleton (b i))
    rw [hW] at hv
    exact b.ne_zero i hv
  have hWtop : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hWne
  have he : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hWtop
  have hdim : Module.finrank (ZMod 2) W.toSubmodule = 1 :=
    finrank_span_singleton (b.ne_zero i)
  rw [he, finrank_top, hd] at hdim
  omega

/-- Every irreducible eight-dimensional binary action of SL₂(GF(8)) becomes
the actual triple Frobenius tensor after extension to GF(8). -/
theorem eight_irreducible_isTriple
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 8) : IsTriple ρ := by
  let K := GaloisField 2 3
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  have hcard : Nat.card K = 2 ^ 3 := GaloisField.card 2 3 (by decide)
  obtain ⟨_,_,_,hsdiv,_,_⟩ := Unsigned.exists_primeField_highestWeight_parameters
    2 ρ (eight_action_nontrivial ρ hd) 3 hcard
  have hdiv8 : Module.finrank (ZMod 2) E ∣ 8 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [ρ.asModuleEquiv.finrank_eq, hd] at ht
    exact ⟨_,ht.symm⟩
  have hdeg : Module.finrank (ZMod 2) E = 1 := by
    have hh := Nat.dvd_gcd hsdiv hdiv8
    norm_num at hh
    exact hh
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars F ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨n,⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 (extendScalars F ρ.endFieldRep)
  have hdim : Module.finrank E ρ.asModule = 8 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [hdeg, one_mul, ρ.asModuleEquiv.finrank_eq, hd] at ht
    exact ht
  have hw : Module.finrank F (highestWeightSpan e n.val).toSubmodule = 8 := by
    rw [← φ.toLinearEquiv.finrank_eq, Module.finrank_baseChange]
    exact hdim
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 (by decide) n.val 3 hcard
    (by simpa only [← hcard] using n.isLt)] at hw
  have hn : n.val < 8 := by simpa [hcard] using n.isLt
  have hn7 : n.val = 7 := by
    interval_cases h : n.val <;> norm_num [Fin.prod_univ_succ] at *
  apply isTriple_of_highestWeight_seven ρ (by simpa [hcard]) hdeg e
  rw [← hn7]
  exact ⟨φ⟩

end Representation.SL2.BinarySmall
