module

public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.FieldIdentification
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.ScalarTransport
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.TripleComparison

/-!
# Descent of the natural and triple-tensor rank-one comparisons

A binary irreducible representation whose Schur-field extension has pure
highest weight is the actual natural scalar restriction when the Schur field
has the defining field's order. The pure-power polynomial equivalence gives
its matrices over the algebraic closure. The compatible finite-field
identification brings those matrices into the Schur field, Noether--Deuring
descends the intertwiner, and restriction to the prime field gives the claimed
natural action.

For Schur degree one over a defining field of order eight, multiplication of
the pure-power factors of degrees one, two and four identifies the weight-seven
span with the actual triple Frobenius tensor. Transport through the two scalar
towers and Noether--Deuring descend that comparison to the defining field.
The field-identification module retains GF(8) and generation of its
automorphisms by the actual squaring map.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(6), (16),
printed pp.354,356--357; GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b).
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
namespace Representation.SL2.BinarySmall
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
local instance recognitionBinaryAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

private def schurRestrictionEquiv :
    ρ.Equiv (restrictScalars (k := ZMod 2) ρ.endFieldRep) := by
  refine Representation.Equiv.mk ρ.asModuleEquiv.symm ?_
  intro g
  apply LinearMap.ext
  intro v
  change ρ.asModuleEquiv.symm (ρ g v) =
    ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (ρ.asModuleEquiv.symm v)))
  rw [LinearEquiv.apply_symm_apply]

private theorem isNatural_of_schur_extension
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (hc : Nat.card K = Nat.card (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (h : Nonempty ((extendScalars
      (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
        (embeddedNatural e))) : IsNatural ρ := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  obtain ⟨c, hc⟩ := exists_fieldEquiv_comp_eq_of_card_eq e (algebraMap E F) hc
  have q := embeddedNaturalBaseChange (F := F) c.toRingHom
  rw [hc] at q
  obtain ⟨d⟩ := repEquiv_of_extendScalars ρ.endFieldRep (embeddedNatural c.toRingHom)
    ⟨RepEquiv.ofRepresentationEquiv (h.some.trans q.symm)⟩
  let ed : (restrictScalars (k := ZMod 2) ρ.endFieldRep).Equiv
      (restrictScalars (k := ZMod 2) (embeddedNatural c.toRingHom)) :=
    Representation.Equiv.mk (d.toLinearEquiv.restrictScalars (ZMod 2)) (fun g => by
      apply LinearMap.ext
      intro v
      exact d.isIntertwining g v)
  exact ⟨(schurRestrictionEquiv ρ).trans (ed.trans (naturalFieldEquiv c).symm)⟩

/-- A pure binary highest weight over the algebraic closure of the Schur field
recognizes the actual prime-field natural module when the Schur degree equals
the defining-field degree. -/
theorem isNatural_of_highestWeight_pow_two
    (n : ℕ) (_hn : 2 ≤ n) (hc : Nat.card K = 2 ^ n)
    (hs : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = n)
    (j : ℕ) (_hj : j < n)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (h : Nonempty ((extendScalars
      (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
        (highestWeightSpan e (2 ^ j)).toRepresentation)) : IsNatural ρ := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  have hcardE : Nat.card K = Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod, hs, hc]
  exact isNatural_of_schur_extension ρ ((iterateFrobenius F 2 j).comp e) hcardE
    ⟨h.some.trans (highestWeightPurePowerEquiv e j)⟩

/-- When the Schur field is the prime field, a polynomial-to-tensor comparison
in its algebraic closure descends to the actual tensor model over `K`. -/
theorem isTriple_of_highestWeight_seven_comparison
    (hs : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 1)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (h : Nonempty ((extendScalars
      (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
        (highestWeightSpan e 7).toRepresentation))
    (hcomparison : letI := e.toAlgebra
      Nonempty ((highestWeightSpan e 7).toRepresentation.Equiv
        (extendScalars (F := K) (V := TripleSpace K)
          (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
          (triple (K := K))))) : IsTriple ρ := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  -- Retain the canonical scalar action on the actual endomorphism field.
  let schurAlgebra : Algebra (ZMod 2) E := inferInstance
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra K F := e.toAlgebra
  let : Algebra (ZMod 2) E := schurAlgebra
  let qE := scalarTowerRepEquiv (S := E) (F := F) ρ
  let qK := scalarTowerRepEquiv (S := K) (F := F) ρ
  let qSchur := baseChangeRepEquiv (S := F) (schurOneBaseChangeEquiv ρ hs)
  let all := qK.trans (qE.symm.trans (qSchur.trans (h.some.trans hcomparison.some)))
  obtain ⟨d⟩ := repEquiv_of_extendScalars (F := K) (S := F) (W := TripleSpace K)
    (extendScalars K ρ) (triple (K := K))
    ⟨RepEquiv.ofRepresentationEquiv all⟩
  exact ⟨d.toRepresentationEquiv⟩

/-- Over a field of eight elements, highest weight seven and Schur degree one
recognize the actual triple Frobenius tensor after extension to the defining
field. The polynomial-to-tensor comparison is supplied by multiplication of
the three pure-power factors. -/
theorem isTriple_of_highestWeight_seven
    (hc : Nat.card K = 8)
    (hs : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 1)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (h : Nonempty ((extendScalars
      (AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
        (highestWeightSpan e 7).toRepresentation)) : IsTriple ρ := by
  apply isTriple_of_highestWeight_seven_comparison ρ hs e h
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra K F := e.toAlgebra
  exact ⟨highestWeightSevenTripleEquiv (K := K) (F := F) hc⟩

end
end Representation.SL2.BinarySmall
