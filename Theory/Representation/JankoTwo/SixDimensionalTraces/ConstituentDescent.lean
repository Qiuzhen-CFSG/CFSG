module

public import Theory.Representation.JankoTwo.SixDimensionalTraces
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.ScalarDescent

/-!
# The degree-six trace comparison in the marked binary constituent

Apply absolute trace rigidity to a faithful six-dimensional constituent and
the actual scalar extension of the marked G₂(4) natural action. The resulting
identity or outer-involution marking discharges the character equality in
`MarkedEmbedding.exists_equiv_of_constituent_character`, giving a binary
representation equivalence with exactly that marking.

The trace and natural irreducibility premises are proved here. The source
assembly owner still supplies its actual constituent and injective intertwiner,
as well as inherited carrier simplicity. This is the constituent step of
Aschbacher--Smith K.4.5 (printed p.460), using the degree-six J₂ case of
Hiss--Malle corrected Table 2; it does not assert a binary degree bound.
-/

public section

namespace Sporadic.LeechRelated.J2.G2FourModule.MarkedEmbedding

open Representation
open scoped TensorProduct

universe u

/-- A faithful degree-six constituent gives a binary equivalence with the same
identity or outer-involution marking supplied by absolute trace rigidity. -/
theorem exists_equiv_of_six_dimensional_constituent [IsSimpleGroup Carrier]
    (d : MarkedEmbedding) {W E U : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    [Field E] [IsAlgClosed E] [AddCommGroup U] [Module E U]
    [FiniteDimensional E U]
    [Algebra F E] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) F E]
    (σ : Representation (ZMod 2) Carrier W) [IsIrreducible σ]
    (τ : Representation E Carrier U) (hτ : Function.Injective τ)
    (hdτ : Module.finrank E U = 6)
    (j : τ.IntertwiningMap (extendScalars E σ)) (hj : Function.Injective j) :
    ∃ a : MulAut Carrier, (a = 1 ∨ a = ExceptionalParabolics.involutionAut) ∧
      Nonempty (RepEquiv σ (d.innerRepresentation.comp a.toMonoidHom)) := by
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  let : IsIrreducible τ :=
    JankoTwo.SixDimensionalCertificate.LocalSpectra.isIrreducible_of_faithful_six τ hτ hdτ
  let : IsIrreducible d.innerRepresentation := d.innerRepresentation_irreducible
  have hf := (extendScalars_faithful_iff E d.fieldRepresentation).mp
    d.fieldRepresentation_injective
  have hd : Module.finrank E (E ⊗[F] V) = 6 := by
    simpa only [Module.finrank_baseChange] using Atlas.G2.Natural.finrank_space F
  obtain ⟨a, ha, htrace⟩ :=
    JankoTwo.SixDimensionalTraces.exists_character_eq_comp_one_or_involution
      τ (extendScalars E d.fieldRepresentation) hτ hf hdτ hd
  let : IsIrreducible (extendScalars E (d.fieldRepresentation.comp a.toMonoidHom)) :=
    d.fieldRepresentation_extendScalars_irreducible E a
  exact ⟨a, ha, d.exists_equiv_of_constituent_character σ a τ j hj htrace.symm⟩

end Sporadic.LeechRelated.J2.G2FourModule.MarkedEmbedding
