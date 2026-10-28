module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Contracts
public import Theory.Representation.KrullSchmidt
public import Theory.Representation.SubrepresentationLattice

/-!
# Preparations for classifying indecomposable vertex reductions

An exhaustive series makes a nonzero representation indecomposable. Its first
factor embeds in the original representation, so the supplied vertex series
contains its designated simple edge. Two lattices with the same ordinary
character also have the same modular trace character at the actual residue map.
This last assertion is equality of field-valued traces, not a claim that equal
traces determine arbitrary modular representations.

`SimpleSupport` and `CommonSimpleRigidity` separate the remaining source steps.
The first identifies an arbitrary simple submodule with an incident edge. The
second is the reduced-module uniqueness argument on Feit VII.2.25, printed
p.304: the Green-correspondent length is fixed by the ordinary vertex, and a
common embedded simple determines the module. Neither proposition has an
existence instance or a proof in this preparation module. In particular, an
arbitrary indecomposable reduction is not assumed to be serial.

Source: Feit, *The Representation Theory of Finite Groups*, VII.2.19--20,
VII.2.25 and its proof on pp.304--305. Only the reduced-module part of VII.2.25
is needed; the later integral lifting of an isomorphism is not used here.
-/

public section
noncomputable section
open scoped Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    {ρ : Representation K G V} {s : ℕ}

/-- Exhaustivity rules out two nonzero complementary group-algebra submodules. -/
theorem series_isIndecomposable (c : ExhaustiveSeries ρ s) [Nontrivial V] :
    Module.IsIndecomposable (MonoidAlgebra K G) ρ.asModule := by
  refine ⟨ρ.asModuleEquiv.symm.injective.nontrivial, ?_⟩
  intro P Q hPQ
  let f := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  rcases c.no_nontrivial_complement (f.symm P) (f.symm Q)
    (f.symm.isCompl_iff.mp hPQ) with hP | hQ
  · left
    simpa using congrArg f hP
  · right
    simpa using congrArg f hQ

private theorem firstFactor_embedding (c : ExhaustiveSeries ρ s) (hs : 0 < s) :
    ∃ f : (c.factor ⟨0, hs⟩).IntertwiningMap ρ, Function.Injective f := by
  let i : Fin s := ⟨0, hs⟩
  let U := c.term i.succ
  let B := inside (c.term i.castSucc) U
  have hB : B.toSubmodule = ⊥ := by
    simp [B, U, i, inside, show (⟨0, Nat.lt_succ_of_lt hs⟩ : Fin (s + 1)) = 0 from rfl]
    exact Submodule.ker_subtype _
  let q : U.toRepresentation.IntertwiningMap (c.factor i) := {
    toLinearMap := B.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  have hq : Function.Bijective q :=
    ⟨LinearMap.ker_eq_bot.mp ((Submodule.ker_mkQ _).trans hB),
      Submodule.mkQ_surjective _⟩
  let j : U.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := U.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  exact ⟨j.comp (q.ofBijective hq).symm.toIntertwiningMap,
    Subtype.val_injective.comp (q.ofBijective hq).symm.injective⟩

variable {p m n : ℕ} [Finite G]
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}


/-- Every member of the supplied vertex family is genuinely indecomposable.
Positivity comes from its nonzero designated simple edge. -/
theorem vertex_reduction_isIndecomposable (a : VertexSeries t r v)
    (hp : p ≠ 1) (e : ↥(t.incident v)) :
    Module.IsIndecomposable (MonoidAlgebra K G) ((a.lattice e).reduction r).asModule := by
  have hdeg : 0 < (a.lattice e).degree := by
    rw [lattice_degree_eq_incident_sum t hp v]
    exact lt_of_lt_of_le (t.degree_pos e.val)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) e.property)
  let : Nonempty (Fin (a.lattice e).degree) := ⟨⟨0, hdeg⟩⟩
  exact series_isIndecomposable (a.series e)

/-- The designated edge embeds through the literal first quotient in the series. -/
theorem vertex_edge_embedding (a : VertexSeries t r v) (e : ↥(t.incident v)) :
    ∃ f : (t.rep e.val).IntertwiningMap ((a.lattice e).reduction r),
      Function.Injective f := by
  have hs : 0 < (t.incident v).card := Finset.card_pos.mpr ⟨e.val, e.property⟩
  obtain ⟨f, hf⟩ := firstFactor_embedding (a.series e) hs
  obtain ⟨q⟩ := a.factor_equiv e ⟨0, hs⟩
  rw [a.first e hs] at q
  exact ⟨f.comp q.symm.toIntertwiningMap, hf.comp q.symm.injective⟩

/-- Equality of ordinary characters survives reduction as equality of traces. -/
theorem reduction_character_eq (X Y : OrdinaryLattice d v.val) :
    (X.reduction r).character = (Y.reduction r).character := by
  funext g
  change LinearMap.trace K _ (mapCoefficients r.residue X.rep g) =
    LinearMap.trace K _ (mapCoefficients r.residue Y.rep g)
  rw [mapCoefficients_trace, mapCoefficients_trace]
  congr 1
  apply ModularBlock.PrimeIntegralModels.localizationToComplex_injective d.primeIdeal
  rw [← mapCoefficients_trace, ← mapCoefficients_trace]
  have h := congrFun (X.character_eq.symm.trans Y.character_eq) (ConjClasses.mk g)
  exact h

/-- A nonzero finite-dimensional reduction contains an actual simple submodule. -/
theorem exists_simple_submodule (X : OrdinaryLattice d v.val)
    (hX : Module.IsIndecomposable (MonoidAlgebra K G) (X.reduction r).asModule) :
    ∃ U : Subrepresentation (X.reduction r), IsIrreducible U.toRepresentation := by
  let : Nontrivial (X.reduction r).asModule := hX.1
  let : Nontrivial (Fin X.degree → K) := (X.reduction r).asModuleEquiv.injective.nontrivial
  exact Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (X.reduction r)


/-- Every simple submodule of an ordinary lattice reduction is an incident
edge. This is a constituent-support obligation, not an assumed simple socle. -/
@[expose] def SimpleSupport (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) : Prop :=
  ∀ (X : OrdinaryLattice d v.val) (U : Subrepresentation (X.reduction r)),
    IsIrreducible U.toRepresentation →
      ∃ e : ↥(t.incident v), Nonempty (U.toRepresentation.Equiv (t.rep e.val))

/-- The uniqueness step in the reduced-module part of VII.2.25. Both modules
are reductions of actual lattices with the same ordinary character. Only an
embedded simple is specified; neither module is assumed to have simple socle. -/
@[expose] def CommonSimpleRigidity (t : Tree d.chi d.block p n L)
    (r : CompatibleRoots d K m) (v : {i // i ∈ d.block}) : Prop :=
  ∀ X Y : OrdinaryLattice d v.val,
    Module.IsIndecomposable (MonoidAlgebra K G) (X.reduction r).asModule →
    Module.IsIndecomposable (MonoidAlgebra K G) (Y.reduction r).asModule →
    ∀ (e : ↥(t.incident v))
      (f : (t.rep e.val).IntertwiningMap (X.reduction r)), Function.Injective f →
      ∀ (g : (t.rep e.val).IntertwiningMap (Y.reduction r)), Function.Injective g →
        Nonempty ((X.reduction r).Equiv (Y.reduction r))

/-- Finite dimensionality supplies a simple submodule; constituent support
then gives an actual injection of an incident edge into the arbitrary reduction. -/
theorem exists_incident_simple_embedding_of_support (hs : SimpleSupport t r v)
    (X : OrdinaryLattice d v.val)
    (hX : Module.IsIndecomposable (MonoidAlgebra K G) (X.reduction r).asModule) :
    ∃ (e : ↥(t.incident v))
      (f : (t.rep e.val).IntertwiningMap (X.reduction r)), Function.Injective f := by
  obtain ⟨U, hU⟩ := exists_simple_submodule X hX
  obtain ⟨e, ⟨q⟩⟩ := hs X U hU
  let j : U.toRepresentation.IntertwiningMap (X.reduction r) := {
    toLinearMap := U.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  exact ⟨e, j.comp q.symm.toIntertwiningMap, Subtype.val_injective.comp q.symm.injective⟩

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
