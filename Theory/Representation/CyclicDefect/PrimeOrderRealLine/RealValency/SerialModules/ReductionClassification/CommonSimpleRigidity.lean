module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.CommonSimpleRigidity.Contracts
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Endpoint rigidity and the normalizer-length reduction

At an endpoint the incident simple already has the full dimension of the
ordinary vertex. Its embedding into any lattice reduction is an isomorphism.
This proves common-simple rigidity at every endpoint, in any characteristic
allowed by the tree, without a seriality or simple-socle hypothesis.

For the other vertices we separate two source obligations. `VertexNormalizerLengths`
requires the literal reductions to lie in the principal block and to have a
fixed normalizer length, either one or `p - 1`. The final theorem here is a
conditional assembly from this obligation and recognition at those two lengths.
Neither obligation is proved or installed as an instance in this module.

Source: Feit VII.2.9, VII.2.14, VII.2.19 and the first part of the proof of
VII.2.25, printed p.304. The lengths are those of the actual nonprojective
normalizer summands defined in `CommonSimpleRigidity.NormalizerLength`.
-/

public section
noncomputable section
open scoped Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {p m n : ℕ} {K G : Type*} [Field K] [Group G] [Finite G]
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}

/-- At any endpoint, every embedding of the unique incident simple is onto. -/
theorem incident_embedding_surjective_of_card_eq_one (hp : p ≠ 1)
    (hv : (t.incident v).card = 1) (X : OrdinaryLattice d v.val)
    (e : ↥(t.incident v)) (f : (t.rep e.val).IntertwiningMap (X.reduction r))
    (hf : Function.Injective f) : Function.Surjective f := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hv
  have he : e.val = a := by simpa [ha] using e.property
  have hdegree : X.degree = t.degree e.val := by
    calc
      X.degree = ∑ i ∈ t.incident v, t.degree i := lattice_degree_eq_incident_sum t hp v X
      _ = t.degree a := by rw [ha, Finset.sum_singleton]
      _ = t.degree e.val := congrArg t.degree he.symm
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) ?_).mp hf
  simp [hdegree]

/-- The common-simple uniqueness theorem is unconditional at every endpoint,
not only at degree-one vertices. -/
theorem commonSimpleRigidity_of_incident_card_eq_one (hp : p ≠ 1)
    (hv : (t.incident v).card = 1) : CommonSimpleRigidity t r v := by
  intro X Y _ _ e f hf g hg
  let ef := f.ofBijective ⟨hf, incident_embedding_surjective_of_card_eq_one hp hv X e f hf⟩
  let eg := g.ofBijective ⟨hg, incident_embedding_surjective_of_card_eq_one hp hv Y e g hg⟩
  exact ⟨ef.symm.trans eg⟩

/-- Conditional assembly of the reduced part of VII.2.25. The second premise
is a theorem about arbitrary principal-block modules of extremal normalizer
length, independent of integral lattices and ordinary vertices. -/
theorem commonSimpleRigidity_of_normalizerLengths (P : Sylow p G)
    (hlength : VertexNormalizerLengths r P v)
    (hrecognition : ∀ (a b s l : ℕ)
      (ρ : Representation K G (Fin a → K))
      (σ : Representation K G (Fin b → K))
      (τ : Representation K G (Fin s → K)),
      (l = 1 ∨ l = p - 1) →
      Module.IsIndecomposable (MonoidAlgebra K G) ρ.asModule →
      Module.IsIndecomposable (MonoidAlgebra K G) σ.asModule →
      ρ.asAlgebraHom (ModuleTree.reducedPrincipal d r.residue) = 1 →
      σ.asAlgebraHom (ModuleTree.reducedPrincipal d r.residue) = 1 →
      HasNormalizerLength P ρ l → HasNormalizerLength P σ l →
      IsIrreducible τ →
      ∀ f : τ.IntertwiningMap ρ, Function.Injective f →
      ∀ g : τ.IntertwiningMap σ, Function.Injective g → Nonempty (ρ.Equiv σ)) :
    CommonSimpleRigidity t r v := by
  obtain ⟨l, hl, hvertex⟩ := hlength
  intro X Y hX hY e f hf g hg
  obtain ⟨hXB, hXL⟩ := hvertex X hX
  obtain ⟨hYB, hYL⟩ := hvertex Y hY
  exact hrecognition X.degree Y.degree (t.degree e.val) l
    (X.reduction r) (Y.reduction r) (t.rep e.val) hl hX hY hXB hYB hXL hYL
    (t.irreducible e.val) f hf g hg

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
