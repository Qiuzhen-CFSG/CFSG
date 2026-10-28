module

public import Theory.GroupTheory.FixedElementaryTransport
public import Theory.Representation.GroupEquivalence
public import Theory.Representation.Triality.BinaryDegree.TensorDescent
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RootComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Transport to the genuine binary triality carrier

The canonical map from the elementary Geck graph-field fixed group to
`Standard.BinaryCarrier` is an isomorphism in characteristic two, by the
proved elementary-center calculation. Thus faithful irreducibles correspond
on the same vector space, including at q = 2.

For a separate split-group construction we provide two conditional routes.
An isomorphism intertwining the graph-field actions induces an isomorphism
of the elementary central quotients. Alternatively, an equivariant embedding
of the standard split group suffices if its image contains every fixed point
of the target action; this accommodates a target over an algebraic closure.
If a representation theorem uses the entire fixed subgroup, its equality with
the p-generated subgroup also has to be established.

Surjective pullback preserves the character values and their Frobenius
periods. Consequently `TensorData` transports without changing its weights,
factor degrees or finrank formula. The classification-transfer theorems give
the precise premise used by `triality_binary_degree_ge_of_tensor_classification`
in `Theory.Representation.Triality.BinaryDegree`.

For the concrete Clifford Spin carrier, `CarrierTransport.FiniteField` proves
coordinate descent over the actual cubic field. `RootComparison` derives the
graph-field compatibility and image from literal signed-simple-root equations.
`GeckSpin` constructs that faithful comparison and `RationalGeneration` proves
generation over the cubic field. Thus `Standard.binarySpinCarrierEquiv` identifies
the actual Clifford Spin elementary central quotient with `BinaryCarrier`
unconditionally, including n = 1. Its fixed-group and elementary-group
comparisons respect the ambient inclusion and the literal central quotient maps.
The representation equivalence preserves the vector space, irreducibility,
faithfulness, finrank and tensor data. Only the representation-classification
input remains explicit in `tensorClassification_of_spin`.

Sources: GLS3 §§2.2 and 2.8 (`refs/KGroup/GLS3/chapter2.tex`), and
Aschbacher–Smith, printed p.356 (PDF p.367, `refs/quasithin.pdf`).
-/

@[expose] public section

namespace Triality.Standard

open Theory.GroupTheory

variable {U : Type*} [Group U]

/-- Transport an actual split-group comparison through fixed points,
p-generation and the quotient by the elementary group’s own center. -/
noncomputable def carrierEquivOfIntertwining (P : Parameters) (σ : U ≃* U)
    (e : U ≃* SplitGroup P) (he : ∀ g, e (σ g) = graphFieldAutomorphism P (e g)) :
    FixedElementary.Carrier P.prime σ ≃* Carrier P :=
  FixedElementary.carrierEquiv P.prime σ (graphFieldAutomorphism P) e he

/-- A comparison with an ambient group over a larger field only requires
an embedding and coverage of all graph-field fixed points. -/
noncomputable def carrierEquivOfEmbedding (P : Parameters) (σ : U ≃* U)
    (f : SplitGroup P →* U) (hf : Function.Injective f)
    (he : ∀ g, f (graphFieldAutomorphism P g) = σ (f g))
    (hfixed : ∀ u, σ u = u → ∃ g, f g = u) :
    Carrier P ≃* FixedElementary.Carrier P.prime σ :=
  FixedElementary.carrierEquivOfEmbedding P.prime (graphFieldAutomorphism P) σ
    f hf he hfixed

/-- The actual elementary-to-carrier quotient is an isomorphism for every
positive binary exponent. Its injectivity uses the proved center calculation. -/
noncomputable def binaryElementaryEquiv (n : ℕ) (hn : 0 < n) :
    ElementaryGroup (binaryParameters n hn) ≃* BinaryCarrier n hn :=
  MulEquiv.ofBijective (toCarrier (binaryParameters n hn))
    ⟨ElementaryCentralKernel.toCarrier_injective _ rfl, toCarrier_surjective _⟩

@[simp] theorem binaryElementaryEquiv_apply (n : ℕ) (hn : 0 < n)
    (g : ElementaryGroup (binaryParameters n hn)) :
    binaryElementaryEquiv n hn g = toCarrier (binaryParameters n hn) g := rfl

/-- Assemble the genuine carriers from a faithful literal root comparison and
rational Spin root generation. Both remaining mathematical inputs are explicit. -/
noncomputable def binarySpinCarrierEquivOfRootFormula
    {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2] {n : ℕ} {hn : 0 < n}
    (f : ExtensionField (binaryParameters n hn) →+* k)
    (e : SplitGroup (binaryParameters n hn) →* SimplyConnected.Points k)
    (hf : Function.Injective e)
    (he : BinaryDegree.CarrierTransport.HasRootFormula f e)
    (hgen : ∀ g : SimplyConnected.Points k,
      (∀ i j, SimplyConnected.naturalMatrix k g i j ∈ f.range) →
        g ∈ BinaryDegree.CarrierTransport.rationalSimpleSubgroup f) :
    BinaryCarrier n hn ≃* SimplyConnected.GraphField.Carrier k n :=
  carrierEquivOfEmbedding (binaryParameters n hn) (SimplyConnected.GraphField.sigma k n)
    e hf he.graphField_intertwines (he.fixed_coverage hgen)

section ConcreteSpin

open BinaryDegree.CarrierTransport

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Identify the actual finite Geck and algebraic-closure Spin fixed groups.
The cubic Frobenius formula and rational root generation supply surjectivity. -/
noncomputable def binarySpinFixedEquiv (n : ℕ) (hn : 0 < n) :
    fixedSubgroup (binaryParameters n hn) ≃* SimplyConnected.GraphField.FixedGroup k n :=
  FixedElementary.fixedEquivOfEmbedding (graphFieldAutomorphism (binaryParameters n hn))
    (SimplyConnected.GraphField.sigma k n)
    (GeckSpin.finiteComparison k (coefficientEmbedding k n hn))
    (GeckSpin.finiteComparison_injective k (coefficientEmbedding k n hn))
    (GeckSpin.finiteComparison_graphField k (coefficientEmbedding k n hn))
    ((GeckSpin.finiteComparison_hasRootFormula k (coefficientEmbedding k n hn)).fixed_coverage
      (rational_generation (coefficientEmbedding k n hn)))

/-- The fixed-group comparison is the literal faithful Geck-to-Spin root map. -/
@[simp] theorem binarySpinFixedEquiv_apply_val (n : ℕ) (hn : 0 < n)
    (g : fixedSubgroup (binaryParameters n hn)) :
    (binarySpinFixedEquiv k n hn g).val =
      GeckSpin.finiteComparison k (coefficientEmbedding k n hn) g.val := rfl

/-- Restrict the fixed-group comparison to the subgroups generated by two-elements. -/
noncomputable def binarySpinElementaryEquiv (n : ℕ) (hn : 0 < n) :
    ElementaryGroup (binaryParameters n hn) ≃* SimplyConnected.GraphField.ElementaryGroup k n :=
  FixedElementary.elementaryEquivOfFixedEquiv 2
    (graphFieldAutomorphism (binaryParameters n hn)) (SimplyConnected.GraphField.sigma k n)
    (binarySpinFixedEquiv k n hn)

/-- The elementary comparison preserves the inclusion into the actual Spin points. -/
@[simp] theorem binarySpinElementaryEquiv_apply_val (n : ℕ) (hn : 0 < n)
    (g : ElementaryGroup (binaryParameters n hn)) :
    SimplyConnected.GraphField.elementaryInclusion k n (binarySpinElementaryEquiv k n hn g) =
      GeckSpin.finiteComparison k (coefficientEmbedding k n hn) g.val.val := rfl

/-- Unconditional comparison with the genuine binary triality carrier, for every
positive exponent, including n = 1. Both quotients use the elementary group’s
own center; no identification with the whole fixed group is assumed. -/
noncomputable def binarySpinCarrierEquiv (n : ℕ) (hn : 0 < n) :
    BinaryCarrier n hn ≃* SimplyConnected.GraphField.Carrier k n :=
  binarySpinCarrierEquivOfRootFormula (coefficientEmbedding k n hn)
    (GeckSpin.finiteComparison k (coefficientEmbedding k n hn))
    (GeckSpin.finiteComparison_injective k (coefficientEmbedding k n hn))
    (GeckSpin.finiteComparison_hasRootFormula k (coefficientEmbedding k n hn))
    (rational_generation (coefficientEmbedding k n hn))

/-- The concrete comparison commutes with the literal central quotient maps. -/
@[simp] theorem binarySpinCarrierEquiv_toCarrier (n : ℕ) (hn : 0 < n)
    (g : ElementaryGroup (binaryParameters n hn)) :
    binarySpinCarrierEquiv k n hn (toCarrier (binaryParameters n hn) g) =
      SimplyConnected.GraphField.toCarrier k n (binarySpinElementaryEquiv k n hn g) := rfl


end ConcreteSpin

end Triality.Standard

namespace Triality.BinaryDegree

open Theory.GroupTheory

variable {F G H W : Type*} [Field F] [Group G] [Group H]
    [AddCommGroup W] [Module F W]

/-- Inflate the tensor parameters along a surjection, preserving the exact
character-period equivalence as well as the dimension formula. -/
noncomputable def TensorData.comp_surjective {n : ℕ} {σ : Representation F H W}
    (h : TensorData n σ) (π : G →* H) (hπ : Function.Surjective π) :
    TensorData n (σ.comp π) where
  weight := h.weight
  factorDegree := h.factorDegree
  factor_pos := h.factor_pos
  trivial_degree := h.trivial_degree
  nontrivial_factor := h.nontrivial_factor
  nontrivial_degree := h.nontrivial_degree
  fixed_degree := h.fixed_degree
  diagram_degree := h.diagram_degree
  twisted_period := h.twisted_period
  finrank_eq := h.finrank_eq
  character_period r := by
    change (∀ g, σ.character (π g) ^ (2 ^ r) = σ.character (π g)) ↔ _
    rw [← h.character_period r]
    exact (hπ.forall (p := fun g => σ.character g ^ (2 ^ r) = σ.character g)).symm

/-- Descend tensor parameters from a surjective pullback of the given action. -/
noncomputable def TensorData.of_comp_surjective {n : ℕ} {σ : Representation F H W}
    (π : G →* H) (hπ : Function.Surjective π) (h : TensorData n (σ.comp π)) :
    TensorData n σ where
  weight := h.weight
  factorDegree := h.factorDegree
  factor_pos := h.factor_pos
  trivial_degree := h.trivial_degree
  nontrivial_factor := h.nontrivial_factor
  nontrivial_degree := h.nontrivial_degree
  fixed_degree := h.fixed_degree
  diagram_degree := h.diagram_degree
  twisted_period := h.twisted_period
  finrank_eq := h.finrank_eq
  character_period r := by
    rw [← h.character_period r]
    change _ ↔ (∀ g, σ.character (π g) ^ (2 ^ r) = σ.character (π g))
    exact (hπ.forall (p := fun g => σ.character g ^ (2 ^ r) = σ.character g))

/-- Faithful irreducibles of the genuine binary carrier and its elementary
fixed group correspond on the same field and vector space. -/
noncomputable def binaryFaithfulIrreducibleEquiv (n : ℕ) (hn : 0 < n) :
    {ρ : Representation F (Standard.BinaryCarrier n hn) W //
      ρ.IsIrreducible ∧ Function.Injective ρ} ≃
    {σ : Representation F (Standard.ElementaryGroup (Standard.binaryParameters n hn)) W //
      σ.IsIrreducible ∧ Function.Injective σ} :=
  Representation.faithfulIrreducibleGroupEquivalence (Standard.binaryElementaryEquiv n hn)

/-- The binary carrier and the elementary fixed group have exactly the
same faithful-irreducible degree bounds. -/
theorem binary_degree_bound_iff_elementary (n : ℕ) (hn : 0 < n) (d : ℕ) :
    (∀ ρ : Representation F (Standard.BinaryCarrier n hn) W,
      ρ.IsIrreducible → Function.Injective ρ → d ≤ Module.finrank F W) ↔
    (∀ σ : Representation F (Standard.ElementaryGroup (Standard.binaryParameters n hn)) W,
      σ.IsIrreducible → Function.Injective σ → d ≤ Module.finrank F W) :=
  (Representation.forall_faithful_irreducible_finrank_ge_iff
    (Standard.binaryElementaryEquiv n hn) d).symm

/-- Classification on the genuine elementary group supplies the exact
carrier classification premise required for binary descent. -/
theorem tensorClassification_of_elementary {n : ℕ} (hn : 0 < n)
    (hclassification : ∀
      σ : Representation F (Standard.ElementaryGroup (Standard.binaryParameters n hn)) W,
      σ.IsIrreducible → Function.Injective σ → Nonempty (TensorData n σ))
    (ρ : Representation F (Standard.BinaryCarrier n hn) W)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) : Nonempty (TensorData n ρ) := by
  let e := Standard.binaryElementaryEquiv n hn
  have hi' := (Representation.irreducible_comp_surjective_iff e.toMonoidHom e.surjective ρ).mpr hi
  have hf' := (Representation.injective_comp_mulEquiv_iff e ρ).mpr hf
  obtain ⟨h⟩ := hclassification (ρ.comp e.toMonoidHom) hi' hf'
  exact ⟨h.of_comp_surjective e.toMonoidHom e.surjective⟩

/-- A compatible split-group isomorphism transfers a proved tensor
classification to the exact binary carrier. -/
theorem tensorClassification_of_splitEquiv {n : ℕ} (hn : 0 < n)
    {U : Type*} [Group U] (σ : U ≃* U)
    (e : U ≃* Standard.SplitGroup (Standard.binaryParameters n hn))
    (he : ∀ g, e (σ g) = Standard.graphFieldAutomorphism (Standard.binaryParameters n hn) (e g))
    (hclassification : ∀ ρ : Representation F (FixedElementary.Carrier 2 σ) W,
      ρ.IsIrreducible → Function.Injective ρ → Nonempty (TensorData n ρ))
    (ρ : Representation F (Standard.BinaryCarrier n hn) W)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) : Nonempty (TensorData n ρ) := by
  let eC := Standard.carrierEquivOfIntertwining (Standard.binaryParameters n hn) σ e he
  have hi' := (Representation.irreducible_comp_surjective_iff
    eC.toMonoidHom eC.surjective ρ).mpr hi
  have hf' := (Representation.injective_comp_mulEquiv_iff eC ρ).mpr hf
  obtain ⟨h⟩ := hclassification (ρ.comp eC.toMonoidHom) hi' hf'
  exact ⟨h.of_comp_surjective eC.toMonoidHom eC.surjective⟩

/-- The same transfer when the source of the representation theorem is
constructed in a larger ambient group, with all its fixed points in the image. -/
theorem tensorClassification_of_splitEmbedding {n : ℕ} (hn : 0 < n)
    {U : Type*} [Group U] (σ : U ≃* U)
    (f : Standard.SplitGroup (Standard.binaryParameters n hn) →* U)
    (hf : Function.Injective f)
    (he : ∀ g, f (Standard.graphFieldAutomorphism (Standard.binaryParameters n hn) g) = σ (f g))
    (hfixed : ∀ u, σ u = u → ∃ g, f g = u)
    (hclassification : ∀ ρ : Representation F (FixedElementary.Carrier 2 σ) W,
      ρ.IsIrreducible → Function.Injective ρ → Nonempty (TensorData n ρ))
    (ρ : Representation F (Standard.BinaryCarrier n hn) W)
    (hi : ρ.IsIrreducible) (hρ : Function.Injective ρ) : Nonempty (TensorData n ρ) := by
  let eC := (Standard.carrierEquivOfEmbedding (Standard.binaryParameters n hn) σ
    f hf he hfixed).symm
  have hi' := (Representation.irreducible_comp_surjective_iff
    eC.toMonoidHom eC.surjective ρ).mpr hi
  have hf' := (Representation.injective_comp_mulEquiv_iff eC ρ).mpr hρ
  obtain ⟨h⟩ := hclassification (ρ.comp eC.toMonoidHom) hi' hf'
  exact ⟨h.of_comp_surjective eC.toMonoidHom eC.surjective⟩

/-- Faithful irreducibles correspond on the same vector space once the two
explicit concrete comparison premises are supplied. -/
noncomputable def spinFaithfulIrreducibleEquivOfRootFormula
    {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2] {n : ℕ} {hn : 0 < n}
    (f : Standard.ExtensionField (Standard.binaryParameters n hn) →+* k)
    (e : Standard.SplitGroup (Standard.binaryParameters n hn) →* SimplyConnected.Points k)
    (hf : Function.Injective e) (he : CarrierTransport.HasRootFormula f e)
    (hgen : ∀ g : SimplyConnected.Points k,
      (∀ i j, SimplyConnected.naturalMatrix k g i j ∈ f.range) →
        g ∈ CarrierTransport.rationalSimpleSubgroup f) :
    {ρ : Representation F (Standard.BinaryCarrier n hn) W //
      ρ.IsIrreducible ∧ Function.Injective ρ} ≃
    {σ : Representation F (SimplyConnected.GraphField.Carrier k n) W //
      σ.IsIrreducible ∧ Function.Injective σ} :=
  Representation.faithfulIrreducibleGroupEquivalence
    (Standard.binarySpinCarrierEquivOfRootFormula f e hf he hgen).symm

/-- The actual Spin classification transfers to `BinaryCarrier` without changing
tensor data, provided the root comparison and rational generation are proved. -/
theorem tensorClassification_of_spin_rootFormula
    {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2] {n : ℕ} {hn : 0 < n}
    (f : Standard.ExtensionField (Standard.binaryParameters n hn) →+* k)
    (e : Standard.SplitGroup (Standard.binaryParameters n hn) →* SimplyConnected.Points k)
    (hf : Function.Injective e) (he : CarrierTransport.HasRootFormula f e)
    (hgen : ∀ g : SimplyConnected.Points k,
      (∀ i j, SimplyConnected.naturalMatrix k g i j ∈ f.range) →
        g ∈ CarrierTransport.rationalSimpleSubgroup f)
    (hclassification : ∀ σ : Representation F (SimplyConnected.GraphField.Carrier k n) W,
      σ.IsIrreducible → Function.Injective σ → Nonempty (TensorData n σ))
    (ρ : Representation F (Standard.BinaryCarrier n hn) W)
    (hi : ρ.IsIrreducible) (hρ : Function.Injective ρ) : Nonempty (TensorData n ρ) :=
  tensorClassification_of_splitEmbedding hn (SimplyConnected.GraphField.sigma k n)
    e hf he.graphField_intertwines (he.fixed_coverage hgen) hclassification ρ hi hρ

section ConcreteSpin

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Change from the genuine carrier to the Spin central quotient on the same
field and vector space; in particular, finrank is unchanged. -/
noncomputable def spinRepresentationEquiv (n : ℕ) (hn : 0 < n) :
    Representation F (Standard.BinaryCarrier n hn) W ≃
      Representation F (SimplyConnected.GraphField.Carrier k n) W :=
  Representation.groupEquivalence (Standard.binarySpinCarrierEquiv k n hn).symm

/-- The unconditional faithful-irreducible correspondence for the concrete
Spin and Geck carriers, on the same vector space. -/
noncomputable def spinFaithfulIrreducibleEquiv (n : ℕ) (hn : 0 < n) :
    {ρ : Representation F (Standard.BinaryCarrier n hn) W //
      ρ.IsIrreducible ∧ Function.Injective ρ} ≃
    {σ : Representation F (SimplyConnected.GraphField.Carrier k n) W //
      σ.IsIrreducible ∧ Function.Injective σ} :=
  Representation.faithfulIrreducibleGroupEquivalence (Standard.binarySpinCarrierEquiv k n hn).symm

/-- Every faithful-irreducible degree bound on the concrete Spin quotient
holds on the exact binary carrier, and conversely. -/
theorem spin_degree_bound_iff (n : ℕ) (hn : 0 < n) (d : ℕ) :
    (∀ ρ : Representation F (Standard.BinaryCarrier n hn) W,
      ρ.IsIrreducible → Function.Injective ρ → d ≤ Module.finrank F W) ↔
    (∀ σ : Representation F (SimplyConnected.GraphField.Carrier k n) W,
      σ.IsIrreducible → Function.Injective σ → d ≤ Module.finrank F W) :=
  Representation.forall_faithful_irreducible_finrank_ge_iff
    (Standard.binarySpinCarrierEquiv k n hn) d

/-- Transport preserves the tensor weights, degrees and exact character periods. -/
theorem tensorData_spin_iff (n : ℕ) (hn : 0 < n)
    (ρ : Representation F (Standard.BinaryCarrier n hn) W) :
    Nonempty (TensorData n (spinRepresentationEquiv k n hn ρ)) ↔
      Nonempty (TensorData n ρ) := by
  let e := (Standard.binarySpinCarrierEquiv k n hn).symm
  constructor
  · rintro ⟨h⟩
    exact ⟨h.of_comp_surjective e.toMonoidHom e.surjective⟩
  · rintro ⟨h⟩
    exact ⟨h.comp_surjective e.toMonoidHom e.surjective⟩

/-- A tensor classification on the actual Spin elementary central quotient
supplies the existing binary degree theorem’s precise input. The concrete
group comparison is fully discharged; only the classification is assumed. -/
theorem tensorClassification_of_spin {n : ℕ} (hn : 0 < n)
    (hclassification : ∀ σ : Representation F (SimplyConnected.GraphField.Carrier k n) W,
      σ.IsIrreducible → Function.Injective σ → Nonempty (TensorData n σ))
    (ρ : Representation F (Standard.BinaryCarrier n hn) W)
    (hi : ρ.IsIrreducible) (hρ : Function.Injective ρ) : Nonempty (TensorData n ρ) := by
  let σ := spinFaithfulIrreducibleEquiv k n hn ⟨ρ, hi, hρ⟩
  exact (tensorData_spin_iff k n hn ρ).mp
    (hclassification σ.val σ.property.1 σ.property.2)


end ConcreteSpin

end Triality.BinaryDegree
