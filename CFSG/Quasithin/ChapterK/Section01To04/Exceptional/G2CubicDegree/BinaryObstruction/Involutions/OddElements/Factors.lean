module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Transport

/-!
# Concrete odd-displacement obligations on the binary G₂ flag factors

The two vertex flags use free-group coordinates marked into the actual derived
G₂ group. Their degree-14 quotients, and the half and quotient of the incidence
kernel in degree 32, are the only concrete calculations still required.
The checked flags and incidence map transport these calculations to every
irreducible quotient of the 189-dimensional permutation module.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11. The degree-32 branch extends the calculation beyond the source's
prior offender-based degree exclusion and is retained explicitly.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Representation Representation.BinaryOffender
open G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- The actual quotient vector space at a step of the checked vertex flag. -/
abbrev VertexFactorSpace (i : Fin 2) (t : Factor i) :=
  ((adaptedFlagCoordinates i).stage (t.val + 1)).toSubmodule ⧸
    (within ((adaptedFlagCoordinates i).stage t.val)
      ((adaptedFlagCoordinates i).stage (t.val + 1))).toSubmodule

/-- The literal quotient representation, retaining its root-word marking. -/
abbrev vertexFactorRepresentation (i : Fin 2) (t : Factor i) :
    Representation (ZMod 2) WordGroup (VertexFactorSpace i t) :=
  (within ((adaptedFlagCoordinates i).stage t.val)
    ((adaptedFlagCoordinates i).stage (t.val + 1))).quotientRepresentation

/-- The finite vertex calculation, restricted precisely to degree fourteen. -/
def VertexBounds : Prop :=
  ∀ (i : Fin 2) (t : Factor i), degree i t = 14 →
    MarkedBounds groupHom (vertexFactorRepresentation i t)

/-- Both literal simple factors of the incidence cycle space must be covered. -/
structure CycleBounds : Prop where
  half : MarkedBounds (V := cycleCoordinates.half.toSubmodule) (MonoidHom.id Derived)
    cycleCoordinates.half.toRepresentation
  quotient : MarkedBounds
    (V := cycleSubrepresentation.toSubmodule ⧸ cycleCoordinates.half.toSubmodule)
    (MonoidHom.id Derived)
    cycleCoordinates.half.quotientRepresentation

/-- The concrete degree-fourteen bounds suffice for every coordinate-flag factor
above degree eight. The other factors have degree one or six. -/
theorem coordinate_boundedFactors (h : VertexBounds) (i : Fin 2) :
    BoundedFactors groupHom (representation i) := by
  let C := adaptedFlagCoordinates i
  apply BoundedFactors.of_flag groupHom (length i) C.stage C.zero C.last C.mono
  · intro m hm
    exact adaptedFlag_quotient_irreducible i ⟨m, hm⟩
  · intro m hm hd
    let t : Factor i := ⟨m, hm⟩
    have ht : 8 < degree i t := by
      rw [← adaptedFlag_quotient_finrank i t]
      exact hd
    have hdegree := (by decide +kernel :
      ∀ i (t : Factor i), degree i t = 1 ∨ degree i t = 6 ∨ degree i t = 14) i t
    exact h i t (by omega)

/-- Surjectivity of the root-word marking makes the bounds valid for the whole
actual derived group, with the same cyclic fixed spaces. -/
theorem vertex_boundedFactors (h : VertexBounds) (i : Fin 2) :
    BoundedFactors (MonoidHom.id Derived) (vertexRepresentation i) := by
  let e : Fin 63 ≃ Vertex i := Equiv.ofBijective (vertex i) (vertex_bijective i)
  let el : Space ≃ₗ[ZMod 2] BinaryPermutation.Full (Vertex i) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  apply BoundedFactors.transport (MonoidHom.id Derived) groupHom groupHom_surjective
    (coordinate_boundedFactors h i) (vertexRepresentation i) el
  intro g v
  ext y
  change v ((wordPerm i g).symm (e.symm y)) =
    v (e.symm ((vertexPerm i (groupHom g)).symm y))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply]
  apply (vertexPerm i (groupHom g)).injective
  rw [Equiv.apply_symm_apply, ← vertex_word_equivariance i e
    (fun j x => vertex_generator_action i j x), Equiv.apply_symm_apply,
    e.apply_symm_apply]

private theorem boundedFactors_simple {G V : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] (π : G →* Derived)
    (ρ : Representation (ZMod 2) G V) (hs : IsIrreducible ρ)
    (hb : MarkedBounds π ρ) : BoundedFactors π ρ := by
  let S : Subrepresentation ρ := ⊥
  let e : (V ⧸ S.toSubmodule) ≃ₗ[ZMod 2] V := S.toSubmodule.quotEquivOfEqBot rfl
  let E : Representation.RepEquiv S.quotientRepresentation ρ := {
    toLinearEquiv := e
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x => rfl }
  refine BoundedFactors.step S ?_ (E.irreducible_of_euqiv hs) ?_
  · let : Subsingleton S := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      exact x.property.trans y.property.symm
    exact BoundedFactors.zero S.toRepresentation
  · intro _
    exact hb.transport π (MonoidHom.id G) (fun g => ⟨g, rfl⟩)
      E.symm.toLinearEquiv E.symm.isIntertwining

/-- The cycle calculation covers both degree-32 factors separately. -/
theorem cycle_boundedFactors (h : CycleBounds) :
    BoundedFactors (MonoidHom.id Derived) cycleSubrepresentation.toRepresentation := by
  apply BoundedFactors.step cycleCoordinates.half
  · exact boundedFactors_simple (V := cycleCoordinates.half.toSubmodule) (MonoidHom.id Derived) cycleCoordinates.half.toRepresentation
      (cycleCoordinates.half_irreducible (CycleData.fullFactorAlgebra 0))
      h.half
  · exact cycleCoordinates.quotient_irreducible (CycleData.fullFactorAlgebra 1)
  · intro _
    exact h.quotient

/-- Incidence pullback assembles the bounds on the literal flag representation. -/
theorem flag_boundedFactors (hv : VertexBounds) (hc : CycleBounds) :
    BoundedFactors (MonoidHom.id Derived) flagRepresentation :=
  BoundedFactors.of_ker boundary (cycle_boundedFactors hc)
    ((vertex_boundedFactors hv 0).prod (vertex_boundedFactors hv 1))

/-- Every large irreducible inherits the concrete factor bounds via an actual
surjection from the flag representation with two-group stabilizer. -/
theorem oddDisplacementBounds_of_factors
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) V) (hv : VertexBounds) (hc : CycleBounds) :
    OddDisplacementBounds σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨f, hf⟩ := BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    flagPerm baseFlag flagStabilizer flagStabilizer_isPGroup
    mem_flagStabilizer_iff flagTransitive σ
  have hn : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨x, hx⟩ := hf v
    exact hv (hx.symm.trans (congrArg (fun q => q x) hz))
  have hb := (flag_boundedFactors hv hc).quotient_bounds hd f hn
  exact ⟨hb.regular_three, hb.seven⟩

/-- Actual full-normalizer application. Inversion witnesses remain the independent
group-theoretic premise; the factor bounds retain both large degrees. -/
theorem involutionBounds_of_factors
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (w : InversionWitnesses) (hv : VertexBounds) (hc : CycleBounds) :
    InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf w
    (oddDisplacementBounds_of_factors σ hd hv hc)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
