module

public import Theory.Representation.G2DerivedPermutationFiltration

/-!
# Exact degrees in the binary derived G₂ permutation filtration

The checked vertex flags have degrees 1, 6 and 14, and the incidence kernel
has two simple factors of degree 32. Keeping those exact degrees in the
filtration proves that every irreducible binary module of G₂(2)′ has degree
1, 6, 14 or 32. In particular the branch above degree eight starts at fourteen.
This uses the actual transitive flag action with two-group stabilizer.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 4.3, pp.10--11; the filtration certificates are those used for
Aschbacher--Smith G.7.2(3), printed pp.347--348.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Representation G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

private def degrees : Set ℕ := {d | d = 1 ∨ d = 6 ∨ d = 14 ∨ d = 32}

private theorem coordinate_exact (i : Fin 2) :
    FactorDegreeFiltration degrees (representation i) := by
  let C := adaptedFlagCoordinates i
  apply filtration_of_flag degrees (length i) C.stage C.zero C.last C.mono
  · intro m hm
    exact adaptedFlag_quotient_irreducible i ⟨m, hm⟩
  · intro m hm
    change Module.finrank (ZMod 2)
      (((adaptedFlagCoordinates i).stage (m + 1)).toSubmodule ⧸
        (within ((adaptedFlagCoordinates i).stage m)
          ((adaptedFlagCoordinates i).stage (m + 1))).toSubmodule) ∈ degrees
    rw [adaptedFlag_quotient_finrank i ⟨m, hm⟩]
    exact (by
      change ∀ i (t : Factor i), degree i t = 1 ∨ degree i t = 6 ∨
        degree i t = 14 ∨ degree i t = 32
      decide +kernel : ∀ i (t : Factor i), degree i t ∈ degrees) i ⟨m, hm⟩

private theorem vertex_exact (i : Fin 2) :
    FactorDegreeFiltration degrees (vertexRepresentation i) := by
  let e := Equiv.ofBijective (vertex i) (vertex_bijective i)
  let el : Space ≃ₗ[ZMod 2] BinaryPermutation.Full (Vertex i) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  apply (coordinate_exact i).transport groupHom groupHom_surjective (vertexRepresentation i) el
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

private theorem cycle_exact :
    FactorDegreeFiltration degrees cycleSubrepresentation.toRepresentation := by
  let c := cycleCoordinates
  apply FactorDegreeFiltration.step c.half
  · apply CycleMatrixCriterion.simple_filtration (k := ZMod 2)
      (G := G2DerivedPermutationFiltration.Group) (V := c.half.toSubmodule)
      degrees c.half.toRepresentation
      (c.half_irreducible (CycleData.fullFactorAlgebra 0))
    rw [c.finrank_half]
    exact Or.inr (Or.inr (Or.inr rfl))
  · exact c.quotient_irreducible (CycleData.fullFactorAlgebra 1)
  · rw [c.finrank_quotient]
    exact Or.inr (Or.inr (Or.inr rfl))

/-- The complete degree list follows from the literal flag filtration. -/
theorem binary_derived_irreducible_degrees
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V)
    [IsIrreducible σ] :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 6 ∨
      Module.finrank (ZMod 2) V = 14 ∨ Module.finrank (ZMod 2) V = 32 := by
  exact BinaryPermutation.finrank_mem_of_factorDegreeFiltration flagPerm baseFlag
    flagStabilizer flagStabilizer_isPGroup mem_flagStabilizer_iff flagTransitive
    (FactorDegreeFiltration.of_ker boundary cycle_exact ((vertex_exact 0).prod (vertex_exact 1))) σ

/-- The large-degree branch has a genuine gap, rather than an assumed catalogue. -/
theorem fourteen_le_binary_derived_degree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V)
    [IsIrreducible σ] (h : 8 < Module.finrank (ZMod 2) V) :
    14 ≤ Module.finrank (ZMod 2) V := by
  have := binary_derived_irreducible_degrees σ
  omega

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
