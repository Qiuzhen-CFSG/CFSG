module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Building
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Equivariant duality for the S₆ building

The coordinate pairings make the actual boundary and coboundary adjoint.
Consequently the cycle space is the annihilator of the coboundaries, giving
an S₆-equivariant perfect pairing between top homology and top cohomology.
Both have dimension sixteen. This supplies the homology interpretation needed
when a concrete tensor is first compared with the cohomology quotient.

Source: the incidence-building realization of the Steinberg representation
used in Aschbacher–Smith G.5.1–2, printed pp.342–343. Identification with the
specific tensor remains a separate obligation.
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
namespace BinaryAlternatingSix.SymmetricCatalogue

private def vertexDual : VertexModule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) VertexModule :=
  ((dotProductEquiv (ZMod 2) Duad).prodCongr (dotProductEquiv (ZMod 2) Syntheme)).trans
    (Module.dualProdDualEquivDual (ZMod 2) (Full Duad) (Full Syntheme))

private theorem vertexDual_edge (f : Flag) (w : VertexModule) :
    vertexDual (edgeVertices f) w = w.1 f.val.1 + w.2 f.val.2 := by
  simp [vertexDual, edgeVertices, single_dotProduct]

/-- Boundary and coboundary are adjoint for the coordinate pairings. -/
private theorem boundary_coboundary_adjoint (v : FlagModule) (w : VertexModule) :
    dotProductEquiv (ZMod 2) Flag v (coboundary w) = vertexDual (boundaryLinear v) w := by
  change (∑ f : Flag, v f * (w.1 f.val.1 + w.2 f.val.2)) =
    vertexDual (∑ f : Flag, v f • edgeVertices f) w
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    vertexDual_edge, smul_eq_mul]

theorem cycles_iff_annihilator (v : FlagModule) :
    v ∈ cycles ↔ dotProductEquiv (ZMod 2) Flag v ∈ coboundaries.toSubmodule.dualAnnihilator := by
  change boundaryLinear v = 0 ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hv w hw
    obtain ⟨u, rfl⟩ := hw
    change dotProductEquiv (ZMod 2) Flag v (coboundary u) = 0
    rw [boundary_coboundary_adjoint, hv, map_zero, LinearMap.zero_apply]
  · intro hv
    apply vertexDual.injective
    rw [map_zero]
    apply LinearMap.ext
    intro w
    rw [← boundary_coboundary_adjoint]
    exact hv (coboundary w) ⟨w, rfl⟩

private noncomputable def cycleAnnihilatorEquiv :
    TopHomology ≃ₗ[ZMod 2] coboundaries.toSubmodule.dualAnnihilator where
  toFun v := ⟨dotProductEquiv (ZMod 2) Flag v.val, (cycles_iff_annihilator v.val).mp v.property⟩
  invFun f := ⟨(dotProductEquiv (ZMod 2) Flag).symm f.val,
    (cycles_iff_annihilator _).mpr (by simpa only [LinearEquiv.apply_symm_apply] using f.property)⟩
  left_inv v := Subtype.ext ((dotProductEquiv (ZMod 2) Flag).symm_apply_apply v.val)
  right_inv f := Subtype.ext ((dotProductEquiv (ZMod 2) Flag).apply_symm_apply f.val)
  map_add' v w := Subtype.ext ((dotProductEquiv (ZMod 2) Flag).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((dotProductEquiv (ZMod 2) Flag).map_smul c v.val)

/-- The perfect coordinate pairing identifies cycles with the dual of top cohomology. -/
noncomputable def homologyCohomologyDualEquiv :
    TopHomology ≃ₗ[ZMod 2] Module.Dual (ZMod 2) TopCohomology :=
  cycleAnnihilatorEquiv.trans coboundaries.toSubmodule.dualQuotEquivDualAnnihilator.symm

@[simp] theorem homologyCohomologyDualEquiv_mk (v : TopHomology) (w : FlagModule) :
    homologyCohomologyDualEquiv v (coboundaries.toSubmodule.mkQ w) =
      ∑ f : Flag, v.val f * w f := by
  change coboundaries.toSubmodule.dualQuotEquivDualAnnihilator.symm
    (cycleAnnihilatorEquiv v) (Submodule.Quotient.mk w) = _
  rw [Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
  rfl

/-- This is a duality of the literal S₆ representations, with their original actions. -/
noncomputable def homologyCohomologyDualRepresentationEquiv :
    topHomologyRepresentation.Equiv topCohomologyRepresentation.dual :=
  .mk homologyCohomologyDualEquiv (fun g => by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      change (∑ f : Flag, v.val (g⁻¹ • f) * w f) =
        ∑ f : Flag, v.val f * w (g • f)
      exact (Equiv.sum_comp (MulAction.toPerm g)
        (fun f : Flag => v.val (g⁻¹ • f) * w f)).symm.trans (by simp))

@[simp] theorem homologyCohomologyDualRepresentationEquiv_mk
    (v : TopHomology) (w : FlagModule) :
    homologyCohomologyDualRepresentationEquiv v (coboundaries.toSubmodule.mkQ w) =
      ∑ f : Flag, v.val f * w f :=
  homologyCohomologyDualEquiv_mk v w

theorem topHomology_finrank : Module.finrank (ZMod 2) TopHomology = 16 := by
  rw [homologyCohomologyDualEquiv.finrank_eq, Subspace.dual_finrank_eq, topCohomology_finrank]

end BinaryAlternatingSix.SymmetricCatalogue
