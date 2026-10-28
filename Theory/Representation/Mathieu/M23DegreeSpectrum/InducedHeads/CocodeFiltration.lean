module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.Flag
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison

/-!
# Assembly of the M23 cocode filtration certificates

The checked basis change and block projections construct the literal
successive quotient actions. The proved native coordinate comparison and
binary common-invariant-subspace certificates give the unconditional
`canonicalCocodeFiltration`. Its five simple factors have dimensions
120, 11, 44, 11 and 44 over F2, at cuts 0, 120, 131, 175, 186 and 230.

The native comparison retains the canonical point-9 marking and the actual
right-coset action. The matrix certificates prove simplicity on the literal
successive quotients, without a character table or a degree-catalogue premise.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph; Theorem 6.6/Table 6.7.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

private theorem irreducible_of_factorMatrices
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M23 V) (t : Factor)
    (e : V ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2))
    (he : ∀ j v, e (ρ (actor j) v) = (factorMatrix t j).mulVec (e v))
    (h : SimpleMatrices) : ρ.IsIrreducible := by
  let : NeZero (degree t) := ⟨Nat.ne_of_gt (degree_pos t)⟩
  let : Nontrivial V := e.symm.injective.nontrivial
  refine ⟨?_⟩
  intro U
  have hstable : ∀ (j : Fin 2) (v : Fin (degree t) → ZMod 2),
      v ∈ U.toSubmodule.map e.toLinearMap →
        (factorMatrix t j).mulVec v ∈ U.toSubmodule.map e.toLinearMap := by
    intro j v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨ρ (actor j) w, U.apply_mem_toSubmodule _ hw, he j w⟩
  rcases h t _ hstable with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    simpa using hb
  · right
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊤
    simpa using ht

/-- Apply the independent binary simplicity certificates to the actual
successive quotients of the canonical cocode induction. -/
theorem filtration_of_flag_matrices (C : FlagCoordinates) (hsimple : SimpleMatrices) :
    FactorDegreeFiltration factorDegrees canonicalCocodeAction := by
  apply filtration_of_flag factorDegrees 5 C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_factorMatrices _ t (C.coordinates t)
      (C.generator_coordinates t) hsimple
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank (ZMod 2)
      ((C.stage (t.val + 1)).toSubmodule ⧸
        (within (C.stage t.val) (C.stage (t.val + 1))).toSubmodule) ∈ factorDegrees
    rw [he]
    exact degree_allowed t

/-- A native-action comparison and matrix simplicity discharge the canonical
filtration obligation. Neither premise is supplied by the discovery data. -/
theorem filtration_of_certificates (C : GeneratorCoordinates) (hsimple : SimpleMatrices) :
    FactorDegreeFiltration factorDegrees canonicalCocodeAction :=
  filtration_of_flag_matrices
    (flagOfGeneratorCoordinates C.equiv C.intertwines C.generates) hsimple

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads

/-- The canonical induction of the native ten-dimensional M22 cocode has a
filtration with simple factors of degrees 120, 11, 44, 11 and 44 over F2.
Both the native-action comparison and every matrix simplicity certificate
are discharged, so no extra premise remains. -/
theorem canonicalCocodeFiltration :
    FactorDegreeFiltration factorDegrees canonicalCocodeAction :=
  CocodeFiltration.filtration_of_certificates
    CocodeFiltration.nativeGeneratorCoordinates CocodeFiltration.simpleMatrices

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads
