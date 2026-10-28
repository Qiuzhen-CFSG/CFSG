module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag

/-!
# Matrix coordinates on the literal cubic flag quotients

The coordinate equivalence carries each stage of the image/kernel flag to an
invariant subspace of the 126 coordinate vectors. The stages are exactly zero,
the image of the fixed nilpotent matrix, its kernel, and the whole space.
`quotientEquiv` identifies all literal successive quotients equivariantly;
`matrixQuotient_actor_mk` gives the checked monomial action on representatives.
The first and last quotients also have explicit coordinates in the same matrix
image, so their simplicity can be checked on one concrete action.

These interfaces consume the independent coordinate and matrix-relation
contracts. `ModelFlag.Realization` discharges both for the original induced
module. Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453. Simplicity is a separate obligation.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
variable {K : Type v} [Field K] [CharP K 2]
  {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ) (h : MatrixRelations.{v})

/-- The original group action in the specified 126 coordinates. -/
def Coordinates.matrixRepresentation : Representation K (standardGroup modelForm) (Fin 126 → K) :=
  (c.equiv.conjAlgEquiv K).toMonoidHom.comp
    (ind (standardBorel modelForm).subtype (scalarCharacter χ))

theorem Coordinates.matrixRepresentation_actor (a : Fin 2) (w : Fin 126 → K) :
    c.matrixRepresentation (c.actor a) w = (generatorMatrix c.z c.quadratic a).mulVec w := by
  change c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ)
    (c.actor a) (c.equiv.symm w)) = _
  rw [c.action, c.equiv.apply_symm_apply]

/-- Transport of the actual flag stage, with no change of acting group. -/
def Coordinates.matrixStage (m : ℕ) : Subrepresentation c.matrixRepresentation where
  toSubmodule := ((c.flag h).stage m).toSubmodule.map c.equiv.toLinearMap
  apply_mem_toSubmodule g w hw := by
    obtain ⟨v, hv, rfl⟩ := hw
    refine ⟨ind (standardBorel modelForm).subtype (scalarCharacter χ) g v,
      ((c.flag h).stage m).apply_mem_toSubmodule g hv, ?_⟩
    change c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) g v) =
      c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) g
        (c.equiv.symm (c.equiv v)))
    rw [c.equiv.symm_apply_apply]

def Coordinates.stageEquiv (m : ℕ) :
    ((c.flag h).stage m).toSubmodule ≃ₗ[K] (c.matrixStage h m).toSubmodule :=
  c.equiv.submoduleMap _

@[simp] theorem Coordinates.stageEquiv_apply (m : ℕ) (x : ((c.flag h).stage m).toSubmodule) :
    (c.stageEquiv h m x).val = c.equiv x.val := rfl

@[simp] theorem Coordinates.stageEquiv_symm_apply (m : ℕ)
    (x : (c.matrixStage h m).toSubmodule) :
    ((c.stageEquiv h m).symm x).val = c.equiv.symm x.val := rfl

theorem Coordinates.stageEquiv_action (m : ℕ) (g : standardGroup modelForm)
    (x : ((c.flag h).stage m).toSubmodule) :
    c.stageEquiv h m (((c.flag h).stage m).toRepresentation g x) =
      (c.matrixStage h m).toRepresentation g (c.stageEquiv h m x) := by
  apply Subtype.ext
  change c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) g x.val) =
    c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) g
      (c.equiv.symm (c.equiv x.val)))
  rw [c.equiv.symm_apply_apply]

theorem Coordinates.within_map (m : ℕ) :
    (within ((c.flag h).stage m) ((c.flag h).stage (m + 1))).toSubmodule.map
      (c.stageEquiv h (m + 1)).toLinearMap =
      (within (c.matrixStage h m) (c.matrixStage h (m + 1))).toSubmodule := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.val, hv, rfl⟩
  · intro hw
    obtain ⟨v, hv, heq⟩ := hw
    change c.equiv v = w.val at heq
    refine ⟨(c.stageEquiv h (m + 1)).symm w, ?_, (c.stageEquiv h (m + 1)).apply_symm_apply w⟩
    change c.equiv.symm w.val ∈ ((c.flag h).stage m).toSubmodule
    rw [← heq, c.equiv.symm_apply_apply]
    exact hv

/-- Equivariant coordinates on the literal successive quotient. -/
def Coordinates.quotientEquiv (m : ℕ) :
    (((c.flag h).stage (m + 1)).toSubmodule ⧸
      (within ((c.flag h).stage m) ((c.flag h).stage (m + 1))).toSubmodule) ≃ₗ[K]
    ((c.matrixStage h (m + 1)).toSubmodule ⧸
      (within (c.matrixStage h m) (c.matrixStage h (m + 1))).toSubmodule) :=
  Submodule.Quotient.equiv _ _ (c.stageEquiv h (m + 1)) (c.within_map h m)

@[simp] theorem Coordinates.quotientEquiv_mk (m : ℕ)
    (x : ((c.flag h).stage (m + 1)).toSubmodule) :
    c.quotientEquiv h m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (c.stageEquiv h (m + 1) x) := rfl

theorem Coordinates.quotientEquiv_action (m : ℕ) (g : standardGroup modelForm)
    (x : ((c.flag h).stage (m + 1)).toSubmodule ⧸
      (within ((c.flag h).stage m) ((c.flag h).stage (m + 1))).toSubmodule) :
    c.quotientEquiv h m
      ((within ((c.flag h).stage m) ((c.flag h).stage (m + 1))).quotientRepresentation g x) =
    (within (c.matrixStage h m) (c.matrixStage h (m + 1))).quotientRepresentation g
      (c.quotientEquiv h m x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x => exact congrArg Submodule.Quotient.mk (c.stageEquiv_action h (m + 1) g x)

theorem Coordinates.matrixQuotient_degree (m : ℕ) (hm : m < 3) :
    Module.finrank K ((c.matrixStage h (m + 1)).toSubmodule ⧸
      (within (c.matrixStage h m) (c.matrixStage h (m + 1))).toSubmodule) =
      if m = 1 then 84 else 21 :=
  (c.quotientEquiv h m).finrank_eq.symm.trans ((c.flag h).degree m hm)

theorem Coordinates.matrixStage_one :
    (c.matrixStage h 1).toSubmodule = LinearMap.range (nilpotentMatrix c.z c.quadratic).toLin' := by
  ext w
  constructor
  · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
    exact ⟨c.equiv x, (c.intertwiner_equiv h x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨c.intertwiner h (c.equiv.symm x), ⟨c.equiv.symm x, rfl⟩, ?_⟩
    change c.equiv (c.intertwiner h (c.equiv.symm x)) =
      (nilpotentMatrix c.z c.quadratic).mulVec x
    rw [c.intertwiner_equiv, c.equiv.apply_symm_apply]

theorem Coordinates.matrixStage_two :
    (c.matrixStage h 2).toSubmodule = LinearMap.ker (nilpotentMatrix c.z c.quadratic).toLin' := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change (nilpotentMatrix c.z c.quadratic).mulVec (c.equiv v) = 0
    rw [← c.intertwiner_equiv h]
    change c.intertwiner h v = 0 at hv
    rw [hv, map_zero]
  · intro hw
    refine ⟨c.equiv.symm w, ?_, c.equiv.apply_symm_apply w⟩
    change c.intertwiner h (c.equiv.symm w) = 0
    apply c.equiv.injective
    rw [c.intertwiner_equiv, c.equiv.apply_symm_apply, map_zero]
    exact hw

theorem Coordinates.matrixStage_zero : (c.matrixStage h 0).toSubmodule = ⊥ := by
  change Submodule.map c.equiv.toLinearMap ⊥ = ⊥
  exact Submodule.map_bot _

theorem Coordinates.matrixStage_three : (c.matrixStage h 3).toSubmodule = ⊤ := by
  change Submodule.map c.equiv.toLinearMap ⊤ = ⊤
  apply top_unique
  intro w _
  exact ⟨c.equiv.symm w, by trivial, c.equiv.apply_symm_apply w⟩

theorem Coordinates.matrixStage_actor (m : ℕ) (a : Fin 2)
    (x : (c.matrixStage h m).toSubmodule) :
    ((c.matrixStage h m).toRepresentation (c.actor a) x).val =
      (generatorMatrix c.z c.quadratic a).mulVec x.val :=
  c.matrixRepresentation_actor a x.val

theorem Coordinates.matrixQuotient_actor_mk (m : ℕ) (a : Fin 2)
    (x : (c.matrixStage h (m + 1)).toSubmodule) :
    (within (c.matrixStage h m) (c.matrixStage h (m + 1))).quotientRepresentation
      (c.actor a) (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk
      (⟨(generatorMatrix c.z c.quadratic a).mulVec x.val, by
        rw [← c.matrixRepresentation_actor]
        exact (c.matrixStage h (m + 1)).apply_mem_toSubmodule (c.actor a) x.property⟩ :
          (c.matrixStage h (m + 1)).toSubmodule) := by
  exact congrArg Submodule.Quotient.mk (Subtype.ext (c.matrixStage_actor h (m + 1) a x))

/-- The first literal quotient identified with the fixed matrix image. -/
def Coordinates.firstQuotientCoordinates :
    (((c.flag h).stage 1).toSubmodule ⧸
      (within ((c.flag h).stage 0) ((c.flag h).stage 1)).toSubmodule) ≃ₗ[K]
      LinearMap.range (nilpotentMatrix c.z c.quadratic).toLin' :=
  (firstQuotientEquivRange (c.intertwiner h)).trans
    (conjugateRangeEquiv c.equiv (nilpotentMatrix c.z c.quadratic).toLin')

/-- The last literal quotient identified with the same fixed matrix image. -/
def Coordinates.lastQuotientCoordinates :
    (((c.flag h).stage 3).toSubmodule ⧸
      (within ((c.flag h).stage 2) ((c.flag h).stage 3)).toSubmodule) ≃ₗ[K]
      LinearMap.range (nilpotentMatrix c.z c.quadratic).toLin' :=
  (lastQuotientEquivRange (c.intertwiner h)).trans
    (conjugateRangeEquiv c.equiv (nilpotentMatrix c.z c.quadratic).toLin')

@[simp] theorem Coordinates.firstQuotientCoordinates_mk
    (x : ((c.flag h).stage 1).toSubmodule) :
    (c.firstQuotientCoordinates h (Submodule.Quotient.mk x)).val = c.equiv x.val := rfl

@[simp] theorem Coordinates.lastQuotientCoordinates_mk
    (x : ((c.flag h).stage 3).toSubmodule) :
    (c.lastQuotientCoordinates h (Submodule.Quotient.mk x)).val =
      c.equiv (c.intertwiner h x.val) := rfl

theorem Coordinates.firstQuotientCoordinates_action (a : Fin 2)
    (x : ((c.flag h).stage 1).toSubmodule ⧸
      (within ((c.flag h).stage 0) ((c.flag h).stage 1)).toSubmodule) :
    (c.firstQuotientCoordinates h
      ((within ((c.flag h).stage 0) ((c.flag h).stage 1)).quotientRepresentation (c.actor a) x)).val =
    (generatorMatrix c.z c.quadratic a).mulVec (c.firstQuotientCoordinates h x).val := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change c.equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ)
      (c.actor a) x.val) = (generatorMatrix c.z c.quadratic a).mulVec (c.equiv x.val)
    exact c.action a x.val

theorem Coordinates.lastQuotientCoordinates_action (a : Fin 2)
    (x : ((c.flag h).stage 3).toSubmodule ⧸
      (within ((c.flag h).stage 2) ((c.flag h).stage 3)).toSubmodule) :
    (c.lastQuotientCoordinates h
      ((within ((c.flag h).stage 2) ((c.flag h).stage 3)).quotientRepresentation (c.actor a) x)).val =
    (generatorMatrix c.z c.quadratic a).mulVec (c.lastQuotientCoordinates h x).val := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change c.equiv (c.intertwiner h
      (ind (standardBorel modelForm).subtype (scalarCharacter χ) (c.actor a) x.val)) =
      (generatorMatrix c.z c.quadratic a).mulVec (c.equiv (c.intertwiner h x.val))
    exact (congrArg c.equiv
      ((c.intertwiner h).isIntertwining _ _ (c.actor a) x.val)).trans (c.action a _)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
