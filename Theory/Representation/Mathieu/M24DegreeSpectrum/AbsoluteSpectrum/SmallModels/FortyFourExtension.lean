module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.Inputs
public import Theory.Representation.ScalarDescent
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Scalar extension of a binary degree-forty-four pair

Genuine tensor extension preserves absolute irreducibility and dimension.
Descent of representation equivalences preserves inequivalence. A basis then
puts each extended action on the coordinate space required by the small
spectrum contract. Thus construction of two binary absolutely irreducible
modules suffices; no completeness premise is introduced.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

public section
noncomputable section
open scoped TensorProduct
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
open Sporadic.Mathieu
universe v

/-- A concrete binary pair gives the required pair over every closed field. -/
theorem fortyFourModelsExist_of_binary
    (h : BinaryFortyFourModelsExist) : FortyFourModelsExist.{v} := by
  classical
  obtain ⟨ρ, hirr, hneq⟩ := h
  intro F _ _ _
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E : (F ⊗[ZMod 2] (Fin 44 → ZMod 2)) ≃ₗ[F] (Fin 44 → F) :=
    (Module.finBasisOfFinrankEq F (F ⊗[ZMod 2] (Fin 44 → ZMod 2)) (by
      rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin])).equivFun
  let σ : Fin 2 → Representation F M24 (Fin 44 → F) := fun i =>
    E.conjRingEquiv.toMonoidHom.comp (extendScalars F (ρ i))
  have equiv (i : Fin 2) : (extendScalars F (ρ i)).Equiv (σ i) :=
    .mk E (by
      intro g
      apply LinearMap.ext
      intro v
      change E ((extendScalars F (ρ i)) g v) =
        E ((extendScalars F (ρ i)) g (E.symm (E v)))
      rw [E.symm_apply_apply])
  refine ⟨σ, ?_, ?_⟩
  · intro i
    let := hirr i
    exact (RepEquiv.ofRepresentationEquiv (equiv i)).irreducible_euqiv.mp
      (IsAbsolutelyIrreducible.irreducible_of_extension (ρ i) F)
  · intro i j hij
    constructor
    intro e
    have ee := ((equiv i).trans e).trans (equiv j).symm
    obtain ⟨d⟩ := repEquiv_of_extendScalars (ρ i) (ρ j)
      ⟨RepEquiv.ofRepresentationEquiv ee⟩
    exact (hneq hij).false d.toRepresentationEquiv

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
