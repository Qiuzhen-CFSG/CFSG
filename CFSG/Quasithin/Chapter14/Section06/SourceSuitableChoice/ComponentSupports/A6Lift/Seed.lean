module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.Coordinates
public import Theory.Representation.BinaryOffender.StabilizerCentralCover
public import Theory.Representation.BinaryPermutation.SixPolar

/-!
# The fixed-moving lift on a natural A₆ seed

The literal central quotient of an Irr⁺ seed is marked in the four-space.
Its fixed kernel has dimension at most one, and is therefore central for
the full stabilizer. The original projection is a cover for that actor.
The polar/permutation coordinate equivalence supplies the exact A₆ marking
required by I.2.3, retaining the original covering space and fixed radical.
Every two-subgroup of the stabilizer fixes a vector moved by the component.

Source: Aschbacher--Smith I.2.3 and the choice before14.6.24,
printed pp.413 and1038. Original subgroup lifting is the source consumer.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
open Theory.SpecificGroups.SymmetricSix Matrix

theorem polar_marking (g : Core) (v : Natural) :
    PolarNatural.equiv (SymplecticFourOrthogonalCover.binaryNatural g v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (alternatingEquiv g) (PolarNatural.equiv v) := by
  have hg : Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
      (alternatingEquiv g).val = g.val := by
    change Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
      (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm g.val) = g.val
    exact MulEquiv.apply_symm_apply _ _
  change PolarNatural.equiv (g.val.val *ᵥ v) = _
  rw [← hg, Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply,
    polarRepresentation_apply]
  exact PolarNatural.equiv_action _ _

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
  {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
  (j : K ≃* alternatingGroup (Fin 6))
  (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
  (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.choose k v) =
    BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (j k) (l v))

include hI j l he in
theorem exists_stabilizer_fixed_moving
    (P : Subgroup (subspaceStabilizer ρ I)) (hP : IsPGroup 2 P) :
    ∃ v : I, v ∉ (fixedSpace ρ K).comap I.subtype ∧
      ∀ p : P, stabilizerRepresentation ρ I p.val v = v := by
  let J := subspaceStabilizer ρ I
  let L := K.subgroupOf J
  let eL := (subgroupOfEquivOfLe hI.choose).trans (j.trans alternatingEquiv.symm)
  let τ := stabilizerRepresentation ρ I
  let η := stabilizerCentralAction ρ K I
  let E := l.trans PolarNatural.equiv.symm
  let q := stabilizerCentralProjection ρ K I
  have hq := stabilizerCentralProjection_isCover ρ K I hI
    (hI.finrank_of_alternating_six_central_quotient ρ K j l he).1
  have hE : ∀ k : L, ∀ v, E (η k.val v) = natural eL k (E v) := by
    intro k v
    apply PolarNatural.equiv.injective
    change PolarNatural.equiv (PolarNatural.equiv.symm (l (η k.val v))) = _
    rw [PolarNatural.equiv.apply_symm_apply]
    change l (η k.val v) = PolarNatural.equiv (SymplecticFourOrthogonalCover.binaryNatural (eL k) (E v))
    rw [polar_marking]
    change l (centralQuotientRepresentation ρ K I hI.choose ⟨k.val.val,k.property⟩ v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)
        (alternatingEquiv (alternatingEquiv.symm (j ⟨k.val.val,k.property⟩)))
        (PolarNatural.equiv (PolarNatural.equiv.symm (l v)))
    rw [alternatingEquiv.apply_symm_apply, PolarNatural.equiv.apply_symm_apply]
    exact he _ _
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  obtain ⟨_,_,⟨v,_,hm,hf⟩,_,_⟩ := fixed_moving_vector L eL
    (coordinateAction η E) (coordinateAction_marked L eL η E hE) τ
    (coordinateProjection q E) (coordinateProjection_isCover q hq E) S
  refine ⟨v,?_,fun p => hf ⟨p.val,hS p.property⟩⟩
  intro hv
  apply hm
  intro k
  exact Subtype.ext (hv ⟨k.val.val,k.property⟩)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
