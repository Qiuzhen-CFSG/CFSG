module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel

/-!
# Realizing the selected FF action on its literal orbit quotient

The actual KT-action maps onto its faithful image; the proved component-image
identification gives K ≃ F* of that image. This constructs the constituent
realization, retaining the original central quotient projection.

The two presentations W/C_W(K) and W/(W ∩ C_U(K)) have equal kernels.
Their quotient equivalence restricts to the inverter-fixed multiplicity spaces
and intertwines K. Composing with the selected constituent coordinates thus
supplies exactly the family deductions' maps, without identifying the selected
constituent with the inverter-fixed space.

Source: Aschbacher–Smith, proof of 13.8.20(a), printed pp.954–955,
F.9.18(4), pp.325–326, combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.Realization
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]
  (P : Sylow 2 D) (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ K P I)
  (hIP : (P : Subgroup D) ≤ subspaceStabilizer ρ I) (hZ : center K = ⊥)

local notation "τ" => SourceOrbit.ActionImage.centralAction ρ K P I hI.invariant hIP
local notation "σ" => imageRepresentation τ

/-- Realize the faithful action image with its actual KT surjection and component map. -/
@[expose] def constituent : LinearTwo.FiveReconstruction.ConstituentRealization ρ K σ
    (generalizedFitting (actionImage τ)) where
  actor := SourceOrbit.ActionImage.KT K P
  contains := le_sup_left
  space := I
  stable := sup_le hI.invariant hIP
  irrPlus := hI.isIrrPlus
  groupMap := actionHom τ
  surjective := (τ).asGroupHom.rangeRestrict_surjective
  component := (SourceOrbit.ActionImage.fittingEquiv ρ K P I hI.invariant hIP hI hZ).symm
  component_map _ := rfl
  linearEquiv := LinearEquiv.refl _ _
  intertwines _ _ := rfl

variable (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))

private def sectionEquiv (W : Subrepresentation ρ) :
    SectionSpace ρ (SourceOrbit.selectedOrbitLower ρ K) W ≃ₗ[ZMod 2]
      SectionSpace ρ (LinearTwo.centralBottom ρ K W) W :=
  Submodule.quotEquivOfEq _ _ (LinearTwo.centralBottom_comap ρ K W).symm

omit [Finite D] [Finite V] [IsQuasisimple K] in
private theorem sectionEquiv_equivariant (W : Subrepresentation ρ) (g : D)
    (v : SectionSpace ρ (SourceOrbit.selectedOrbitLower ρ K) W) :
    sectionEquiv ρ K W (sectionRepresentation ρ (SourceOrbit.selectedOrbitLower ρ K) W g v) =
      sectionRepresentation ρ (LinearTwo.centralBottom ρ K W) W g (sectionEquiv ρ K W v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private def multiplicityEquiv (W : Subrepresentation ρ) :
    SectionMultiplicity ρ s (SourceOrbit.selectedOrbitLower ρ K) W ≃ₗ[ZMod 2]
      SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W where
  toFun v := ⟨sectionEquiv ρ K W v.val, by
    apply (mem_multiplicitySpace _ _).mpr
    exact (sectionEquiv_equivariant ρ K W (s inverter) v.val).symm.trans
      (congrArg (sectionEquiv ρ K W) ((mem_multiplicitySpace _ _).mp v.property))⟩
  invFun v := ⟨(sectionEquiv ρ K W).symm v.val, by
    apply (mem_multiplicitySpace _ _).mpr
    apply (sectionEquiv ρ K W).injective
    exact (sectionEquiv_equivariant ρ K W (s inverter) ((sectionEquiv ρ K W).symm v.val)).trans
      (by
        simp only [LinearEquiv.apply_symm_apply]
        exact (mem_multiplicitySpace _ _).mp v.property)⟩
  left_inv v := Subtype.ext ((sectionEquiv ρ K W).symm_apply_apply v.val)
  right_inv v := Subtype.ext ((sectionEquiv ρ K W).apply_symm_apply v.val)
  map_add' v w := Subtype.ext ((sectionEquiv ρ K W).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((sectionEquiv ρ K W).map_smul c v.val)

omit [Finite D] [Finite V] [IsQuasisimple K] in
private theorem multiplicityEquiv_equivariant (W : Subrepresentation ρ) (k : K)
    (v : SectionMultiplicity ρ s (SourceOrbit.selectedOrbitLower ρ K) W) :
    multiplicityEquiv ρ K s W
      (sectionMultiplicityAction ρ K.subtype s hs (SourceOrbit.selectedOrbitLower ρ K) W k v) =
      sectionMultiplicityAction ρ K.subtype s hs (LinearTwo.centralBottom ρ K W) W k
        (multiplicityEquiv ρ K s W v) := by
  apply Subtype.ext
  exact sectionEquiv_equivariant ρ K W k v.val

/-- Transport the selected constituent quotient to the literal bottom W ∩ C_V(K).
The quotient equivalence is induced by equality of the two restricted kernels. -/
def multiplicityCoordinates
    (e : (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose).Equiv
      (sectionMultiplicityAction ρ K.subtype s hs
        (SourceOrbit.selectedOrbitLower ρ K) (SourceOrbit.selectedOrbitUpper ρ I))) :
    centralQuotient ρ K I ≃ₗ[ZMod 2]
      SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K (SourceOrbit.selectedOrbitUpper ρ I))
        (SourceOrbit.selectedOrbitUpper ρ I) :=
  e.toLinearEquiv.trans (multiplicityEquiv ρ K s (SourceOrbit.selectedOrbitUpper ρ I))

/-- The quotient-kernel comparison preserves the specified component marking. -/
theorem multiplicityCoordinates_equivariant
    (e : (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose).Equiv
      (sectionMultiplicityAction ρ K.subtype s hs
        (SourceOrbit.selectedOrbitLower ρ K) (SourceOrbit.selectedOrbitUpper ρ I)))
    (k : K) (v : centralQuotient ρ K I) :
    multiplicityCoordinates ρ K P I hI s hs e
        (σ ((constituent ρ K P I hI hIP hZ).component k) v) =
      sectionMultiplicityAction ρ K.subtype s hs
        (LinearTwo.centralBottom ρ K (SourceOrbit.selectedOrbitUpper ρ I))
        (SourceOrbit.selectedOrbitUpper ρ I) k
        (multiplicityCoordinates ρ K P I hI s hs e v) := by
  change multiplicityEquiv ρ K s _ (e (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose k v)) = _
  exact (congrArg (multiplicityEquiv ρ K s (SourceOrbit.selectedOrbitUpper ρ I))
    (e.toIntertwiningMap.isIntertwining _ _ k v)).trans
      (multiplicityEquiv_equivariant ρ K s hs _ k (e v))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.Realization
