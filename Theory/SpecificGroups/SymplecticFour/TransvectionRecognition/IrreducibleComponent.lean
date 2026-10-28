module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.PerfectLayer
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Schur
public import Theory.GroupTheory.GeneralizedFitting.PerfectLayerAlternative
/-!
# An irreducible component is the ambient socle

Over a finite coefficient field the Schur commutant of an irreducible action
is commutative. Every other component centralizes a given component and is
perfect, so acts trivially; faithfulness excludes it. Thus, when F=1, an
irreducible component is the whole generalized Fitting subgroup. This
transfers the simple socle of the normal transvection closure to the actual
pair. Source: Aschbacher--Smith G.4.9, printed pp.341--342.
-/

public noncomputable section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open Theory.GroupTheory
variable {F:Type*} [Field F] [Finite F]
omit [Finite F] in
private theorem faithful (H:Subgroup (Sp F)) :
    Function.Injective ((Representation.symplecticNatural 2).comp H.subtype) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun f : Module.End F (Vector F) => f (Pi.single j 1) i) he
  change ((g : Sp F).val  *ᵥ  Pi.single j 1) i = ((h : Sp F).val  *ᵥ  Pi.single j 1) i at hh
  simpa using hh

/-- A literal irreducible symplectic component is the entire generalized
Fitting subgroup when the ambient Fitting subgroup vanishes. -/
theorem generalizedFitting_eq_of_irreducible_component (H:Subgroup (Sp F))(K:Subgroup H)(hK:IsComponent H K)
    (hi:Representation.IsIrreducible (((Representation.symplecticNatural 2).comp H.subtype).comp K.subtype))
    (hfit:fittingSubgroup H=⊥) : generalizedFitting H=K := by
  let ρ : Representation F H (Vector F) := (Representation.symplecticNatural 2).comp H.subtype
  let : Representation.IsIrreducible (ρ.comp K.subtype) := hi
  have hu (D:Subgroup H)(hD:IsComponent H D):D=K := by
    by_contra hne
    let : IsQuasisimple D := hD.2
    have hc := commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hK hne)
    have he : ρ.comp D.subtype=1 := Representation.ComponentTensor.commuting_eq_one_of_irreducible
      (ρ.comp K.subtype) (ρ.comp D.subtype) (fun k d=>by
        change ρ (k:H)*ρ (d:H)=ρ (d:H)*ρ (k:H)
        rw [←map_mul,←map_mul]
        exact congrArg ρ ((hc d.property k k.property)))
    have hbot : D=⊥ := by
      apply bot_unique
      intro d hd
      change d=1
      apply faithful H
      exact (congrArg (fun σ:Representation F D (Vector F)=>σ ⟨d,hd⟩) he).trans ρ.map_one.symm
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact (nontrivial_iff_ne_bot D).mp inferInstance hbot
  apply le_antisymm _ (component_le_generalizedFitting H K hK)
  rw [generalizedFitting,hfit,bot_sup_eq]
  exact sSup_le fun D hD=>(hu D hD).le
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
