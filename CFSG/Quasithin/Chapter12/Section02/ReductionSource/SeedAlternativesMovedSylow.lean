module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedGeometry
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowTypes
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowModels
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete

/-!
# The local moved-seed classification boundary

Homogeneity converts two unchanged-L module types to the literal equality
V_T = V ∨ Vᵗ. The faithful seed action satisfies every input of the corrected
B.4.2 classification except the FF condition. The separate A₇ row is
realized by transporting that same faithful action to binary four-space.

The conditional source325 consumer exposes two remaining source arguments:
D.3.5(2)'s FF-offender extraction, and the B.4.2 type bound and exclusions
in D.3.5(4--5). Neither is asserted here; the local classification still
requires both arguments, and the later full-normalizer orbit is separate.

Source: Aschbacher--Smith B.4.2, D.3.5 and D.3.11, combined manuscript
of 1 March 2004, printed pp.86,195--196 and201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The type bound needed from the B.4.2 sieve. Both comparisons retain the
original L-action. It specifies a conclusion, without assuming equality of
the actual subgroups or asserting the source classification. -/
@[expose] def SylowTwoModuleTypes (_D : ChosenModule T L V) : Prop :=
  ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
    ∀ s ∈ (T : Subgroup G),
      SameConjugationModule L V (V.map (MulAut.conj s).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj s).toMonoidHom)

omit [Finite G] in
/-- Two unchanged-L types exhaust the actual homogeneous Sylow orbit. -/
theorem sylowOrbit_eq_sup_of_two_module_types (D : ChosenModule T L V)
    (t : G) (ht : t ∈ (T : Subgroup G))
    (htypes : ∀ s ∈ (T : Subgroup G),
      SameConjugationModule L V (V.map (MulAut.conj s).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj s).toMonoidHom)) :
    componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom := by
  let H := L ⊔ (T : Subgroup G)
  let R := (T : Subgroup G).subgroupOf H
  let t' : R := ⟨⟨t, (le_sup_right : (T : Subgroup G) ≤ H) ht⟩, ht⟩
  apply le_antisymm
  · apply iSup_le
    intro s
    rcases htypes s s.property with hs | hs
    · have he : SameConjugationModule L (subspaceImage H D.space)
          ((subspaceImage H D.space).map (MulAut.conj s.val).toMonoidHom) := by
        rwa [D.image_eq]
      have heq := homogeneous_conjugate_eq_of_sameConjugationModule H L le_sup_left R
        D.space D.irrPlus (⟨⟨s, (le_sup_right : (T : Subgroup G) ≤ H) s.property⟩,
          s.property⟩ : R) he
      change (subspaceImage H D.space).map (MulAut.conj s.val).toMonoidHom =
        subspaceImage H D.space at heq
      rw [D.image_eq] at heq
      rw [heq]
      exact le_sup_left
    · have he : SameConjugationModule L
          ((subspaceImage H D.space).map (MulAut.conj t).toMonoidHom)
          ((subspaceImage H D.space).map (MulAut.conj s.val).toMonoidHom) := by
        rwa [D.image_eq]
      have heq := homogeneous_conjugates_eq_of_sameConjugationModule H L le_sup_left R
        D.space D.irrPlus t' (⟨⟨s, (le_sup_right : (T : Subgroup G) ≤ H) s.property⟩,
          s.property⟩ : R) he
      change (subspaceImage H D.space).map (MulAut.conj t).toMonoidHom =
        (subspaceImage H D.space).map (MulAut.conj s.val).toMonoidHom at heq
      rw [D.image_eq] at heq
      rw [← heq]
      exact le_sup_right
  · exact sup_le (le_componentOrbit V T)
      (le_iSup (fun s : T => V.map (MulAut.conj s.val).toMonoidHom) ⟨t, ht⟩)

/-- The corrected full B.4.2 classification on the faithful seed actor.
Only the FF premise remains; the source group and irreducibility hypotheses
come from the original chosen setup. -/
theorem seed_b4_of_ff (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hff : IsFFModule D.seedRepresentation) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      D.seedRepresentation D.componentImage (offenderSubgroup D.seedRepresentation) := by
  obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender D.seedRepresentation).mp hff
  exact ChapterB.SourceClassification.actionCase_of_bestOffender
    (D.seed_sqtk h (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)))
    (D.seed_fitting h.quasisimple) (D.componentImage_quasisimple h.quasisimple)
    (subspaceImageRepresentation_injective _ _) (D.seed_irreducible hc) hA

/-- Actual four-space coordinates for the separate A₇ row of the seed
classification, using the faithful component action rather than a profile. -/
theorem seed_constituentModel_of_alternatingSeven (D : ChosenModule T L V)
    (e : D.componentImage ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) D.space = 4) :
    ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) :=
  constituentModel_of_alternatingSeven _
    ((subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective) e hd

omit [Finite G] in
/-- The model and type sieve gives the literal local D.3.5 conclusion.
The equality of the orbit is derived from homogeneity. -/
theorem sylowMovedModel_of_model_of_two_module_types (D : ChosenModule T L V)
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype))
    (htypes : D.SylowTwoModuleTypes) : D.SylowMovedModel := by
  obtain ⟨t, ht, hnt, htypes⟩ := htypes
  exact ⟨hmodel, t, ht, hnt, D.sylowOrbit_eq_sup_of_two_module_types t ht htypes⟩

/-- Chapter12 source assembly from two independently provable local inputs:
FF extraction, then the model/type sieve conditional on FF. The full orbit
and fixed-space inputs retain the same contracts as the existing consumer. -/
theorem source325_of_ff_and_sieve_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
    (hfixed : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (hff : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → IsFFModule D.seedRepresentation)
    (hsieve : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → IsFFModule D.seedRepresentation →
      ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∧
        D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_moved_inputs_of_many h hmany hfull hfixed _ hexhaust
  intro hq hc hm
  obtain ⟨hmodel, htypes⟩ := hsieve hq hc hm (hff hq hc hm)
  exact D.sylowMovedModel_of_model_of_two_module_types hmodel htypes

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
