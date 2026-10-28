module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulExclusion
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import Theory.GroupTheory.CComponent.ResidualImage
public import Theory.Representation.Quotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.AlternatingSix

/-!
# Constructing the component for the nonsolvable seed exclusion

The original point normalizer has nontrivial two-core, so the genuine A/C
source theorems and A.3.9 give generation of its solvable residual by
C-components. The residual of the faithful hatted action lifts through its
literal quotient map to an actual C-component of H. Its nonsolvable normal
image proves relative normality even when the full action kernel is not
known to be solvable. Surjective restriction transports irreducibility,
image orders and the original conjugate-center marking.

The faithful-family and rank-one inner-action argument then proves the
nonsolvable branch of 14.3.25 from the earlier marked quotient row. No
component, kernel equality, centerlessness, or later natural coordinates
are assumed. The last theorems feed this result to the S5/A6 centerlessness
exclusions and the literal LocalStructure consumer.

NonsolvableSeedRow is an explicit earlier-action contract, not a theorem
asserting the action classification. Constructing the full marked 14.3.23--24
alternatives remains with qt-d-hs-action-source. The solvable seed exclusion
and remaining S6/G2(2) and Goldschmidt branches remain with this centerlessness
owner; final discharge of the action and centerlessness inputs stays with
qt-d-hs-local-structure.

Source: Aschbacher--Smith, A.3.3, A.3.9(1), 1.2.1(1), 14.3.23--25 and
14.3.31, printed pp.42--43,46,504,999--1003, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_H_residual_generation (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) :
    cComponentLayer F.H = solvableResidual F.H := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hp : F.Vi 1 ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (F.Vi 1))
    ((F.le_seed 1).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H)) le_rfl
  have hH : F.H ∈ Chapter1.H G := by
    intro he
    have hz : F.Vi 1 = ⊥ := le_bot_iff.mp (he ▸ hp)
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  exact Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
    (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hH)

/-- Lift the earlier quotient component through the literal hatted action,
without assuming solvability of its kernel or centerlessness. -/
theorem source_lift_dotted_residual (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3)
    (hR : IsQuasisimple (solvableResidual (Hdot F F.uhatAction))) :
    ∃ K : Subgroup F.H, K.Normal ∧
      K.map F.H.subtype ∈ Chapter1.cComponentsIn F.H ∧
      K.map (QuotientGroup.mk' F.uhatAction.ker) =
        solvableResidual (Hdot F F.uhatAction) := by
  have hC : (solvableResidual (Hdot F F.uhatAction)).IsCComponent :=
    (show IsComponent (Hdot F F.uhatAction) (solvableResidual (Hdot F F.uhatAction)) from
      ⟨(inferInstance : (solvableResidual (Hdot F F.uhatAction)).Normal).isSubnormal,hR⟩).isCComponent
  obtain ⟨K,hK,hn,hm⟩ := exists_normal_cComponent_map_residual
    (source_H_residual_generation d chosen F) (QuotientGroup.mk' F.uhatAction.ker)
    (QuotientGroup.mk'_surjective _) hC
  refine ⟨K,hn,⟨map_subtype_le K,?_⟩,hm⟩
  simpa only [subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hK

/-- The part of the earlier nonsolvable action rows consumed by 14.3.25.
Every clause concerns the literal faithful quotient, its residual, and the
original conjugate center; none asserts a lifted component or seed exclusion. -/
structure NonsolvableSeedRow (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (g : G) : Prop where
  quasisimple : IsQuasisimple (solvableResidual (Hdot F F.uhatAction))
  irreducible : IsIrreducible
    ((elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)).comp
      (solvableResidual (Hdot F F.uhatAction)).subtype)
  order : Nat.card (solvableResidual (Hdot F F.uhatAction)) = 60 ∨
    Nat.card (solvableResidual (Hdot F F.uhatAction)) = 360 ∨
    Nat.card (solvableResidual (Hdot F F.uhatAction)) = 6048
  marked : Nat.card (solvableResidual (Hdot F F.uhatAction)) = 60 →
    dotImage F F.uhatAction (conjugate F.ZU g) ≤ solvableResidual (Hdot F F.uhatAction) ∧
    Nat.card (dotImage F F.uhatAction (conjugate F.ZU g)) = 2

/-- Construct the normal component, its exact image and all transport premises
needed by the faithful seed exclusion from the earlier dotted row. -/
theorem source_marked_component_of_dotted_row (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L)
    (row : NonsolvableSeedRow F g) :
    ∃ K : Subgroup F.H, K.Normal ∧
      K.map F.H.subtype ∈ Chapter1.cComponentsIn F.H ∧
      IsIrreducible ((elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype) ∧
      (Nat.card (K.map F.uhatAction) = 60 ∨ Nat.card (K.map F.uhatAction) = 360 ∨
        Nat.card (K.map F.uhatAction) = 6048) ∧
      (Nat.card (K.map F.uhatAction) = 60 →
        (F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≤
          K.map F.uhatAction ∧
        Nat.card (F.uhatAction.comp
          (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2) := by
  obtain ⟨K,hn,hK,hm⟩ := source_lift_dotted_residual d chosen F row.quasisimple
  let q := QuotientGroup.mk' F.uhatAction.ker
  let R := solvableResidual (Hdot F F.uhatAction)
  change K.map q = R at hm
  let π : K →* R := (q.comp K.subtype).codRestrict R
    (fun k => show q k ∈ R from hm ▸ mem_map_of_mem q k.property)
  have hπ : Function.Surjective π := by
    intro r
    obtain ⟨k,hk,he⟩ := (show (r : Hdot F F.uhatAction) ∈ K.map q from hm.symm ▸ r.property)
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hi := (irreducible_comp_surjective_iff π hπ
    ((elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)).comp R.subtype)).mpr row.irreducible
  have hρ : (((elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)).comp
      R.subtype).comp π) = (elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype := by
    ext k x
    rfl
  rw [hρ] at hi
  have himage : K.map F.uhatAction = R.map (faithfulAction F F.uhatAction) := by
    rw [←hm,map_map]
    rfl
  have hcard : Nat.card (K.map F.uhatAction) = Nat.card R := by
    rw [himage]
    exact card_map_of_injective (faithfulAction_injective F F.uhatAction)
  refine ⟨K,hn,hK,hi,?_,?_⟩
  · simpa only [hcard] using row.order
  · intro h60
    obtain ⟨hle,hc⟩ := row.marked (hcard.symm.trans h60)
    have hactor : (F.uhatAction.comp
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range =
        (dotImage F F.uhatAction (conjugate F.ZU g)).map (faithfulAction F F.uhatAction) := by
      rw [faithfulAction_dotImage]
      ext a
      constructor
      · rintro ⟨z,rfl⟩
        exact ⟨F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z,z.property,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨z,hz⟩,rfl⟩
    rw [hactor,himage]
    exact ⟨map_mono hle,(card_map_of_injective (faithfulAction_injective F F.uhatAction)).trans hc⟩

/-- The complete nonsolvable seed argument from the earlier marked action row. -/
theorem source_seed_exclusion_of_dotted_row (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat] (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : NonsolvableSeedRow F g) : centralLTSeed F L = ⊥ := by
  obtain ⟨K,hn,hK,hi,ho,hm⟩ := source_marked_component_of_dotted_row d chosen F g hgP row
  let := hn
  exact source_seed_exclusion_of_nonsolvable_rows d earlier hq chosen structural alternatives
    classification F hne g hgP hgH K hK hi ho hm


/-- Apply the lifted-component seed proof to the S5 and A6 branches of the
original centerlessness argument. -/
theorem source_centerless_of_dotted_row_small (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat] (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : NonsolvableSeedRow F g)
    (model : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* alternatingGroup (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  have hs := source_seed_exclusion_of_dotted_row d earlier hq chosen structural alternatives
    classification F hne g hgP hgH row
  rcases model with hS | hA
  · exact source_centerless_of_symmetricFive d earlier hq chosen structural alternatives F hne hs hS
  · exact source_centerless_of_alternatingSix d earlier hq chosen structural alternatives F hne hs hA

/-- The actual LocalStructure application, with the lifted component and seed
exclusion discharged. The independently produced action remains explicit. -/
theorem localStructure_of_dotted_row_small_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat] (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : NonsolvableSeedRow F g)
    (model : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* alternatingGroup (Fin 6)))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_dotted_row_small d earlier hq chosen structural alternatives
      classification F hne g hgP hgH row model) action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
