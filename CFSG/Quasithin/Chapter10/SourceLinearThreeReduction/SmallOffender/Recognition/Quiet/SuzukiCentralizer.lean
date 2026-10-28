module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.FamilySelection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.ThompsonCentralizer

/-!
# The nonsolvable centralizer required by a quiet Suzuki small offender

The degree and TI arguments force a quiet Suzuki small offender to move the
whole full module and force Thompson to move it. Local Thompson still fixes
the original local module. Its nontrivial image supplies an actual FF-offender
in the centralizer of the component-orbit image. The solvable FF theorem and
the fixed-free perfect orbit exclude solvability of this centralizer.

The final theorem retains only this nonsolvable FF centralizer branch in the
literal original small-offender consumer. Its exclusion and final assembly
remain with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains producer
qt-d-10-nona5-half-sylow-unique and final discharge by
qt-d-10-nona5-point-control. No classification of the remaining nonsolvable
centralizer is asserted. Source: Aschbacher--Smith B.1.8, 10.1.1--2 and
10.2.12, printed pp.70,741--742,754--755.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The surviving Suzuki configuration has a genuine nonsolvable FF action
of the literal orbit centralizer on the original full module. -/
theorem quiet_suzuki_orbit_centralizer_nonsolvable_ff
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
    ¬ Group.IsSolvable C ∧
      IsFFModule ((ChapterB.InternalThompsonAction.action U).comp C.subtype) := by
  have hmove := quiet_suzuki_full_thompson_moves D c hJ hNL hm e
  exact ⟨full_orbit_centralizer_not_solvable_of_local_quiet D c.many c.nonnormal hJ hmove,
    full_orbit_centralizer_ff_of_local_quiet D c.nonnormal hJ hmove⟩

/-- The original contract is reduced to a fully moved Suzuki module with
nonsolvable FF orbit centralizer; the solvable centralizer branch is discharged. -/
theorem nonnormalSmallOffender_or_quiet_suzuki_nonsolvable
    (hhalf : PointControl.HalfSylowUniqueAt T) :
    SourceNonnormalSmallOffenderAt T ∨
    (∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) ∧
      normalizer (L : Set G) ≤ D.maximalLocal ∧
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) ∧
        ⁅D.fullModule,L⁆ = D.fullModule ∧
        D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∧
        (let U := D.fullModule.subgroupOf D.maximalLocal
         let := (source_full_module_reduced D).normal
         let := (source_full_module_reduced D).elementary
         let q := ChapterB.InternalThompsonAction.actionMk U
         let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
         let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
         ¬ Group.IsSolvable C ∧
           IsFFModule ((ChapterB.InternalThompsonAction.action U).comp C.subtype))) := by
  rcases nonnormalSmallOffender_or_quiet_suzuki hhalf with hs | h
  · exact Or.inl hs
  obtain ⟨L,D,g,c,hJ,hNL,m,hm,he,hfull,hfixed,hmove⟩ := h
  exact Or.inr ⟨L,D,g,c,hJ,hNL,m,hm,he,hfull,hfixed,hmove,
    quiet_suzuki_orbit_centralizer_nonsolvable_ff D c hJ hNL hm he.some⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
