module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Source

/-!
# Assembly of the selected non-A₅ point-Sylow argument

The selected minimal module is retained throughout. Thompson centralization
uses the already proved fixed-layer vanishing theorem. In the moving branch,
rank-one Baumann orbits or the binary-three omega-center geometry control
the actual Sylow normalizer. Half-Sylow uniqueness excludes every escaping
fixed vector and supplies the original component normalizer containment.

The three source geometry contracts remain explicit and are not proved by
this conditional assembly. The final theorem below passes its selection
result to the parent's actual point-centralizer consumer, retaining that
consumer's independently owned uniqueness and component-exclusion premises.
Source: Aschbacher--Smith, 10.1.1--2 and 10.2.8--9, pp.741--742,749--750.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The binary-three point geometry controls the original Sylow normalizer,
including the positive fixed-layer exception of 10.2.8. -/
theorem pointSylowControl_of_binaryThree_geometry
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hgeometry : BinaryThreePointGeometry D t) : PointSylowControl D t := by
  intro v hv hvne hout hs
  obtain ⟨hv0,hstab⟩ := escaping_point_stabilizes D hhalf hgeometry.fixed_layer
    ht htn hcross hv hvne hout
  refine ⟨?_,hstab⟩
  rcases hgeometry.points v hv hvne hv0 hs with ⟨he,hN⟩ | ⟨hd,hZ,hr⟩
  · change normalizer (↑((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G) ≤
      D.maximalLocal
    rw [he]
    exact hN
  · have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
    have hvT := D.fullModule_le_sylow hu (partner_le_fullModule D ht hv)
    have hZle : omegaCenterIn (T : Subgroup G) ≤
        omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) := by
      intro z hz
      obtain ⟨hzT,hzc,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
      exact (mem_omegaCenterIn_iff _ _).mpr
        ⟨⟨hzT,mem_centralizer_singleton_iff.mpr (hzc v hvT).symm⟩,
          centralizer_le inf_le_left hzc,hz2⟩
    exact point_normalizer_le_of_omega_residual D (fun hn => htn (hn ht))
      hhalf hd hZ v hZle hr

omit D in
/-- The three independent geometry producers imply the exact selection
contract. Half-Sylow uniqueness remains conditional as required. -/
theorem selectionAt_of_source_geometry
    (hchoice : ModuleChoiceAt T)
    (hrankOne : RankOneGeometryAt T)
    (hthree : BinaryThreeGeometryAt T) : SelectionAt T := by
  intro hmany L hL hf hq hn hnotA5
  obtain ⟨D,hD,t,ht,htn,hcross,hcases⟩ := hchoice hmany L hL hf hq hn hnotA5
  refine ⟨D,hD,t,ht,htn,hcross,?_⟩
  intro hhalf
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)
  · exact pointSylowControl_of_thompson_centralizes D hmany ht htn hcross hJ
  obtain ⟨heq,hmodel⟩ := hcases.resolve_left hJ
  rcases hmodel with hmodel | hmodel
  · have hgeometry := hrankOne hmany L D hD heq hnotA5 hmodel hJ t ht htn hcross hhalf
    exact pointSylowControl_of_baumann_orbits D hhalf hgeometry.fixed_layer
      ht htn hcross hgeometry.baumann_normalizer hgeometry.fixed_orbits
  · exact pointSylowControl_of_binaryThree_geometry D hhalf ht htn hcross
      (hthree hmany L D hD heq hnotA5 hmodel hJ t ht htn hcross hhalf)

omit D in
/-- Actual application to the parent's point-centralizer assembly. The
remaining source contracts must be discharged by their respective owners. -/
theorem source_nonnormalPointControl_of_selection_geometry
    (hchoice : ModuleChoiceAt T)
    (hrankOne : RankOneGeometryAt T)
    (hthree : BinaryThreeGeometryAt T)
    (hhalf : HalfSylowUniqueAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hconstrained : ConstrainedExclusionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf
    (selectionAt_of_source_geometry hchoice hrankOne hthree) hquasi hconstrained

end CFSG.Quasithin.Chapter10.PointControl.Selection
