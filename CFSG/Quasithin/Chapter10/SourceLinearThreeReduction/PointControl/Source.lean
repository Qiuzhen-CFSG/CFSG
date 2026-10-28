module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Thompson
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion

/-!
# Assembly of the non-A₅ point-centralizer argument

A saturated escaping point of the opposite moved factor has a Sylow
centralizer in G once its normalizer is controlled. Source 1.2.4 then
constructs a normal C-component containing L. Half-Sylow uniqueness makes
that containment strict and the containing component escapes M. For a
nonquasisimple component, the odd-core argument and B.2.14 construct the
literal reduced module used by the source FF argument.

The two component exclusions therefore control every saturated point.
Conjugation inside M and the original two-factor permutation transfer
control to every nonidentity element of [V,L], including fixed vectors.
The selected minimal setup is retained unchanged.

The earlier half-Sylow uniqueness, chosen-module preparation, and the two
component exclusions remain explicit source obligations. This conditional
assembly is not an unconditional proof of 10.2.9. Source: Aschbacher--Smith,
10.2.6--9, printed pp.748--753 (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual enlarged-component consumer of the half-Sylow and
point-normalizer source steps. No nonfixed-vector restriction is added. -/
theorem escapingComponent_of_local_sylow
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hhalf : HalfSylowUnique D) (hpoint : PointSylowControl D t)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hsM : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    ∃ I : Subgroup G, EscapingComponent D t v I := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hNL := component_normalizer_le_of_halfSylowUnique D hn hhalf
  have hNW := moved_normalizer_le_of_halfSylowUnique D hn hhalf
  have hvV := partner_le_fullModule D ht hv
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  obtain ⟨hN,hstab⟩ := hpoint v hv hvne hout hsM
  have hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) :=
    exists_sylow_eq_of_relative_normalizer_le hsM inf_le_right
      (le_inf (inf_le_right.trans hN) inf_le_left)
  obtain ⟨I,hLI,hIX,hI,hNI⟩ := source_element_containing_component_of_sylow D
    (D.fullModule_le_sylow hu hvV) hvne (hcross hv) hs hstab
  obtain ⟨hlt,hIM⟩ := source_element_containing_component_escape D hNL hout hLI hIX hI hNI
  exact ⟨I,⟨ht,htn,hcross,hv,hvne,
    (fun hfix => hout (fixed_element_centralizer_le_of_halfSylowUnique D hhalf hvV hvne hfix)),
    hhalf,hs,hN,hstab,hNL,hNW,hlt,hIX,hI,hNI,hIM,
    source_containing_component_normal_generation D hLI hIX hI⟩⟩

omit D in
/-- The exact public point-control contract follows from four independent
source steps. All vector conjugation, component construction, relative
normality and constrained reduced-module inputs are discharged here. -/
theorem source_nonnormalPointControl_of_sourceSteps
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T := by
  intro hmany L hL hf hq hn hnotA5
  obtain ⟨D,hD,t,ht,htn,hcross,hpoint⟩ := hselect hmany L hL hf hq hn hnotA5
  have hU := hhalf hmany L D hn hnotA5
  refine ⟨D,hD,?_⟩
  apply source_a5_moved_point_control_of_partner_saturated D hn ht htn
  intro v hv hvne hsM
  by_contra hout
  obtain ⟨I,C⟩ := escapingComponent_of_local_sylow D ht htn hcross hU (hpoint hU)
    hv hvne hsM hout
  by_cases hI : IsQuasisimple I
  · exact hquasi hmany L D hD hnotA5 t v I C hI
  · have hvV := partner_le_fullModule D ht hv
    have hCW := (Subgroup.centralizer_le_normalizer _).trans C.moved_normalizer
    exact hconstrained hmany L D hD hnotA5 t v I C hI
      (source_a5_point_component_characteristicTwo D hvV hvne (hcross hv) hCW I
        C.le_centralizer C.component hI)
      (source_a5_point_component_reduced_module D hvV hvne (hcross hv) hCW I C.strict.le
        C.le_centralizer C.component C.normalizes hI C.sylow)

end CFSG.Quasithin.Chapter10.PointControl
