module
public import CFSG.Quasithin.Chapter10.SourceA5PointScalarBranches
public import CFSG.Quasithin.Chapter10.SourceA5PointSelectedModels.Cohomology
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion

/-!
# The two alternating-seven point-action models

The literal source selector retains both alternating-seven irreducibility
records. The four scalar alternatives are excluded by cubic movement on the
original point-action module. This leaves the original four-dimensional or
marked deleted-seven action on precisely the chosen B.5.1 moved section.
Full movement and the full source conclusion remain available to the final
point-component inspection. Source: Aschbacher–Smith 10.2.9, pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource

/-- The two remaining models retain their original cohomology hypotheses. -/
inductive SourceA5PointA7Model
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {C : Subgroup G}
    (s : MovedSection ρ C) : Prop
  | four (irreducible : ExtensionConsequences.IrreducibleAlternative C s)
      (actor : C ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2)
        (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
  | deleted (irreducible : ExtensionConsequences.IrreducibleAlternative C s)
      (action : MarkedActionEquiv s.action (offenderSubgroup s.action) C
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual partner point has only the two A7 action rows. All normalizer,
Thompson, local-section, fixed-span and scalar-exclusion premises are discharged. -/
theorem source_a5_point_a7_models_of_partner
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I) (hout : ¬ I ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    ∃ hr : IsPReduced 2 U, letI := hr.normal; letI := hr.elementary
      let A := (I.subgroupOf H).map (actionMk U)
      let N := offenderSubgroup (action U)
      ∃ _hAN : A ≤ N, moved (action U) A = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action U).comp N.subtype) (A.subgroupOf N),
        SourceA5PointA7Model h.sectionData := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hNL := source_a5_component_normalizer_le D e hn
  have hNW := source_a5_moved_normalizer_le D e ht htn hcross
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hNW
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D ht htn hcross))
  obtain ⟨hr,hAN,h,hcases⟩ := source_a5_point_six_way_irreducible_models_of_partner
    D e hi hn ht hcross hv hvne I hLI hIX hI hNI hnot hout hCW hs
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
  let := hr.normal
  let := hr.elementary
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hmapV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := hmapV ▸ map_mono hWV hv
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu hvV
  have hspan := source_a5_escaping_point_component_fixed_span_contains D e hi hn hvT hvne
    (hcross hv) (fun hc => hout (hIX.trans hc)) I hLI
  have hfull := source_a5_point_action_fully_moved D I hLI hout hCW hspan hr
  obtain ⟨hBp,⟨eB⟩,R,hR,hlocal⟩ := source_a5_point_small_image_local_data
    D e I hLI hIX hI hNI hout hCW hs hspan hr
  have hscalar := source_a5_point_no_scalar_model D e hn ht htn hcross hsep hNL
    I hLI hIX hI hout hCW hspan hr hAN hfull hBp.ne eB R hR hlocal h.sectionData
  refine ⟨hr,hAN,hfull,h,?_⟩
  cases hcases with
  | linearThree F _ action => exact (hscalar (.linear F action)).elim
  | doubleThree F action => exact (hscalar (.repeated F action)).elim
  | symplectic F large _ action => exact (hscalar (.symplectic F large action)).elim
  | g2 F large _ action => exact (hscalar (.g2 F large action)).elim
  | alternatingSevenFour irreducible actor dimension => exact .four irreducible actor dimension
  | alternatingSevenDeleted irreducible action => exact .deleted irreducible action

end CFSG.Quasithin.Chapter10
