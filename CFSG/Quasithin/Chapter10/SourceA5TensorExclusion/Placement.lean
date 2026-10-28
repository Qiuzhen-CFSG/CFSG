module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.PlaneTerminal
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import Theory.Representation.OrthogonalFourPlusMatrix.FirstCohomology
public import Theory.Representation.BinaryConjugationSection.FixedPointFree
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# Placement of the original tensor module in its first component

A fixed-point-free first-factor matrix lifts to the original component L.
The original section coordinates therefore give V=[V,L]. The source
commutator containment puts V inside L; normalization and elementary
abelianness put it inside O₂(L). Every surjection from L to the actual
symplectic plane-local model sends V into its radical.

The terminal consumer consequently requires neither a separate placement
hypothesis nor a radical-image hypothesis. Its remaining inputs are the
marked original parabolic and natural quotient, and the containing block
module and component from source9.3.
Source: Aschbacher--Smith9.3, printed pp.732--735.
-/

public section
open Matrix Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m

/-- The first factor moves the entire original tensor module. -/
theorem fullModule_eq_component_commutator : D.fullModule = ⁅D.fullModule, L⁆ := by
  obtain ⟨a, ha⟩ := Binary.exists_left_fixedPointFree
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L)
    (e.symm (m.firstMarking.symm a))
  let t : localOrbit T L := ⟨l, le_componentOrbit L T l.property⟩
  have ht : m.quotient t = (a, 1) := by
    rw [m.first_factor l, hl]
    simp
  have hh := m.sectionData.section_eq_commutator_sup_of_fixedPointFree L
    (le_componentOrbit L T) t l.property (fun v hv => ha v (by
      change Binary.action (m.quotient t) v = v at hv
      rwa [ht] at hv))
  simpa only [sup_bot_eq] using hh

/-- The original tensor module is contained in its original first component. -/
theorem fullModule_le_component : D.fullModule ≤ L :=
  m.fullModule_eq_component_commutator ▸ source_full_moved_le_component D

omit m in
/-- The original component normalizes the original full-module intersection. -/
theorem fullModule_component_normal : (D.fullModule.subgroupOf L).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)

/-- The original tensor module lies in the ambient image of the component two-core. -/
theorem fullModule_le_component_core : D.fullModule ≤ L.pCoreIn 2 :=
  le_pCoreIn_of_normalizes m.fullModule_elementary.isPGroup m.fullModule_le_component
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)

/-- A marked plane quotient sends the original module into the literal radical. -/
theorem original_plane_radical_image
    (q : L →* planeLocal (F := Binary.F)) (hq : Function.Surjective q) :
    (D.fullModule.subgroupOf L).map q ≤ Plane.radical := by
  let : (D.fullModule.subgroupOf L).Normal := fullModule_component_normal (D := D)
  have hN : ((D.fullModule.subgroupOf L).map q).Normal :=
    (inferInstance : (D.fullModule.subgroupOf L).Normal).map q hq
  have hp : IsPGroup 2 (D.fullModule.subgroupOf L) :=
    m.fullModule_elementary.isPGroup.comap_of_injective L.subtype L.subtype_injective
  have hh : (D.fullModule.subgroupOf L).map q ≤ pCore 2 (planeLocal (F := Binary.F)) :=
    le_sSup ⟨hN, hp.map q⟩
  rw [planeLocal_core_eq (n := 2) (by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    norm_num) (by decide)] at hh
  exact hh


/-- The original component version has no separate placement or radical-image premise. -/
theorem false_of_original_plane_radical
    (U K : Subgroup G)
    (q : L →* planeLocal (F := Binary.F)) (hq : Function.Surjective q)
    (hk : q.ker = U.subgroupOf L)
    (p : D.fullModule.subgroupOf L →* Multiplicative (Fin 2 → Binary.F))
    (hp : Function.Surjective p)
    (hpk : p.ker ≤ (U.subgroupOf L).comap (D.fullModule.subgroupOf L).subtype)
    (he : letI := fullModule_component_normal (D := D)
      ∀ (g : L) (v : D.fullModule.subgroupOf L),
      p (MulAut.conjNormal g v) =
        Multiplicative.ofAdd ((Plane.quotientMap (q g)).val *ᵥ (p v).toAdd))
    (hU : Nat.card U = 256)
    (hK : K ≤ normalizer (U : Set G)) (hKM : ¬ K ≤ D.maximalLocal) : False := by
  let : (D.fullModule.subgroupOf L).Normal := fullModule_component_normal (D := D)
  exact m.false_of_plane_radical L U K m.fullModule_le_component q hq hk p hp hpk
    (m.original_plane_radical_image q hq) he hU hK hKM

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
