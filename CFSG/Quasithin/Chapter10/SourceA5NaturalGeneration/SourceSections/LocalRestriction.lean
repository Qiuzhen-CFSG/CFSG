module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import Theory.Representation.BinaryConjugationSection.Restriction
public import Theory.Representation.BinaryConjugationSection.Ambient
public import Theory.GroupTheory.SubgroupTransport

/-!
# The chosen natural section on the original local module

The local moved subgroup is nonzero and fully moved by the original
component. Restrict the full-module natural coordinates to this subgroup.
Transitivity of SL₂ on nonzero vectors makes the restriction surjective;
its kernel is precisely the local fixed subgroup. Thus neither equality of
the full and local modules nor a splitting of their central covers is needed.

Source: Aschbacher–Smith 10.2.3(4), printed p.746, using 3.2.2(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual local moved layer lies in the full moved layer. -/
theorem source_local_moved_le_full : ⁅D.moduleSubgroup,L⁆ ≤ ⁅D.fullModule,L⁆ :=
  commutator_mono (le_componentOrbit D.moduleSubgroup D.maximalLocal) le_rfl

/-- The actual local moved layer is fully moved by the original component. -/
theorem source_local_moved_eq_commutator : ⁅⁅D.moduleSubgroup,L⁆,L⁆ = ⁅D.moduleSubgroup,L⁆ := by
  apply commutator_isPPerfect_idempotent L D.moduleSubgroup D.faithful.1.2.1
    D.module_elementary.isPGroup
  exact (le_componentOrbit L T).trans D.orbit_normalizes_module

/-- The original component acts nontrivially on the local source module. -/
theorem source_local_moved_ne_bot : ⁅D.moduleSubgroup,L⁆ ≠ ⊥ := by
  intro he
  have hLC : L ≤ centralizer (D.moduleSubgroup : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hTC : (T : Subgroup G) ≤ normalizer (centralizer (D.moduleSubgroup : Set G) : Set G) :=
    D.sylow_normalizes_module.trans (normalizer_le_normalizer_centralizer _)
  have hOC : localOrbit T L ≤ centralizer (D.moduleSubgroup : Set G) :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hLC hTC
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hh := D.fullModule_centralizer_eq_module_orbit hu
  rw [inf_eq_left.mpr (le_centralizer_iff.mpr hOC)] at hh
  have hVC : D.fullModule ≤ centralizer (localOrbit T L : Set G) :=
    hh.ge.trans inf_le_right
  exact source_full_moved_ne_bot D
    (commutator_eq_bot_iff_le_centralizer.mpr
      (hVC.trans (centralizer_le (le_componentOrbit L T))))

open scoped MatrixGroups
variable {F : Type*} [Field F] [CharP F 2]
local instance sourceSectionsLocalFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Restrict the chosen full-module natural coordinates to the actual local
moved layer, preserving the original quotient actor and central kernel. -/
def source_original_local_natural_section
    (q : L →* SL(2,F)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D) (Representation.SL2.BinarySmall.natural.comp q)) :
    Representation.BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆
      (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G))
      (Representation.SL2.BinarySmall.natural.comp q) := by
  have hle := source_local_moved_le_full D
  have hnorm : L ≤ normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) :=
    normalizer_commutator_ge_right _ _
  have hnon : ¬ ⁅D.moduleSubgroup,L⁆ ≤ sourceMovedFixed D :=
    Representation.BinaryConjugationSection.not_le_kernel_of_fully_moved
      ⁅D.moduleSubgroup,L⁆ inf_le_right (source_local_moved_ne_bot D)
      (source_local_moved_eq_commutator D)
  have honto := Representation.BinaryConjugationSection.restricted_natural_coordinates_surjective
    q hq c ⁅D.moduleSubgroup,L⁆ hle hnorm hnon
  have he : ⁅D.moduleSubgroup,L⁆ ⊓ sourceMovedFixed D =
      ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G) := by
    change _ ⊓ (_ ⊓ _) = _
    rw [←inf_assoc,inf_eq_left.mpr hle]
  exact (c.restrict ⁅D.moduleSubgroup,L⁆ hle hnorm honto).replaceKernel _ he

/-- The restriction uses exactly the original supplied coordinates. -/
theorem source_original_local_natural_section_coordinates
    (q : L →* SL(2,F)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D) (Representation.SL2.BinarySmall.natural.comp q))
    (v : (⁅D.moduleSubgroup,L⁆ : Subgroup G)) :
    (source_original_local_natural_section D q hq c).coordinates v =
      c.coordinates (inclusion (source_local_moved_le_full D) v) := by
  simp only [source_original_local_natural_section,
    Representation.BinaryConjugationSection.replaceKernel_coordinates,
    Representation.BinaryConjugationSection.restrict_coordinates]

/-- The A₅ consumer retains exactly L → L/O₂(L) → A₅ → SL₂(F). -/
def source_original_a5_local_natural_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D) (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    Representation.BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆
      (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G))
      (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :=
  source_original_local_natural_section D _
    (f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))) c

/-- The same local section is available inside the original local join,
with the original component inclusion and quotient map explicitly retained. -/
def source_original_a5_internal_natural_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D) (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    let X := localJoin T L
    let hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
    Representation.BinaryConjugationSection (L.subgroupOf X)
      ((⁅D.moduleSubgroup,L⁆ : Subgroup G).subgroupOf X)
      ((⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G)).subgroupOf X)
      (Representation.SL2.BinarySmall.natural.comp
        ((f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).comp
          (subgroupOfEquivOfLe hLX).toMonoidHom)) :=
  (source_original_a5_local_natural_section D e f c).subgroupOf (localJoin T L)
    ((le_componentOrbit L T).trans le_sup_left)

/-- The original natural section in the literal internal moved subgroup and
its centralizer kernel, ready for the local block-module comparison. -/
def source_original_a5_internal_moved_natural_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D) (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    let X := localJoin T L
    let A := L.subgroupOf X
    let U := D.moduleSubgroup.subgroupOf X
    let hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
    Representation.BinaryConjugationSection A ⁅U,A⁆
      (⁅U,A⁆ ⊓ centralizer (A : Set X))
      (Representation.SL2.BinarySmall.natural.comp
        ((f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).comp
          (subgroupOfEquivOfLe hLX).toMonoidHom)) := by
  let X := localJoin T L
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hUX : D.moduleSubgroup ≤ X := D.module_le_core.trans (pCoreIn_le 2 X)
  have hm := SubgroupTransport.subgroupOf_commutator D.moduleSubgroup L hUX hLX
  have hk : (centralizer (L : Set G)).subgroupOf X = centralizer (L.subgroupOf X : Set X) := by
    ext x
    constructor
    · intro hx y hy
      exact Subtype.ext (hx y hy)
    · intro hx y hy
      exact congrArg X.subtype (hx ⟨y,hLX hy⟩ hy)
  have cr := source_original_a5_internal_natural_section D e f c
  change Representation.BinaryConjugationSection (L.subgroupOf X)
    ((⁅D.moduleSubgroup,L⁆ : Subgroup G).subgroupOf X)
    (((⁅D.moduleSubgroup,L⁆ : Subgroup G).subgroupOf X) ⊓
      (centralizer (L : Set G)).subgroupOf X) _ at cr
  rw [hm,hk] at cr
  exact cr

end CFSG.Quasithin.Chapter10
