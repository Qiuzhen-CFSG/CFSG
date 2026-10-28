module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.MarkedTransport
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Ratios
public import Theory.Representation.BinaryOffender.SectionOffender

/-!
# The offender plane in B.5.7

This module performs the last module calculation in the high-three-rank
branch.  The source-specific permutation estimates are kept as explicit
inputs: the S₇ estimate is the ratio-one/B.1.5(8) span conclusion, while the
S₆ estimate is the genuine offender upper bound on the original cubic moved
space.  The calculation below proves the consequences on the literal
subgroups and spaces in `G`; in particular, it does not replace the original
three-core by a cyclic tag or split off a global fixed space.

The retained marking is the one carried by `m.sectionData.space` and by the
embedded component `L.subgroupOf (L ⊔ A)`.  Thus the final equivalence with
`A₆` is the actual component equivalence used by the subsequent centralizer
assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, B.5.7,
printed pp.105--106, especially the ratio-one paragraph and the final
paragraph on p.106.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable {K : GroupClass.{u}}
variable (ρ : Representation (ZMod 2) G V)

/-! The source-specific estimates consumed by the endgame. -/

/-- The numerical and span conclusions needed from the earlier offender
calculation.  The first two fields retain the exceptional source facts
`rank A = 3` and codimension two on the component moved space.  `seven_span`
is the full ratio-one/B.1.5(8) conclusion used below.  The cubic
fixed-codimension and `plane_bound` fields are the two genuine A₆ offender
estimates; the exact plane dimension is proved here from them. -/
structure OffenderPlaneBounds {L A : Subgroup G}
    (m : SymmetricMovedModel ρ L A) where
  rank_eq : IsBestOffender ρ A → rank A = 3
  component_fixedCodim_eq :
    IsBestOffender ρ A →
    fixedCodim m.sectionData.space.toRepresentation
      (A.subgroupOf (L ⊔ A)) = 2
  seven_span :
    IsBestOffender ρ A →
    ∀ (_e : MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 7))
      (alternatingGroup (Fin 7))),
      moved ρ (L ⊔ pCore 3 G) ≤ moved ρ L ⊔ fixedSpace ρ A
  cubic_fixedCodim_eq :
    IsBestOffender ρ A →
      fixedCodim (normalMoved ρ (pCore 3 G)).toRepresentation A = 2
  plane_bound :
    IsBestOffender ρ A →
      Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) ≤ 2

/-! A linear transport lemma for the S₇ span.  It is the point where the
source's equality case is converted into fixation of the original odd-core
moved space. -/

omit [Finite G] in
theorem moved_threeCore_fixed_of_span {L A : Subgroup G}
    [L.Normal]
    (hsum : moved ρ (L ⊔ pCore 3 G) =
      moved ρ L ⊔ moved ρ (pCore 3 G))
    (hdisj : Disjoint (moved ρ L) (moved ρ (pCore 3 G)))
    (hspan : moved ρ (L ⊔ pCore 3 G) ≤ moved ρ L ⊔ fixedSpace ρ A) :
    moved ρ (pCore 3 G) ≤ fixedSpace ρ A := by
  intro w hw a
  have hwH : w ∈ moved ρ (L ⊔ pCore 3 G) := by
    rw [hsum]
    exact Submodule.mem_sup_right hw
  obtain ⟨u, hu, f, hf, hwu⟩ := Submodule.mem_sup.mp (hspan hwH)
  have hUstable : ρ a u ∈ moved ρ L := by
    exact (normalMoved ρ L).apply_mem_toSubmodule a hu
  have hWstable : ρ a w - w ∈ moved ρ (pCore 3 G) := by
    have hstable := (normalMoved ρ (pCore 3 G)).apply_mem_toSubmodule a hw
    exact (moved ρ (pCore 3 G)).sub_mem hstable hw
  have hf' : ρ a f = f := hf a
  have hUdiff : ρ a w - w ∈ moved ρ L := by
    rw [← hwu, map_add, hf']
    simpa only [add_sub_add_right_eq_sub] using
      (moved ρ L).sub_mem hUstable hu
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hdisj _ hUdiff hWstable)

/-! The complete output of the offender endgame. -/

structure OffenderPlaneConclusion {L A : Subgroup G}
    (d : NoncentralContext K G L) (m : SymmetricMovedModel ρ L A) where
  marking :
    Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) ∨
    Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.coreRepresentation (Fin 6))
      (alternatingGroup (Fin 6)))
  componentEquiv : Nonempty (L ≃* alternatingGroup (Fin 6))
  plane : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2
  threeCoreEquiv : Nonempty (pCore 3 G ≃* Multiplicative (ZMod 3))
  rank_eq : rank A = 3
  component_fixedCodim_eq :
    fixedCodim m.sectionData.space.toRepresentation
      (A.subgroupOf (L ⊔ A)) = 2

/-- Choose the actual component equivalence carried by a completed endgame. -/
noncomputable def componentEquivOfConclusion {L A : Subgroup G}
    {d : NoncentralContext K G L} {m : SymmetricMovedModel ρ L A}
    (c : OffenderPlaneConclusion ρ d m) : L ≃* alternatingGroup (Fin 6) :=
  Classical.choice c.componentEquiv

/-- Choose the actual cyclic equivalence produced by `threeCoreEquiv_of_plane`.
-/
noncomputable def threeCoreEquivOfConclusion {L A : Subgroup G}
    {d : NoncentralContext K G L} {m : SymmetricMovedModel ρ L A}
    (c : OffenderPlaneConclusion ρ d m) :
    pCore 3 G ≃* Multiplicative (ZMod 3) :=
  Classical.choice c.threeCoreEquiv

/-! The component equivalence extracted from a surviving marking. -/

private noncomputable def componentEquivOfNaturalSix {L A : Subgroup G}
    (m : SymmetricMovedModel ρ L A)
    (e : MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) : L ≃* alternatingGroup (Fin 6) :=
  (subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv

private noncomputable def componentEquivOfCoreSix {L A : Subgroup G}
    (m : SymmetricMovedModel ρ L A)
    (e : MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.coreRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) : L ≃* alternatingGroup (Fin 6) :=
  (subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv

/-! The S₇ branch is impossible, and the two-dimensional moved plane follows
from the noncentral offender and the A₆ upper bound. -/
theorem offender_plane
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hfix : moved ρ L ≤ fixedSpace ρ (pCore 3 G))
    (m : SymmetricMovedModel ρ L A)
    (bounds : OffenderPlaneBounds ρ m) :
    OffenderPlaneConclusion ρ d m := by
  let : L.Normal := d.normal
  let := hyp.finite_module
  have hdec := threeCore_moved_decomposition ρ hL d hfix
  have hseven (e : MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 7))
    (alternatingGroup (Fin 7))) : False := by
    have hW := moved_threeCore_fixed_of_span ρ hdec.1 hdec.2.1
      (bounds.seven_span hA e)
    exact hm (centralizes_of_fixes_odd_moved ρ hyp.faithful _ threeCore_odd A hW)
  have hcubic := fixedCodim_add_finrank
    (normalMoved ρ (pCore 3 G)).toRepresentation A
  rw [bounds.cubic_fixedCodim_eq hA] at hcubic
  change 2 + _ = Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) at hcubic
  have hplane_lower : 2 ≤ Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) := by
    omega
  have hplane : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2 := by
    exact Nat.le_antisymm (bounds.plane_bound hA) hplane_lower
  have hthree := threeCoreEquiv_of_plane ρ hyp d hplane
  cases m.action with
  | natural n hn e =>
      rcases hn with rfl | rfl
      · refine {
          marking := Or.inl ⟨e⟩
          componentEquiv := ⟨componentEquivOfNaturalSix ρ m e⟩
          plane := hplane
          threeCoreEquiv := ⟨hthree⟩
          rank_eq := bounds.rank_eq hA
          component_fixedCodim_eq := bounds.component_fixedCodim_eq hA }
      · exact (hseven e).elim
  | coreSix e =>
      refine {
        marking := Or.inr ⟨e⟩
        componentEquiv := ⟨componentEquivOfCoreSix ρ m e⟩
        plane := hplane
        threeCoreEquiv := ⟨hthree⟩
        rank_eq := bounds.rank_eq hA
        component_fixedCodim_eq := bounds.component_fixedCodim_eq hA }

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
