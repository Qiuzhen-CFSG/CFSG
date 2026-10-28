module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockRecognition
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityCentralizers
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups

/-!
# The literal natural block used by 12.2.25

The chosen subgroup `V` is identified with the actual commutator layer
`[O₂(L),L]`.  Consequently the intrinsic block quotient
`blockU L / C_{blockU L}(L)` is transported through the ambient inclusion to
`V`; the natural marking in `NaturalLocalAnalysis` then gives the same
quotient actor and the same conjugation formula.  The resulting
`BlockModuleModel` is the literal model consumed by the dimension branches.

No cocycle, complement, self-normalization, or core equality is assumed here.
The cocycle and fixed-space interfaces below retain the original subgroup and
quotient maps, so downstream centralizer arguments cannot replace them by an
abstract action.

Source: Aschbacher--Smith, 12.2.24--25, printed pp.804--805, and C.1.7.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

namespace LiteralNaturalBlock

omit [Finite G] in
set_option linter.unusedVariables false in
/-- The chosen module is the literal commutator layer of the component. -/
theorem blockLayer_eq [Finite G]
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    (ChapterC.blockU L).map L.subtype = V := by
  have hV : V ≤ (ChapterC.blockU L).map L.subtype := by
    rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl)
  let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  have hVi : V.subgroupOf L ≤ ChapterC.blockU L := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hV hx
    exact (Subtype.ext he : y = x) ▸ hy
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy C.block.2.1
    (V.subgroupOf L) hVi with hc | he
  · have hv : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      exact congrArg Subtype.val (mem_center_iff.mp
        (hc (show (⟨v, D.le_component hv⟩ : L) ∈ V.subgroupOf L from hv)) ⟨l, hl⟩)
    exact (D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hv))).elim
  · have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le D.le_component] at hm
    exact hm.symm

/-- The component commutator is the chosen subgroup. -/
theorem component_commutator_eq
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ⁅L.pCoreIn 2, L⁆ = V := by
  have hh := blockLayer_eq D A C
  rwa [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hh

/-- The fixed part of the intrinsic block layer is trivial. -/
theorem blockFixed_eq_bot
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ChapterC.blockFixed L = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  apply Subtype.ext
  apply mem_bot.mp
  rw [← A.fixed_eq_bot D]
  refine ⟨(blockLayer_eq D A C) ▸ mem_map_of_mem L.subtype x.property, ?_⟩
  intro l hl
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨l, hl⟩)

/-- The subgroup called `Q` in the proof of 12.2.25 is retained literally.
It is the Sylow centralizer of the chosen module, hence the two-core of the
local join.  This equality is relative to `L ⊔ T`; no ambient normality is
used. -/
theorem kernel_eq_local_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← blockLayer_eq D A C]
  exact C.block.2.1.sylow_centralizer_blockU_eq_pCoreIn
    D.sylow_normalizes_component

omit [Finite G] in
set_option linter.unusedVariables false in
/-- The fixed-space premise is the original fixed-space equality on `V`. -/
theorem chosen_fixed_eq_bot [Finite G]
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    V ⊓ centralizer (L : Set G) = ⊥ :=
  A.fixed_eq_bot D

/-- The literal multiplicative equivalence from the intrinsic block module to V. -/
def moduleEquiv
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ChapterC.BlockModule L ≃* V :=
  ((QuotientGroup.quotientMulEquivOfEq (blockFixed_eq_bot D A C)).trans
    QuotientGroup.quotientBot).trans
    ((equivMapOfInjective (ChapterC.blockU L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr (blockLayer_eq D A C)))

/-- The quotient equivalence has its original ambient representative formula. -/
theorem moduleEquiv_mk
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (x : ChapterC.blockU L) :
    moduleEquiv D A C (QuotientGroup.mk' (ChapterC.blockFixed L) x) =
      (⟨(x : L), (blockLayer_eq D A C) ▸ mem_map_of_mem L.subtype x.property⟩ : V) := rfl

set_option linter.unusedVariables false in
/-- The exact quotient and action model on the original V. -/
theorem literal_block_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (hnone : NoEscape L V)
    (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ∃ m : ChapterC.BlockModuleModel L (binaryNaturalAut d),
      (m.moduleIso : ChapterC.BlockModule L ≃* Multiplicative (Fin d → ZMod 2)) =
        (moduleEquiv D A C).trans (A.natural.choose_spec.choose) ∧
      m.quotientIso = A.natural.choose ∧
      ∀ (l : L) (x : ChapterC.blockU L),
        m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L)
          (ChapterC.blockConjugate L l x)) =
          binaryNaturalAut d (A.natural.choose (QuotientGroup.mk' (pCore 2 L) l))
            (m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) x)) := by
  let e := A.natural.choose
  let f := A.natural.choose_spec.choose
  let b := moduleEquiv D A C
  let m : ChapterC.BlockModuleModel L (binaryNaturalAut d) := {
    quotientIso := e
    moduleIso := b.trans f
    intertwining := by
      intro l x
      change f (b (QuotientGroup.mk' (ChapterC.blockFixed L)
        (ChapterC.blockConjugate L l x))) =
        binaryNaturalAut d (e (QuotientGroup.mk' (pCore 2 L) l))
          (f (b (QuotientGroup.mk' (ChapterC.blockFixed L) x)))
      rw [moduleEquiv_mk]
      change f (⟨(l : G) * (x : G) * (l : G)⁻¹, _⟩) = _
      apply f.symm.injective
      apply Subtype.ext
      rw [f.symm_apply_apply]
      exact (A.natural.choose_spec.choose_spec l
        (b (QuotientGroup.mk' (ChapterC.blockFixed L) x))).symm }
  refine ⟨m, rfl, rfl, ?_⟩
  intro l x
  exact m.intertwining l x

end LiteralNaturalBlock

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
