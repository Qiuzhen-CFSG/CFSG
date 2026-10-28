module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingBlock.Quotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Seed
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Excluding an A₅ block using the actual seed constituent

An A₅ block initially supplies coordinates only on U(K)/C_U(K). The literal
moving space is a full commutator space by the short-group two-residual
condition, so its irreducible quotient makes it a member of Irr⁺. Vanishing
of H¹ for the A₅ permutation module and its dual splits this central
extension. Thus the whole moving space, not merely its quotient, is the
permutation module.

The source identities for [W_K,K] and [⟨z^K⟩,K] put this constituent inside
the literal seedSpace. The exact 13.6.15 exclusion then rules out the A₅
block alternative in 13.6.18. The earlier exclusion and trivial two-core
conclusion remain explicit inputs; block subnormality is only relative to KTᵥ.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7–13,
printed pp.123–124, and 13.6.15, 13.6.18, pp.930–931 (PDF pp.947–948).
-/

public section
open Subgroup Representation Representation.BinaryOffender OneCohomology
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection ComponentElimination.SourceTransferFields.RankOneBorel
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
local notation "W" => WK K L T z v
local notation "Kp" => plusImage K L T z v hL hz K
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v
local notation "C" => Submodule.comap (Submodule.subtype D) (Representation.invariants ρ)

namespace AlternatingBlock

private noncomputable def movedSection : MovedSection ρ (⊤ : Subgroup Kp) where
  space := Replacement.Action.movingSubrepresentation K L T z v hL hz
  space_eq := by
    change movingSpace K L T z v = moved ρ (⊤ : Subgroup Kp)
    rw [Replacement.Action.movingSpace_eq_subspaceCommutator]

  central := Replacement.Action.fixedInMoving K L T z v hL hz
  central_eq := by
    change C = fixedSpace (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation (⊤ : Subgroup Kp)
    rw [fixedSpace_top]
    ext x
    change (∀ a, ρ a (x : Additive W) = (x : Additive W)) ↔
      ∀ a, (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation a x = x
    constructor
    · intro h a
      apply Subtype.ext
      exact h a
    · intro h a
      exact congrArg Subtype.val (h a)

/-- The short-group two-residual condition gives full commutator generation. -/
theorem movingSpace_full (hs : IsShort K) : subspaceCommutator ρ D ⊤ = D := by
  have hn : K ≤ normalizer (W : Set G) :=
    (K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz)
  have hm : ⁅W, K⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hn
  have hg : ⁅⁅W, K⁆, K⁆ = ⁅W, K⁆ :=
    commutator_isPPerfect_idempotent K W hs.twoPerfect
      (IsElementaryAbelian.isPGroup 2 W) hn
  let S := subspaceCommutator ρ D ⊤
  have hc : ⁅⁅W, K⁆, K⁆ ≤ S.toAddSubgroup.toSubgroup'.map (W).subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk w hw
    let a : Kp := componentMap K L T z v hL hz ⟨k, hk⟩
    let x : Additive W := Additive.ofMul ⟨w, hm hw⟩
    let d := ρ a x - x
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ S
      exact Submodule.subset_span ⟨a, mem_top a, x, hw, rfl⟩
    · change (((ρ a x).toMul : W) : G) / w = _
      rw [componentRepresentation_mk, div_eq_mul_inv]
      rfl
  rw [hg] at hc
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, _, w, hw, rfl⟩
    exact (D).sub_mem (Replacement.Action.movingSpace_invariant K L T z v hL hz a ⟨w, hw⟩) hw
  · intro w hw
    obtain ⟨d, hd, he⟩ := hc hw
    have hdw : Additive.ofMul d = w := congrArg Additive.ofMul (Subtype.ext he)
    exact hdw ▸ hd

/-- Quotient coordinates and full generation establish the exact Irr⁺ condition. -/
theorem movingSpace_isIrrPlus (hs : IsShort K)
    (e : ActionEquiv (Replacement.Action.sectionRepresentation K L T z v hL hz)
      (alternatingNatural 5)) : IsIrrPlus ρ ⊤ D := by
  have hstab : (⊤ : Subgroup Kp) ≤ subspaceStabilizer ρ D := by
    apply le_subspaceStabilizer
    intro a _ w hw
    exact Replacement.Action.movingSpace_invariant K L T z v hL hz a ⟨w, hw⟩
  refine ⟨hstab, movingSpace_full K L T z v hL hz hs, ?_⟩
  have he : (fixedSpace ρ (⊤ : Subgroup Kp)).comap (D).subtype = C := by
    rw [fixedSpace_top]
  let q := Submodule.quotEquivOfEq _ _ he
  let a : ActionEquiv (centralQuotientRepresentation ρ ⊤ D hstab)
      (alternatingNatural 5) := {
    groupEquiv := (Subgroup.topEquiv (G := Kp)).trans e.groupEquiv
    linearEquiv := q.trans e.linearEquiv
    intertwines := by
      intro g u
      obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ u
      change e.linearEquiv (q (Submodule.Quotient.mk
        ((invariantSubspace ρ ⊤ D hstab).toRepresentation g d))) =
          (alternatingNatural 5) (e.groupEquiv g.val)
            (e.linearEquiv (q (Submodule.Quotient.mk d)))
      simp only [q, Submodule.quotEquivOfEq_mk]
      exact e.intertwines g.val (Submodule.Quotient.mk d)
  }
  exact irreducible_of_equiv a
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))

include hL hz in
/-- Both source commutators equal the embedded U(K), placing it in the seed. -/
theorem movingSpace_le_seedSpace (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    D ≤ seedSpace K L T z v := by
  have he := (Replacement.MovingBlock.source_moving_eq_blockU K L T z v hL hz hK hn hW hb).trans
    (Replacement.MovingBlock.seed_moving_eq_blockU K L T z v hK hn hW hb).symm
  intro w hw
  change w.toMul.val ∈ conjugateSpanBy (zpowers z) K
  change w.toMul.val ∈ ⁅W, K⁆ at hw
  rw [he] at hw
  exact (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy (zpowers z) K)) hw

/-- A₅ cohomology vanishing removes the central kernel and lifts the coordinates. -/
noncomputable def fullActionEquiv
    (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA)
    (hρA : ∀ (g : alternatingGroup (Fin 5)) (w : Multiplicative (BinaryPermutation.natural (Fin 5))),
      Multiplicative.toAdd (rhoA g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) g w.toAdd)
    (hIrr : IsIrrPlus (componentRepresentation K L T z v hL hz)
      (⊤ : Subgroup (plusImage K L T z v hL hz K))
      (movingSpace K L T z v)) :
    ActionEquiv
      (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation
      (alternatingNatural 5) := by
  let s := movedSection K L T z v hL hz
  letI : Subsingleton (H1 (alternatingNatural 5)) := by
    apply (Module.finrank_zero_iff (R := ZMod 2)).mp
    exact BinaryPermutation.alternatingNatural_finrank_H1_eq_zero_of_odd
      (Fin 5) (by norm_num [Fintype.card_fin]) (by decide)
  let selfDual : ActionEquiv (alternatingNatural 5)
      (Representation.dual (alternatingNatural 5)) := by
    exact ⟨MulEquiv.refl _, BinaryPermutation.naturalDualEquiv (Fin 5),
      fun g w => BinaryPermutation.naturalDualEquiv_equivariant (Fin 5) g.val w⟩
  letI : Subsingleton (H1 (Representation.dual (alternatingNatural 5))) :=
    (actionSymm selfDual).H1_subsingleton
  let e := sectionActionEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
  let e' : ActionEquiv (s.action.comp (⊤ : Subgroup Kp).subtype)
      (alternatingNatural 5) :=
    ⟨(Subgroup.topEquiv (G := Kp)).trans e.groupEquiv,
      e.linearEquiv, fun a x => e.intertwines a.val x⟩
  have hcomp := moved_isCompl_of_equiv s hIrr e'
  have hC : (Submodule.comap (movingSpace K L T z v).subtype
      (Representation.invariants (componentRepresentation K L T z v hL hz))) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hfix : (x : Additive (WK K L T z v)) ∈
        fixedSpace (componentRepresentation K L T z v hL hz)
          (⊤ : Subgroup (plusImage K L T z v hL hz K)) := by
      intro a
      exact hx a.val
    exact hcomp.disjoint.le_bot ⟨x.property, hfix⟩
  let q : movingSpace K L T z v ≃ₗ[ZMod 2]
      (movingSpace K L T z v ⧸
        Submodule.comap (movingSpace K L T z v).subtype
          (Representation.invariants (componentRepresentation K L T z v hL hz))) :=
    LinearEquiv.ofBijective
      (Submodule.comap (movingSpace K L T z v).subtype
        (Representation.invariants (componentRepresentation K L T z v hL hz))).mkQ
      ⟨(LinearMap.ker_eq_bot).mp (by rw [Submodule.ker_mkQ, hC]),
        Submodule.mkQ_surjective _⟩
  let E : ActionEquiv
      (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation
      (alternatingNatural 5) := {
    groupEquiv := actorEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
    linearEquiv := q.trans (sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model)
    intertwines := by
      intro a x
      change (sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model)
          (Submodule.mkQ
            (Submodule.comap (movingSpace K L T z v).subtype
              (Representation.invariants (componentRepresentation K L T z v hL hz)))
            ((Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation
              a x)) = _
      exact (sectionActionEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA).intertwines
        a (Submodule.mkQ
          (Submodule.comap (movingSpace K L T z v).subtype
            (Representation.invariants (componentRepresentation K L T z v hL hz))) x)
  }
  exact E

end AlternatingBlock

open AlternatingBlock

/-- An actual A₅ block produces the forbidden full constituent inside ⟨z^K⟩.
No natural rank-one coordinates or ambient-G subnormality enter the construction. -/
theorem source_alternatingFive_constituent
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (htype : IsAlternatingBlock K 5) :
    ∃ I : Subrepresentation ρ, I.toSubmodule ≤ seedSpace K L T z v ∧
      IsIrrPlus ρ ⊤ I.toSubmodule ∧
      Nonempty (ActionEquiv I.toRepresentation (alternatingNatural 5)) := by
  obtain ⟨_, hs, rhoA, ⟨model⟩, hρA⟩ := htype
  let e := sectionActionEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
  have hi := movingSpace_isIrrPlus K L T z v hL hz hs e
  exact ⟨Replacement.Action.movingSubrepresentation K L T z v hL hz,
    movingSpace_le_seedSpace K L T z v hL hz hK hn hW hb, hi,
    ⟨fullActionEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA hi⟩⟩

/-- The exact earlier seed exclusion rules out the A₅ block alternative. -/
theorem source_not_isAlternatingBlock
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hex : ExcludesAlternatingFiveSeed K L T z v hL hz) :
    ¬ IsAlternatingBlock K 5 := by
  intro htype
  obtain ⟨I, hseed, hi, he⟩ :=
    source_alternatingFive_constituent K L T z v hL hz hK hn hW hb hcore htype
  exact hex I hseed hi he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
end
