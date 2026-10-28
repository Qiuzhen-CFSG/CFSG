module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingBlock
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Natural recognition and the rank-one block type in 13.6.18

Apply the genuine universal adequate B.5 classifier to the offender subgroup
of the faithful W_K action. The earlier local conclusions construct all its
applicability hypotheses. Quasisimplicity excludes degree one through the
concrete SL₂(2) ≃ S₃ model. The natural alternative supplies coordinates over
the original field on the literal U_K/C_U_K(K), without a block witness.

In the other alternative the whole moving module is irreducible. The
noncentral seed has a nonzero commutator inside it, so the moving module lies
inside the seed. Its transported Irr⁺ membership and actual A₅ permutation
coordinates contradict exactly 13.6.15.

For a relative block inside KTᵥ, the independent AlternatingBlock argument
excludes the A₅ branch of the full pushing-up disjunction. Comparing the
literal block quotient with the independently constructed natural section
then recovers the same exponent. The universal classifier, the earlier seed
exclusion, and the specified earlier local conclusions remain explicit source
inputs. The parent replacement assembly supplies the relative block premises.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1/B.5.6,
printed pp.99–105, and 13.6.15/13.6.18, pp.930–931 (PDF pp.947–948).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open ComponentSelection ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
section
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  [IsElementaryAbelian 2 (WK K L T z v)]
local notation "Kp" => plusImage K L T z v hL hz K
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v

/-- A noncentral invariant seed contains the whole moving space when the
latter is irreducible. This does not use a block witness. -/
theorem moving_le_seed_of_irreducible (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hi : IsIrreducible
      (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation) :
    D ≤ seedSpace K L T z v := by
  let R := Replacement.Action.movingSubrepresentation K L T z v hL hz
  let I : Subrepresentation R.toRepresentation := {
    toSubmodule := (seedSpace K L T z v).comap (D).subtype
    apply_mem_toSubmodule := fun a x hx => seedSpace_invariant K L T z v hL hz a x hx }
  let : IsIrreducible R.toRepresentation := hi
  rcases eq_bot_or_eq_top I with hb | ht
  · exfalso
    apply seedSpace_commutator_ne_bot K L T z v hL hz hK hn
    apply le_bot_iff.mp
    have hm : subspaceCommutator ρ (seedSpace K L T z v) ⊤ ≤ D := by
      rw [Replacement.Action.movingSpace_eq_subspaceCommutator K L T z v hL hz]
      exact subspaceCommutator_mono_left ρ le_top ⊤
    have hs : subspaceCommutator ρ (seedSpace K L T z v) ⊤ ≤ seedSpace K L T z v := by
      apply subspaceCommutator_le_of_invariant
      apply le_subspaceStabilizer
      intro a _ x hx
      exact seedSpace_invariant K L T z v hL hz a x hx
    intro x hx
    have hi : (⟨x, hm hx⟩ : D) ∈ I := hs hx
    rw [hb] at hi
    exact congrArg Subtype.val hi
  · intro x hx
    have hi : (⟨x, hx⟩ : D) ∈ I := ht.symm ▸ Submodule.mem_top
    exact hi

/-- Exclude the permutation branch on the actual seed and transport the
natural branch to the literal central quotient, with a single actor map. -/
theorem natural_actionEquiv_of_case
    (J : Subgroup (Gplus K L T z v hL hz)) (hJ : Kp ≤ J)
    (F : BinaryField)
    (hcase : RankOneComponentCase ((wkRepresentation K L T z v hL hz).comp J.subtype)
      ((Kp).subgroupOf J) F)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hex : ExcludesAlternatingFiveSeed K L T z v hL hz) :
    Nonempty (ActionEquiv (Replacement.Action.sectionRepresentation K L T z v hL hz)
      (linearNatural F 2)) := by
  cases hcase with
  | natural s e =>
    let t := ClassifierTransport.sectionActionEquiv K L T z v hL hz J hJ s
    exact ⟨{ groupEquiv := t.groupEquiv.trans e.groupEquiv
             linearEquiv := t.linearEquiv.trans e.linearEquiv
             intertwines := fun a x => by
               change e.linearEquiv (t.linearEquiv
                 (Replacement.Action.sectionRepresentation K L T z v hL hz a x)) = _
               rw [t.intertwines, e.intertwines]
               rfl }⟩
  | alternatingFive s hi e =>
    let t := ClassifierTransport.movingActionEquiv K L T z v hL hz J hJ s
    let a : ActionEquiv
        (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation
        (alternatingNatural 5) := {
      groupEquiv := t.groupEquiv.trans e.groupEquiv
      linearEquiv := t.linearEquiv.trans e.linearEquiv
      intertwines := fun a x => by
        change e.linearEquiv (t.linearEquiv
          ((Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation a x)) = _
        rw [t.intertwines, e.intertwines]
        rfl }
    have hirr := ExtensionConsequences.irreducible_of_equiv a
      (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
    exact (hex (Replacement.Action.movingSubrepresentation K L T z v hL hz)
      (moving_le_seed_of_irreducible K L T z v hL hz hK hn hirr)
      (ClassifierTransport.isIrrPlus_moving K L T z v hL hz J hJ s hi) ⟨a⟩).elim

end

namespace Source
open Theory.GroupTheory ChapterB.SourceInduction
open Matrix.SpecialLinearGroup.RankOneResidual
open scoped MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem degree_gt_one {C : Type*} [Group C] (hc : IsQuasisimple C)
    (F : BinaryField) (e : C ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    1 < F.degree := by
  let : IsQuasisimple C := hc
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  by_contra h
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  let : Fintype F.Carrier := Fintype.ofFinite _
  let f := ZMod.ringEquivOfPrime F.Carrier Nat.prime_two
    (show Fintype.card F.Carrier = 2 by rw [← Nat.card_eq_fintype_card, F.card_eq, hd]; norm_num)
  let a := e.trans ((Atlas.fieldEquivSL 2 f.symm).trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable C
    (Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective)

variable {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (F : BinaryField)
    (e : plusImage K L T z v hL hz K ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (classification : AdequateClassificationInput.{u,u} 𝒦)

include hG hv hn e classification in
/-- The first paragraph of 13.6.18 on the actual action: all classifier
applicability conditions are proved, and the exact earlier 13.6.15 assertion
removes the A₅ permutation branch. No block witness enters this construction. -/
theorem natural_actionEquiv
    (hex : let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed K L T z v hL hz) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    Nonempty (ActionEquiv (Replacement.Action.sectionRepresentation K L T z v hL hz)
      (linearNatural F 2)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  have ha := classifierApplicability_of_local hG K L T z v hv hL hz hSylow hzOmega hf hK hn
  have hc := plusImage_K_quasisimple K L T z v hL hz hK ha.twoCore
  have hcase := ClassifierCases.wk_offender_component_case K L T z v hL hz
    ha hc F (degree_gt_one hc F e) e classification
  exact natural_actionEquiv_of_case K L T z v hL hz
    (offenderSubgroup (wkRepresentation K L T z v hL hz)) ha.le_offenders
    F hcase hK hn hex

include hG hv hn e classification in
/-- Natural coordinates on U_K/C_U_K(K), over the originally specified
field, with one actor isomorphism throughout. -/
theorem naturalSection
    (hex : let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed K L T z v hL hz) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    Nonempty (NaturalSection (F := F.Carrier)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  obtain ⟨a⟩ := natural_actionEquiv hG K L T z v hv hL hz hSylow hzOmega hf hK hn F e
    classification hex
  exact ⟨Replacement.Action.naturalSectionOfActionEquiv K L T z v hL hz F a⟩

include hG hv hL hz hSylow hzOmega hf hK hn e classification in
/-- Resolve the full pushing-up disjunction using the exact seed exclusion,
then recover the same field exponent through the literal block quotient.
The relative block premises are supplied by the replacement assembly. -/
theorem isL2EvenBlock
    (hex : let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed K L T z v hL hz)
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (htypes : (∃ m, ChapterC.IsL2EvenBlock K m) ∨ ChapterC.IsAlternatingBlock K 5) :
    ChapterC.IsL2EvenBlock K F.degree := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  have hcore := plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow
  obtain ⟨m, hm⟩ := htypes.resolve_right
    (source_not_isAlternatingBlock K L T z v hL hz hK hn hW hb hcore hex)
  obtain ⟨s⟩ := naturalSection hG K L T z v hv hL hz hSylow hzOmega hf hK hn F e
    classification hex
  exact source_l2EvenBlock_of_type K L T z v hL hz F.card_eq hK hn hW hb s hm

end Source

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
end
