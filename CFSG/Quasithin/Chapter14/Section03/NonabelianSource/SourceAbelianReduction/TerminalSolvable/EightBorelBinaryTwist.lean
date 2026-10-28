module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelInvolutions
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.BinaryTwist

/-!
# The single remaining twist on the original eight-field component

Apply the two-representative reduction to the literal ComponentLift and
EightImageRow. The checked ambient generation theorem extends the untwisted
completion isomorphism to G, preserving both original endpoint maps. Thus the
original exclusion of Theorem E models removes this entire branch. Only the
explicit highest-root-twisted arms reflection and canonical central reflection
remain, with product order six in the original completion and in G.

Excluding that twisted relation remains necessary for the original Borel
contradiction. The genuine earlier MarkedTriality premise stays explicit,
with its original inclusion maps and commuting squares. No T ≤ K hypothesis
is added.
Source: Aschbacher--Smith F.4.15--17 and 14.3.6,15, pp.281--283,991,994
(`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.BinaryTorusEndpoints
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- The untwisted binary orbit recognizes the original ambient group,
preserving both endpoint maps. Only the single twisted relation remains. -/
theorem source_eight_marked_recognition_or_twist
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    (∃ f : G ≃* BinaryCarrier 1 Nat.zero_lt_one,
      (∀ x, f (c.left x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left x) ∧
      (∀ x, f (c.right x : G)=ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right x)) ∨
    (let s := endpointWord .arms ![0,0,1] 0 1
     let t := simpleEndpoint .central
     s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
       (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6) := by
  let c := EightLargeParabolic.markedCompletion r
  have hgen := (source_eight_marked_generation hG T hempty hM hu hmany hcard e hK h8 r).2
  have hord := source_eight_marked_card_eq_triality hG T hempty hM hu hmany hcard e hK h8 r
  let J := (K ⊔ (T : Subgroup G)) ⊔
    EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G))
  have hbound : Nat.card J≤Nat.card (BinaryCarrier 1 Nat.zero_lt_one) :=
    (Nat.card_le_card_of_injective J.subtype J.subtype_injective).trans_eq hord
  rcases ChapterF.SourceCompletion.TrialityTwo.Completion.recognition_or_twisted_relation c hbound
    with ⟨f,hfL,hfR⟩ | ht
  · let j : J ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
    refine Or.inl ⟨j.symm.trans f,?_,?_⟩
    · intro x
      change f (j.symm (j (c.left x)))=_
      rw [j.symm_apply_apply,hfL]
    · intro x
      change f (j.symm (j (c.right x)))=_
      rw [j.symm_apply_apply,hfR]
  · exact Or.inr ht

/-- Under the original model exclusion, the remaining actual pair is the
central-root-twisted arms reflection and the canonical central reflection.
The displayed equation uses the original maps and the literal inclusion in G. -/
theorem source_eight_marked_forced_twist
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hnot : ¬ClassificationModels.IsTheoremEModel G) :
    let c := EightLargeParabolic.markedCompletion r
    let s := endpointWord .arms ![0,0,1] 0 1
    let t := simpleEndpoint .central
    s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
      (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
      ((c.left s:G)*(c.right t:G))^6=1 ∧
        orderOf ((c.left s:G)*(c.right t:G))=6 := by
  rcases source_eight_marked_recognition_or_twist hG T hempty hM hu hmany hcard e hK h8 r
    with ⟨f,_,_⟩ | ⟨hs,ht,hsout,htout,hpow,ho⟩
  · exact (hnot (ClassificationModels.IsTheoremEModel.triality
      ((isTrialityGroupAt_two_iff G).mpr ⟨f⟩))).elim
  · exact ⟨hs,ht,hsout,htout,hpow,ho,congrArg Subtype.val hpow,
      (Subgroup.orderOf_coe _).trans ho⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
