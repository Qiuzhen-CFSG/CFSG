module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SeedAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Generation
public import Theory.Representation.BinaryPermutation.TransvectionQuotients
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.SpecificGroups.SymmetricTwoResidual
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import Theory.Representation.BinaryOffender.FaithfulRankOne
import Mathlib.Tactic

/-!
# The whole-section transvection alternative in the original S₈ branch

The natural seed proves that the action on every literal U/V₁ section has
kernel exactly O₂(H). Thus a marking H/O₂(H) ≃ S₈ gives a faithful action on
the same space and coordinates. The original commutator theorem supplies
full A₈ movement, without assuming Data or a residual-component conclusion.

A rank-one involution would then give a surjective augmentation-core map.
Proper invariant preimages in that core are fixed, yielding a natural quotient
with a fixed kernel even in the nonsplit case. The original plane-centralizer
rank obstruction excludes it. Consequently no involution of the actual star
action has fixed codimension one.

The final application constructs the original quadratic actor in R₁. It
retains the whole-module bound and shows that either its rank is one and its
fixed codimension is exactly two, or its rank is at least two. Excluding these
remaining alternatives requires the original seed or reciprocal geometry;
this module does not complete the S₈ exclusion or 14.7.52.

Source: Aschbacher–Smith, Notation 14.7.1, 14.7.4(3), 14.7.48(2), and the
S₈ branch of 14.7.51, printed pp.1043,1064–1065; B.3.1, printed p.83.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem eight_residual_image (e : HStar F.H ≃* Equiv.Perm (Fin 8)) :
    ((K F).subgroupOf F.H).map (e.toMonoidHom.comp (starMap F)) =
      alternatingGroup (Fin 8) := by
  change (((pResidual 2 F.H).map F.H.subtype).comap F.H.subtype).map _ = _
  rw [comap_map_eq_self_of_injective F.H.subtype_injective,
    map_pResidual_of_surjective 2 _ (e.surjective.comp (QuotientGroup.mk'_surjective _)),
    Equiv.Perm.twoResidual_eq_alternating]

/-- The literal section has precisely the original two-core as its action
kernel in the S₈ branch. Normal kernel structure and the seed discharge faithfulness. -/
theorem original_eight_action_kernel_eq_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ρ.ker = pCore 2 F.H := by
  have hcore := core_le_action_kernel h c
  let q := e.toMonoidHom.comp (starMap F)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 F.H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact QuotientGroup.ker_mk' _
  let I := ρ.ker.map q
  let : I.Normal := (inferInstance : ρ.ker.Normal).map q hq
  have hI : I = ⊥ := by
    by_contra hn
    have hA : alternatingGroup (Fin 8) ≤ I :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot I).mpr hn)
    have hK : (K F).subgroupOf F.H ≤ ρ.ker := by
      have hmap : ((K F).subgroupOf F.H).map q ≤ ρ.ker.map q := by
        rw [eight_residual_image]
        exact hA
      have hpre := map_le_iff_le_comap.mp hmap
      rwa [comap_map_eq,hqk,sup_eq_left.mpr hcore] at hpre
    have hVP : V ≤ F.Vi 1 := by
      apply (seed_commutator h F).le.trans
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl v hv
      have hlH : l ∈ F.H := (F.Li_le L 1 hl).2
      exact (c.action_mem_ker_iff ⟨l,hlH⟩).mp
        (hK (pointResidual_le F hl)) v (le_conjugateSpanBy V F.H hv)
    have hc := card_le_of_le hVP
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    omega
  exact le_antisymm (((Subgroup.map_eq_bot_iff _).mp hI).trans hqk.le) hcore

/-- Factor the original action faithfully through its actual star quotient,
without changing the vector space or its conjugation coordinates. -/
theorem original_eight_faithful_factorization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) W,
      σ.comp (e.toMonoidHom.comp (starMap F)) = ρ ∧ Function.Injective σ := by
  obtain ⟨τ,hτ⟩ := exists_star_representation h c
  let σ := τ.comp e.symm.toMonoidHom
  have heq : σ.comp (e.toMonoidHom.comp (starMap F)) = ρ := by
    ext g w
    change τ (e.symm (e (starMap F g))) w = ρ g w
    rw [e.symm_apply_apply]
    exact congrArg (fun a : Representation (ZMod 2) F.H W => a g w) hτ
  refine ⟨σ,heq,?_⟩
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply bot_unique
  intro g hg
  obtain ⟨a,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) g
  have ha : a ∈ ρ.ker := by
    change ρ a = 1
    rw [←heq]
    exact hg
  have hc := (original_eight_action_kernel_eq_core h e c).le ha
  change e (starMap F a) = 1
  rw [show starMap F a = 1 from (QuotientGroup.eq_one_iff a).mpr hc,map_one]

/-- A rank-one star involution is impossible on the whole original section.
The natural quotient and its kernel fixation are constructed in the proof. -/
theorem original_eight_involution_fixedCodim_ne_one_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha : starMap F a ≠ 1) (ha2 : starMap F a ^ 2 = 1) :
    fixedCodim ρ (zpowers a) ≠ 1 := by
  intro hr
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨σ,hσ,hf⟩ := original_eight_faithful_factorization h e c
  let q := e.toMonoidHom.comp (starMap F)
  have hm := c.subspaceCommutator_eq_top_of_movement (K F) (map_subtype_le _) (by
    rw [commutator_comm,commutator_U h F,sup_eq_left.mpr c.kernel_le])
  rw [←hσ,subspaceCommutator_comp_map,eight_residual_image] at hm
  have hr' : fixedCodim σ (zpowers (q a)) = 1 := by
    rw [←hσ] at hr
    change Module.finrank (ZMod 2) (W ⧸ fixedSpace (σ.comp q) (zpowers a)) = 1 at hr
    rwa [fixedSpace_comp_map,MonoidHom.map_zpowers] at hr
  have ha' : q a ≠ 1 := fun hz => ha (e.injective (hz.trans e.map_one.symm))
  have ha2' : q a ^ 2 = 1 := by
    change e (starMap F a) ^ 2 = 1
    rw [←map_pow,ha2,map_one]
  obtain ⟨p,_,hk⟩ := BinaryPermutation.TransvectionCoreMap.natural_fixed_kernel_quotient_of_rank_one_involution
    σ hf (MulEquiv.refl _) (alternatingGroup (Fin 8)) (by simp) hm (q a) ha' ha2' hr'
  let p' : ρ.IntertwiningMap ((BinaryPermutation.naturalRepresentation (Fin 8)).comp q) := {
    toLinearMap := p.toLinearMap
    isIntertwining' := by
      intro g
      have he : ρ g = σ (q g) := congrArg (fun τ => τ g) hσ.symm
      change p.toLinearMap.comp (ρ g) = _
      rw [he]
      exact p.isIntertwining' (q g) }
  apply original_eight_residual_fixed_quotient_impossible_at h structural previous faithful e c p'
  intro w hw k
  have he : ρ k.val = σ (q k.val) := congrArg (fun τ => τ k.val) hσ.symm
  change ρ k.val w = w
  rw [he]
  exact hk hw (q k.val)

/-- The same whole-section exclusion with the original many-overgroup guards. -/
theorem original_eight_involution_fixedCodim_ne_one_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8))
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha : starMap F a ≠ 1) (ha2 : starMap F a ^ 2 = 1) :
    fixedCodim ρ (zpowers a) ≠ 1 :=
  original_eight_involution_fixedCodim_ne_one_at h (structural hmany) (previous hmany)
    faithful e c a ha ha2

open Chapter15.Section03.AbelianAmalgam

/-- Select the actual whole-section quadratic actor. In its rank-one case,
faithfulness and the transvection exclusion force fixed codimension exactly two.
The higher-rank alternative remains explicit and is not an excluded branch. -/
theorem original_eight_quadratic_actor_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 8)) :
    ∃ hU : IsElementaryAbelian 2 F.U, let := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        (∀ t : HStar F.H, t ≠ 1 → t ^ 2 = 1 →
          fixedCodim a.representation (zpowers t) ≠ 1) ∧
        ∃ A : Subgroup F.H,
          A ≤ (F.Ri L 1).subgroupOf F.H ∧
          IsElementaryTwo (A.map (starMap F)) ∧
          IsQuadratic a.representation (A.map (starMap F)) ∧
          fixedCodim a.representation (A.map (starMap F)) ≤ 2 * rank (A.map (starMap F)) ∧
          ((rank (A.map (starMap F)) = 1 ∧
            fixedCodim a.representation (A.map (starMap F)) = 2) ∨
            2 ≤ rank (A.map (starMap F))) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  let earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u} := ⟨structural,uniqueness,previous⟩
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod⟩ :=
    Chapter12.Section09.NaturalSource.abelian_local_quadratic_actor h earlier F hab
      F.H (h.point_mem_Hz_at F (previous.at T))
  let := hU
  change IsElementaryTwo (A.map (starMap F)) at hA
  change fixedCodim a.representation (A.map (starMap F)) ≤
    2 * rank (A.map (starMap F)) at hcod
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let s := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ hpoint)
  let c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s.le
    kernel_le := s.line_le
    normalized := s.normalizes
    coordinates := s.quotient
    onto := s.surjective
    kernel_eq := s.kernel
    equivariant := fun x v => (s.conjugates x v).symm }
  have hno (t : HStar F.H) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
      fixedCodim a.representation (zpowers t) ≠ 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) t
    have hn := original_eight_involution_fixedCodim_ne_one_at h (structural.at T)
      (previous.at T) faithful e c x ht ht2
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp (starMap F)) (zpowers x)) ≠ 1 at hn
    rwa [fixedSpace_comp_map,MonoidHom.map_zpowers] at hn
  refine ⟨hU,a,hq,hno,A,hAR,hA,hquad,hcod,?_⟩
  by_cases hr : rank (A.map (starMap F)) = 1
  · left
    refine ⟨hr,?_⟩
    let B := A.map (starMap F)
    let : IsElementaryAbelian 2 B := hA.2
    let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hA.1
    obtain ⟨t,ht⟩ := exists_ne (1 : B)
    have hc : Nat.card B = 2 := by
      change Nat.card (A.map (starMap F)) = 2
      rw [hA.card_eq_two_pow_rank,hr]
      rfl
    have ht' : (t : HStar F.H) ≠ 1 := fun hz => ht (Subtype.ext hz)
    have ht2 : (t : HStar F.H) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ t.property
    have hz : zpowers (t : HStar F.H) = B := by
      have hh := congrArg (Subgroup.map B.subtype) (zpowers_eq_top_of_prime_card hc ht)
      rwa [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    have hn : fixedCodim a.representation B ≠ 1 := hz ▸ hno t ht' ht2
    change fixedCodim a.representation (A.map (starMap F)) ≠ 1 at hn
    have hp : 0 < fixedCodim a.representation (A.map (starMap F)) :=
      fixedCodim_pos_of_faithful a.representation a.faithful hA.1
    rw [hr] at hcod
    change fixedCodim a.representation (A.map (starMap F)) = 2
    omega
  · right
    have hp := hA.rank_pos
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
