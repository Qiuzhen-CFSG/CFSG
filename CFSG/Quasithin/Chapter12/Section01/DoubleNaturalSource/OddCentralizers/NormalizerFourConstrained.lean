module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourPushingUp

/-!
# The two remaining constrained star models in degree four

The original intersection residual has simple quotient L₄(2), of order
20160, and contains elements of order four. Its actual normalized action
on the escaping constrained component has solvable kernel. The large
rank-two star models are excluded by their local exponent calculation;
the smaller finite star models are excluded by section-order divisibility.
The exact C.2.7 catalogue therefore leaves only A₈ and SL₅(2), with actual
isomorphisms of the original star image. Their module exclusions remain.

The last theorem constructs these two possibilities on the original C.2.8
witness produced by failure of residual uniqueness, retaining the full orbit
and original radical. Source: Aschbacher--Smith 4.2.12--13, 4.4.6 and 12.1.9,
pp.610--612,620,793; C.2.7--8, pp.146--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private abbrev Four := alternatingGroup (Fin 8)
private instance fourSimple : IsSimpleGroup Four := alternatingGroup.isSimpleGroup (by simp)
private theorem four_card : Nat.card Four = 20160 := by
  rw [nat_card_alternatingGroup,Nat.card_fin]
  decide

private theorem four_two_exponent :
    ¬ ∀ P : Subgroup Four, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  let c : Equiv.Perm (Fin 8) :=
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5
  let b : Four := ⟨c,by
    change Equiv.Perm.sign c = 1
    decide⟩
  have hb : b ^ 4 = 1 := by decide
  have hb2 : b ^ 2 ≠ 1 := by decide
  have hp : IsPGroup 2 (zpowers b) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hb
  intro he
  exact hb2 (congrArg Subtype.val (he (zpowers b) hp ⟨b,mem_zpowers b⟩))

variable {G : Type*} [Group G] [Finite G]

/-- These are markings of the literal star image, not abstract family labels. -/
@[expose] def FourConstrainedModels (K R : Subgroup G) : Prop :=
  Nonempty (starImage K R K ≃* alternatingGroup (Fin 8)) ∨
    Nonempty (starImage K R K ≃* SL(5,ZMod 2))

/-- The original normalized L₄(2) section eliminates every other C.2.7 star row. -/
theorem doubledFour_constrained_models
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 8))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : FourConstrainedModels (K.map H.subtype) R := by
  let π := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hS : ¬ Group.IsSolvable Four := Group.IsPerfect.not_isSolvable Four
  have hsmall (hh : Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) < 20160) : False := by
    have hd := constrained_normalized_simple_order_dvd h hn hS π hπ K hK hq hout
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv] at hd
    have hd' := hd.trans (center (starImage (K.map H.subtype) R (K.map H.subtype))).card_quotient_dvd_card
    have hle := Nat.le_of_dvd Nat.card_pos hd'
    rw [four_card] at hle
    omega
  have hm := ChapterC.C27Source.star_model_from_source (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo E e => exact (h.no_constrained_component_star_linear_two K hK hq hout hfK E e).elim
  | linearThree E e =>
    by_cases hE : 1 < E.degree
    · exact (no_constrained_normalized_linear_three h hn hS four_two_exponent π hπ K hK hq hout hfK E hE e).elim
    · apply (hsmall ?_).elim
      have hdeg : E.degree = 1 := by have := E.degree_pos; omega
      rw [Nat.card_congr e.toEquiv]
      have hc := (center SL(3,E.Carrier)).index_mul_card
      rw [Atlas.ExceptionalSupport.card_sl_center] at hc
      change Nat.card PSL(3,E.Carrier) * Nat.gcd 3 (Nat.card E.Carrier - 1) = _ at hc
      rw [←hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar,E.card_eq,hdeg]
      norm_num
  | symplectic E hE e =>
    apply (no_constrained_normalized_symplectic h hn hS four_two_exponent π hπ K hK hq hout hfK e ?_).elim
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2 E hE e =>
    apply (no_constrained_normalized_g2 h hn hS four_two_exponent π hπ K hK hq hout hfK e ?_).elim
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  | g2DerivedTwo e =>
    apply (hsmall ?_).elim
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    norm_num
  | alternating n hdegree e =>
    rcases hdegree with rfl | rfl | rfl | rfl
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num
    · exact Or.inl ⟨e⟩
  | linearFiveTwo e => exact Or.inr ⟨e⟩
  | tripleSix ez eq =>
    apply (hsmall ?_).elim
    let C := starImage (K.map H.subtype) R (K.map H.subtype)
    have hc := (center C).index_mul_card
    change Nat.card (C ⧸ center C) * Nat.card (center C) = Nat.card C at hc
    rw [Nat.card_congr eq.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc
    rw [←hc]
    norm_num

variable {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

/-- Failure of residual uniqueness now gives one of two literal constrained star models. -/
theorem doubledFour_pushingUp_two_linear_models_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        FourConstrainedModels (K.map H.subtype) (J.pCoreIn 2) := by
  obtain ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,hcon⟩ :=
    D.doubledFour_pushingUp_constrained_of_many h hmany B A hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  obtain ⟨e,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,hout,hcon,
    doubledFour_constrained_models hc hn (e.trans (B.component.trans doubledFour_linearEquiv))
      K hK hq hout hcon⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
