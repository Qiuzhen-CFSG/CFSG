module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalClassification
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Generators
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Theory.Alternating.Aut
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The outer natural-action branch of B.5.1

The full corrected B.4.2 catalogue leaves Sp₄(2), G₂(2), S₅, S₇ and S₈
when the offender subgroup J of LT differs from L. For the symmetric and
G₂ endpoints, actual conjugation identifies the full model with the
automorphism group of its component. This proves that Out(L) is abelian;
source observation β then gives G = LT for every Sylow two-subgroup.
Faithful conjugation of LT on its centerless generalized Fitting subgroup
bounds its order by the marked J, proving J = LT. The given linear
intertwiner consequently extends to the original ambient action.

For Sp₄(2), the genuine polar equivalence identifies its derived subgroup
with A₆. The proved abelian outer group again gives G = LT. Any proper
local overgroup of J would be all of Aut(A₆). Its element of order eight
cannot act faithfully in binary dimension four: the displacement of a
two-power operator is nilpotent, with nilpotence index at most four.
This excludes Aut(A₆). The concrete polar linear equivalence identifies
the resulting action with the deleted six-letter natural module.

All model automorphism, order and action facts used here are proved in the
narrow imports. The final theorem takes only the original source hypothesis,
the moved section, its Irr⁺ hypothesis, the complete corrected local B.4.2
case, and J ≠ L. It does not invoke the legacy triple-cover offender clause.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, the irreducible branch (β′); B.4.2, printed p.86.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.OuterNatural

universe u v w z

private theorem outer_commutative {E : Type w} [Group E] (M : Subgroup E) [M.Normal]
    (hd : commutator E ≤ M)
    (hs : Function.Surjective (MulAut.conjNormal : E →* MulAut M)) :
    IsMulCommutative (MulAut.Outer M) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  have hm := Subgroup.map_mono (f := (MulAut.conjNormal : E →* MulAut M)) hd
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hs] at hm
  apply hm.trans
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩

private theorem center_eq_bot_of_conjugation_injective {E : Type w} [Group E]
    (M : Subgroup E) [M.Normal]
    (hf : Function.Injective (MulAut.conjNormal : E →* MulAut M)) : center M = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subtype.ext
  apply hf
  change (MulAut.conjNormal : E →* MulAut M) (x : E) = MulAut.conjNormal (1 : E)
  rw [map_one, MulAut.conjNormal_val]
  ext y
  apply mul_inv_eq_iff_eq_mul.mpr
  exact congrArg Subtype.val (mem_center_iff.mp hx y).symm

private theorem center_eq_bot_transport {A : Type u} {B : Type w} [Group A] [Group B]
    (e : A ≃* B) (hB : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  have he := (centerCongr e ⟨a, ha⟩).property
  change e a ∈ center B at he
  rw [hB, mem_bot] at he
  exact e.map_eq_one_iff.mp he

private theorem conjugation_injective_of_fitting {Q : Type u} [Group Q] [Finite Q]
    (N : Subgroup Q) [N.Normal] (hfit : generalizedFitting Q = N)
    (hz : center N = ⊥) : Function.Injective (MulAut.conjNormal : Q →* MulAut N) := by
  apply MulAut.conjNormal_injective_of_centralizer_eq_bot
  have hc : centralizer (N : Set Q) ≤ N :=
    hfit ▸ QuasisimpleSections.centralizer_generalizedFitting_le
  apply bot_unique
  intro x hx
  have hz' : (⟨x, hc hx⟩ : N) ∈ center N := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hx y y.property
  rw [hz, mem_bot] at hz'
  exact congrArg Subtype.val hz'

private noncomputable def lift_top_action {Q : Type u} [Group Q]
    {E : Type w} [Group E] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q V} {σ : Representation (ZMod 2) E W}
    {H : Subgroup Q} (e : ActionEquiv (ρ.comp H.subtype) σ) (hH : H = ⊤) :
    ActionEquiv ρ σ where
  groupEquiv := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hH.symm)).trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, hH.symm ▸ mem_top g⟩ v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- A marked endpoint whose full group is Aut of its component fills the
local group and then, by source β, the original ambient group. -/
theorem full_automorphism_endpoint {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (M : Subgroup E) [M.Normal]
    (e : MarkedActionEquiv (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype))
      (L.subgroupOf (L ⊔ (T : Subgroup G))) σ M)
    (hd : commutator E ≤ M)
    (ha : Function.Bijective (MulAut.conjNormal : E →* MulAut M)) :
    (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧ Nonempty (ActionEquiv s.action σ) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let D := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf D
  let J := offenderSubgroup (s.action.comp D.subtype)
  let eL : L ≃* M := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm.trans
    e.subgroupEquiv
  let : IsMulCommutative (MulAut.Outer M) := outer_commutative M hd ha.2
  let : IsMulCommutative (MulAut.Outer L) := ⟨⟨fun a b =>
    (MulAut.outerCongr eL).injective ((map_mul _ a b).trans
      ((mul_comm' _ _).trans (map_mul _ b a).symm))⟩⟩
  have htop (T' : Sylow 2 G) : L ⊔ (T' : Subgroup G) = ⊤ :=
    whole_eq_component_sylow_of_outer_abelian ρ L h.fitting h.generated T'
  have hf : Function.Injective (MulAut.conjNormal : D →* MulAut N) :=
    conjugation_injective_of_fitting N
      (local_generalizedFitting L T h.fitting h.twoCore T.isPGroup')
      (center_eq_bot_transport e.subgroupEquiv (center_eq_bot_of_conjugation_injective M ha.1))
  have hc : Nat.card D ≤ Nat.card J := calc
    Nat.card D ≤ Nat.card (MulAut N) := Nat.card_le_card_of_injective _ hf
    _ = Nat.card (MulAut M) := Nat.card_congr (MulAut.congr e.subgroupEquiv).toEquiv
    _ = Nat.card E := (Nat.card_congr (Equiv.ofBijective _ ha)).symm
    _ = Nat.card J := (Nat.card_congr e.action.groupEquiv.toEquiv).symm
  have hJ : J = ⊤ := J.eq_top_of_card_eq
    (Nat.le_antisymm (Nat.card_le_card_of_injective _ J.subtype_injective) hc)
  exact ⟨htop, ⟨lift_top_action (lift_top_action e.action hJ) (htop T)⟩⟩

/-- The marked symmetric rows (including the separate degree-eight row). -/
theorem symmetric_endpoint {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    {n : ℕ} (hn : n = 5 ∨ n = 7 ∨ n = 8)
    (e : MarkedActionEquiv (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype))
      (L.subgroupOf (L ⊔ (T : Subgroup G)))
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n))) :
    (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧ OuterNaturalAction s.action := by
  obtain ⟨htop, he⟩ := full_automorphism_endpoint h s T _ _ e
    (by rw [alternatingGroup.commutator_perm_eq (by simpa using (show 5 ≤ n by omega))])
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) (by omega))
  exact ⟨htop, Or.inl ⟨n, by omega, by omega, he⟩⟩

/-- The actual octonion G₂(2) action, using its proved automorphism identification. -/
theorem g2_endpoint {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (e : MarkedActionEquiv (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype))
      (L.subgroupOf (L ⊔ (T : Subgroup G))) (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) :
    (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧ OuterNaturalAction s.action := by
  obtain ⟨htop, he⟩ := full_automorphism_endpoint h s T _ _ e le_rfl
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective
  exact ⟨htop, Or.inr he⟩



/-- Aut(A₆) has an element of order eight, which cannot act faithfully on
four-dimensional binary space. This is the exceptional exclusion in B.5.1. -/
private theorem aut_six_not_faithful_four
    {Q : Type w} [Group Q] (e : Q ≃* AlternatingSix.ShadowLocal.AutA6)
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Q W) (hdim : Module.finrank (ZMod 2) W = 4) :
    ¬ Function.Injective σ := by
  intro hf
  let a := e.symm AlternatingSix.ShadowLocal.Identification.rotation
  have ha : orderOf a = 8 := e.symm.orderOf_eq _ |>.trans
    AlternatingSix.ShadowLocal.Identification.rotation_order
  have h8 : (σ a) ^ 8 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hn : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) W)
  let : Nontrivial W := hn
  let : CharP (Module.End (ZMod 2) W) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) _).injective 2
  have hnil : (σ a - 1) ^ (2 ^ 3) = 0 := by
    rw [sub_pow_char_pow_of_commute 2 3 (Commute.one_right (σ a))]
    norm_num only [show (2 : ℕ) ^ 3 = 8 by decide, one_pow]
    rw [h8, sub_self]
  have hfour : (σ a - 1) ^ 4 = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    have hh := Module.End.ker_pow_le_ker_pow_finrank (σ a - 1) (2 ^ 3)
    rwa [hnil, hdim, LinearMap.ker_zero] at hh
  have hp : (σ a) ^ 4 = 1 := by
    have hh := sub_pow_char_pow_of_commute (R := Module.End (ZMod 2) W)
      2 2 (Commute.one_right (σ a))
    norm_num only [show (2 : ℕ) ^ 2 = 4 by decide, one_pow] at hh
    rw [hfour] at hh
    exact sub_eq_zero.mp hh.symm
  have ha4 : a ^ 4 = 1 := hf (by simpa only [map_pow, map_one] using hp)
  have hd := orderOf_dvd_of_pow_eq_one ha4
  norm_num [ha] at hd

open Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison in
/-- The marked Sp₄(2) endpoint fills LT. A hypothetical proper overgroup
would be all of Aut(A₆), excluded by its order-eight element on the actual
four-dimensional module. The polar maps then identify the full natural S₆ action. -/
theorem symplectic_endpoint {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (e : MarkedActionEquiv (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype))
      (L.subgroupOf (L ⊔ (T : Subgroup G))) (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) :
    (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧ OuterNaturalAction s.action := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let D := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf D
  let σ := s.action.comp D.subtype
  let J := offenderSubgroup σ
  let eN : N ≃* alternatingGroup (Fin 6) :=
    e.subgroupEquiv.trans alternatingDerivedEquiv.symm
  let eL : L ≃* alternatingGroup (Fin 6) :=
    (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm.trans eN
  let : IsMulCommutative (MulAut.Outer (alternatingGroup (Fin 6))) :=
    AlternatingSix.ShadowLocal.outer_isMulCommutative
  let : IsMulCommutative (MulAut.Outer L) := ⟨⟨fun a b =>
    (MulAut.outerCongr eL).injective ((map_mul _ a b).trans
      ((mul_comm' _ _).trans (map_mul _ b a).symm))⟩⟩
  have htop (T' : Sylow 2 G) : L ⊔ (T' : Subgroup G) = ⊤ :=
    whole_eq_component_sylow_of_outer_abelian ρ L h.fitting h.generated T'
  let f : D →* AlternatingSix.ShadowLocal.AutA6 :=
    (MulAut.congr eN).toMonoidHom.comp MulAut.conjNormal
  have hf : Function.Injective f := (MulAut.congr eN).injective.comp
    (conjugation_injective_of_fitting N
      (local_generalizedFitting L T h.fitting h.twoCore T.isPGroup')
      (center_eq_bot_transport eN (alternatingGroup.center_eq_bot (by norm_num))))
  have hdim : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
    rw [e.action.linearEquiv.finrank_eq]
    simp
  have hlt : Nat.card D < 1440 := by
    have hle := Nat.card_le_card_of_injective _ hf
    rw [AlternatingSix.ShadowLocal.card_aut] at hle
    apply lt_of_le_of_ne hle
    intro heq
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le
      (by rw [AlternatingSix.ShadowLocal.card_aut, heq])
    exact aut_six_not_faithful_four (MulEquiv.ofBijective f hb) σ hdim
      (local_faithful h s T T.isPGroup')
  have hcardJ : Nat.card J = 720 := by
    rw [Nat.card_congr (e.action.groupEquiv.trans symmetricSymplecticEquiv.symm).toEquiv]
    exact Theory.SpecificGroups.SymmetricSix.s6_order
  have hcardD : Nat.card D = 720 := by
    apply Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos (α := D)).ne'
    · rw [← hcardJ]
      exact J.card_subgroup_dvd_card
    · omega
  have hJ : J = ⊤ := J.eq_top_of_card_eq (hcardJ.trans hcardD.symm)
  let a := lift_top_action (lift_top_action e.action hJ) (htop T)
  let b : ActionEquiv (symplecticNatural (k := ZMod 2) 2)
      (BinaryPermutation.naturalRepresentation (Fin 6)) := {
    groupEquiv := symmetricSymplecticEquiv.symm
    linearEquiv := naturalLinearEquiv.symm
    intertwines := by
      intro g v
      apply naturalLinearEquiv.injective
      rw [LinearEquiv.apply_symm_apply, naturalLinearEquiv_equivariant]
      change symplecticNatural 2 g v = symplecticNatural 2
        (symmetricSymplecticEquiv (symmetricSymplecticEquiv.symm g))
        (naturalLinearEquiv (naturalLinearEquiv.symm v))
      rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] }
  refine ⟨htop, Or.inl ⟨6, by decide, by decide, ⟨{
    groupEquiv := a.groupEquiv.trans b.groupEquiv
    linearEquiv := a.linearEquiv.trans b.linearEquiv
    intertwines := ?_ }⟩⟩⟩
  intro g v
  exact (congrArg b.linearEquiv (a.intertwines g v)).trans
    (b.intertwines (a.groupEquiv g) (a.linearEquiv v))

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.OuterNatural

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The proper local offender-group branch of B.5.1(1i), on the original
moved quotient. The complete corrected B.4.2 marking is the only
classification input. In particular, no ambient faithfulness, outer
commutativity, LT equality or natural-action conclusion is assumed. -/
theorem outer_natural_of_local_offender_ne {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (_hi : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)))
    (hne : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) ≠
      L.subgroupOf (L ⊔ (T : Subgroup G))) :
    (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧ OuterNaturalAction s.action := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  rw [local_generalizedFitting L T h.fitting h.twoCore T.isPGroup'] at hc
  cases hc with
  | linearTwo _ he _ _ _ => exact (hne he).elim
  | linearThree _ he _ _ => exact (hne he).elim
  | symplectic _ _ he _ _ => exact (hne he).elim
  | symplecticTwo e _ => exact OuterNatural.symplectic_endpoint h s T e
  | g2 _ _ he _ _ _ => exact (hne he).elim
  | g2Two e _ _ => exact OuterNatural.g2_endpoint h s T e
  | symmetric n hn e _ _ =>
    exact OuterNatural.symmetric_endpoint h s T (hn.imp_right Or.inl) e
  | alternatingSix he _ _ _ => exact (hne he).elim
  | alternatingSeven he _ _ _ _ _ => exact (hne he).elim
  | tripleSix he _ _ => exact (hne he).elim
  | binaryLinear _ _ he _ _ => exact (hne he).elim
  | orthogonalSix he _ _ _ _ => exact (hne he).elim
  | symmetricEight _ e _ =>
    exact OuterNatural.symmetric_endpoint h s T (Or.inr (Or.inr rfl)) e
  | exteriorFive he _ _ _ _ _ => exact (hne he).elim

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
