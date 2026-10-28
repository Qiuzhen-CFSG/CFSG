module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupTheory.DoubleCoverCentralizer.Action
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The J₂ pair-fixer reduction

The source calculation is a calculation on the actual embedded component in
the actual quotient `I/O₂(I)`, not on an abstract copy of either component.
This file proves the cover and fixed-component transport needed for that
calculation. The A₅ calculation remains explicit in `A5ComponentFixerBound`.
For PSL₃(2), the faithful order-four actor has a nontrivial inner involution
because Inn(J₂) has index two. Its fixed subgroup would contain the projected
PSL₃(2), contrary to the checked inner fixed-subgroup orders 240 and 1920.
This excludes the linear row without a new outer-centralizer calculation or
an assumption that E is elementary abelian.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(8), 16.1.7(3f,g), and 16.3.5, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko

open Subgroup Theory.GroupTheory ClassificationModels
open PerfectCentralCovering
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics

universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

abbrev A5 := alternatingGroup (Fin 5)
abbrev L3Two := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
abbrev J2 := Sporadic.LeechRelated.J2.Carrier

/- The intrinsic obligations retain the actual component embedding. -/
def A5ComponentFixerBound : Prop :=
  ∀ (r : MulAut J2) (K : Subgroup J2),
    orderOf r = 2 → IsComponentIn K r.fixedSubgroup →
    Nonempty (K ≃* A5) →
    Nat.card (fixingSubgroup (MulAut J2) (K : Set J2)) ≤ 4 ∧
      ∀ a : fixingSubgroup (MulAut J2) (K : Set J2), a ^ 2 = 1

/-- The projected component in the specified model, retaining its cover map. -/
noncomputable def projected (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2) : Subgroup J2 :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- The actual involution on the covering group induced by the distinguished `t`. -/
def coverInvolution (h : PairContext E L I t i) : MulAut I :=
  inducedAction E I h.normalizes ⟨t, h.t_mem⟩

/-- Its descended automorphism on the concrete J₂ carrier. -/
noncomputable def quotientInvolution (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2) : MulAut J2 :=
  (h.coreCover hG e).autMap (h.coreCover_kernel hG e) (coverInvolution h)

theorem quotientInvolution_order (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2) :
    orderOf (quotientInvolution h hG e) = 2 := by
  rw [quotientInvolution,
    orderOf_injective _ ((h.coreCover hG e).autMap_injective (h.coreCover_kernel hG e)),
    coverInvolution, orderOf_injective _ h.faithful,
    ← orderOf_injective E.subtype E.subtype_injective]
  exact h.setup.involution_t

theorem projected_ne_bot (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2) :
    projected h hG e ≠ ⊥ := by
  intro hp
  let := h.component_in_action_fixed.quasisimple
  have hb : L.subgroupOf I ≤ ⊥ := perfect_le_of_map_le_of_central_kernel
    (h.coreCover hG e).toMonoidHom (h.coreCover hG e).ker_le_center
    (L.subgroupOf I) ⊥ (by change projected h hG e ≤ _; simp [hp])
  exact h.component_in_action_fixed.ne_bot (le_bot_iff.mp hb)

/- A quotient map is injective on either of the two centerless component models. -/
theorem projected_equiv_of_centerless {M : Type*} [Group M]
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* J2) (eL : L ≃* M)
    (hM : Subgroup.center M = ⊥) :
    Nonempty (projected h hG e ≃* M) := by
  let f := h.coreCover hG e
  let j : L →* J2 := f.toMonoidHom.comp (inclusion h.proper.le)
  have hj : Function.Injective j := by
    apply j.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hxI : (⟨(x : G), h.proper.le x.property⟩ : I) ∈ center I :=
      f.ker_le_center hx
    have hxL : x ∈ center L := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun z : I => (z : G)) (mem_center_iff.mp hxI
        ⟨(y : G), h.proper.le y.property⟩)
    have hz : eL x ∈ center M := (centerCongr eL ⟨x, hxL⟩).property
    rw [hM, mem_bot] at hz
    exact mem_bot.mpr (eL.injective (hz.trans (map_one eL).symm))
  have hr : j.range = projected h hG e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), h.proper.le x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), hx⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans
    ((MonoidHom.ofInjective hj).symm.trans eL)⟩

theorem projected_a5_equiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2)
    (eL : Nonempty (L ≃* A5)) :
    Nonempty (projected h hG e ≃* A5) := by
  obtain ⟨eL⟩ := eL
  exact projected_equiv_of_centerless h hG e eL
    (alternatingGroup.center_eq_bot (by simp))

omit [Finite G] in
private theorem l3Two_equiv (hL : ClassicalGroup.IsPSL L 3 2) :
    Nonempty (L ≃* L3Two) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  exact ⟨(e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hF)).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two⟩

theorem projected_l3Two_equiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2)
    (hL : ClassicalGroup.IsPSL L 3 2) :
    Nonempty (projected h hG e ≃* L3Two) := by
  obtain ⟨eL⟩ := l3Two_equiv hL
  exact projected_equiv_of_centerless h hG e eL
    Matrix.PSL3Two.Automorphisms.center_psl_eq_bot

theorem projected_component (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2) :
    IsComponentIn (projected h hG e) (quotientInvolution h hG e).fixedSubgroup := by
  exact h.component_in_action_fixed.map_fixed_of_central_ker
    (coverInvolution h) (quotientInvolution h hG e)
    (h.coreCover hG e).toMonoidHom (h.coreCover hG e).surjective
    (h.coreCover hG e).ker_le_center
    (fun x => ((h.coreCover hG e).autMap_apply (h.coreCover_kernel hG e)
      (coverInvolution h) x).symm)
    (projected_ne_bot h hG e)

theorem a5_fixer_of_model (hmodel : A5ComponentFixerBound)
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G) :
    Nonempty ((I ⧸ pCore 2 I) ≃* J2) →
      Nonempty (L ≃* A5) → FourBound L I := by
  rintro ⟨e⟩ eL
  obtain ⟨hb, hsq⟩ := hmodel (quotientInvolution h hG e) (projected h hG e)
    (quotientInvolution_order h hG e) (projected_component h hG e)
    (projected_a5_equiv h hG e eL)
  exact fourBound_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e) hb hsq

open Theory.GroupTheory.DoubleCoverCentralizer
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem inner_index : (MulAut.conj : J2 →* MulAut J2).range.index = 2 := by
  have hc : Nat.card (MulAut.conj : J2 →* MulAut J2).range = 604800 :=
    (Nat.card_congr (MonoidHom.ofInjective J2Reduction.conj_injective).symm.toEquiv).trans
      FirstParabolic.card_carrier
  have ha : Nat.card (MulAut J2) = 1209600 :=
    (Nat.card_congr J2Reduction.fullAutomorphismEquiv.symm.toEquiv).trans
      (SecondParabolic.card_extension FirstParabolic.card_l₁)
  have hh := (MulAut.conj : J2 →* MulAut J2).range.card_mul_index
  rw [hc, ha] at hh
  omega

private theorem seven_not_dvd_inner_fixed (r : MulAut J2) (hr : orderOf r = 2)
    (hi : ∃ g : J2, r = MulAut.conj g) : ¬ 7 ∣ Nat.card r.fixedSubgroup := by
  rcases J2Reduction.inner_fixed_representatives r hr hi with he | he
  · obtain ⟨e⟩ := he
    have hA5 : Nat.card A5 = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hc : Nat.card r.fixedSubgroup = 240 := by
      rw [Nat.card_congr (e.trans J2Inner.a_centralizer_equiv).toEquiv,
        Nat.card_prod, hA5]
      norm_num [E4, C2, Nat.card_fun]
    rw [hc]
    decide
  · obtain ⟨e⟩ := he
    have hc : Nat.card r.fixedSubgroup = 1920 :=
      (Nat.card_congr e.toEquiv).trans FirstParabolic.card_l₁
    rw [hc]
    decide

private theorem four_action_no_seven {A : Type*} [Group A] [Finite A]
    (α : A →* MulAut J2) (hinj : Function.Injective α) (hA : Nat.card A = 4)
    (K : Subgroup J2) (hK : 7 ∣ Nat.card K)
    (hfix : ∀ a : A, ∀ x ∈ K, α a x = x) : False := by
  have hidx : (innerActors α).index ≤ 2 := innerActors_index_le_outer α inner_index.le
  have hdiv : 2 ∣ Nat.card (innerActors α) := by
    rcases innerActors_card α hA hidx with hc | hc
    · rw [hc]
    · rw [hc]
      decide
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  have hr : orderOf (α (a : A)) = 2 := by
    rw [orderOf_injective α hinj, orderOf_coe a, ha]
  have hi : ∃ g : J2, α (a : A) = MulAut.conj g := by
    obtain ⟨g, hg⟩ := a.property
    exact ⟨g, hg.symm⟩
  have hle : K ≤ (α (a : A)).fixedSubgroup := fun x hx =>
    (MulAut.mem_fixedSubgroup _ _).mpr (hfix a x hx)
  exact seven_not_dvd_inner_fixed _ hr hi (hK.trans (card_dvd_of_le hle))

/-- An order-four faithful actor cannot fix the projected PSL₃(2): its inner
involution would have a fixed subgroup with order divisible by seven. -/
theorem l3Two_context_impossible (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* J2)
    (hL : ClassicalGroup.IsPSL L 3 2) : False := by
  let f := h.coreCover hG e
  let α := (f.autMap (h.coreCover_kernel hG e)).comp
    (inducedAction E I h.normalizes)
  have hinj : Function.Injective α :=
    (f.autMap_injective (h.coreCover_kernel hG e)).comp h.faithful
  obtain ⟨eL⟩ := projected_l3Two_equiv h hG e hL
  have hseven : 7 ∣ Nat.card (projected h hG e) := by
    rw [Nat.card_congr eL.toEquiv, Matrix.PSL3Two.card_PSL]
    decide
  apply four_action_no_seven α hinj h.card (projected h hG e) hseven
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  change f.autMap _ (inducedAction E I h.normalizes a) (f.toMonoidHom y) = f.toMonoidHom y
  rw [f.autMap_apply]
  apply congrArg f.toMonoidHom
  apply Subtype.ext
  change (a : G) * (y : G) * (a : G)⁻¹ = (y : G)
  have hc := h.centralizes a.property y hy
  change (y : G) * (a : G) = (a : G) * (y : G) at hc
  rw [← hc]
  simp [mul_assoc]

/-- The linear row is excluded using the actor already supplied by the context. -/
theorem l3Two_fixer (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G) :
    Nonempty ((I ⧸ pCore 2 I) ≃* J2) →
      ClassicalGroup.IsPSL L 3 2 → Nat.card (pairFixer L I) < 4 := by
  rintro ⟨e⟩ hL
  exact (l3Two_context_impossible h hG e hL).elim

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
