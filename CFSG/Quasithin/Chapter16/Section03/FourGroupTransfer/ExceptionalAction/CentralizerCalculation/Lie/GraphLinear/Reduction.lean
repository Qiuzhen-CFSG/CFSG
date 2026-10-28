module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import Theory.GroupAction.PerfectCentralQuotient.ComponentImage
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The actual projected component and divisibility of its fixer

A faithful group of order four fixing L embeds in its full automorphism
fixer. Faithful descent through the central cover preserves this divisibility.
Condition (E1) identifies the kernel with the entire center, and the component
image theorem places the actual image of L in the full quotient fixed subgroup.
When L is binary PSL₂, its trivial center makes the projection injective on L.
No injectivity of the projection on I is asserted.

These reductions are for the graph rows of Aschbacher–Smith 16.1.7(3b–c)
and their exclusion in 16.3.5, printed pp.1172–1173 and 1178–1179.
The graph row requires a bound on the two-part of the full fixer order:
its odd part is not discarded or assumed trivial. The intrinsic matrix
calculations remain separate proof obligations.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.GraphLinear
universe u
variable {G : Type u} [Group G] {E L I : Subgroup G} {t i : G}

/-- The image of the actual embedded L under the two-core quotient map. -/
@[expose] def corePairComponent (L I : Subgroup G) : Subgroup (I ⧸ pCore 2 I) :=
  (L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))

/-- The faithful ambient actor embeds into the full pair fixer. -/
theorem four_dvd_pairFixer (h : PairContext E L I t i) :
    4 ∣ Nat.card (pairFixer L I) := by
  let f : E →* pairFixer L I :=
    (inducedAction E I h.normalizes).codRestrict _ (by
      intro e
      rw [pairFixer, mem_fixingSubgroup_iff]
      intro l hl
      apply Subtype.ext
      change (e : G) * (l : G) * (e : G)⁻¹ = (l : G)
      rw [← mem_centralizer_iff.mp (h.centralizes e.property) l hl]
      group)
  have hf : Function.Injective f := fun a b hab =>
    h.faithful (congrArg Subtype.val hab)
  simpa only [h.card] using Subgroup.card_dvd_of_injective f hf

variable [Finite G] {𝒦 : GroupClass.{u}}

/-- Divisibility survives the genuine central-cover descent. -/
theorem four_dvd_corePairFixer (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) :
    4 ∣ Nat.card (fixingSubgroup (MulAut (I ⧸ pCore 2 I))
      (corePairComponent L I : Set (I ⧸ pCore 2 I))) :=
  (four_dvd_pairFixer h).trans
    ((h.coreCover hG (MulEquiv.refl _)).card_fixing_dvd
      (h.coreCover_kernel hG (MulEquiv.refl _)) (L.subgroupOf I))

private theorem quotientAction_injective_of_center_eq {K : Type*} [Group K]
    [Group.IsPerfect K] (N : Subgroup K) [N.Characteristic] (hN : center K = N) :
    Function.Injective N.quotientAut := by
  subst N
  exact MulAut.quotient_center_injective

private theorem component_image_of_center_eq {K : Type*} [Group K]
    (N : Subgroup K) [N.Characteristic] (hN : center K = N)
    (a : MulAut K) (P : Subgroup K) (hP : IsComponentIn P a.fixedSubgroup) :
    IsComponentIn (P.map (QuotientGroup.mk' N)) (N.quotientAut a).fixedSubgroup := by
  subst N
  exact a.component_image_in_quotient_fixed P hP

/-- The actual descended distinguished action is still an involution. -/
theorem coreAction_orderOf (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) :
    orderOf ((pCore 2 I).quotientAut h.involutionAction) = 2 := by
  let := h.component.quasisimple.toIsPerfect
  exact (orderOf_injective _ (quotientAction_injective_of_center_eq _
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)) _).trans
      h.involutionAction_orderOf

/-- Relative component membership in the full fixed subgroup downstairs. -/
theorem component_in_coreAction_fixed (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) :
    IsComponentIn (corePairComponent L I)
      ((pCore 2 I).quotientAut h.involutionAction).fixedSubgroup := by
  exact component_image_of_center_eq _
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)
    h.involutionAction _ h.component_in_action_fixed

private theorem center_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : center Y = ⊥) : center X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hy : e x ∈ center Y := ((centerCongr e) ⟨x, hx⟩).property
  have hy1 : e x = 1 := by simpa only [hY, mem_bot] using hy
  exact mem_bot.mpr (e.injective (hy1.trans e.map_one.symm))

/-- A centerless L is identified with its actual image, retaining the cover of I. -/
noncomputable def corePairComponentEquiv (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) (hL : center L = ⊥) :
    L ≃* corePairComponent L I :=
  (subgroupOfEquivOfLe h.proper.le).symm.trans
    (MulEquiv.ofBijective ((QuotientGroup.mk' (pCore 2 I)).subgroupMap (L.subgroupOf I))
      ⟨(QuotientGroup.mk' (pCore 2 I)).subgroupMap_injective_of_ker_le_center
        (by rw [QuotientGroup.ker_mk',
              ← hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component])
        (L.subgroupOf I) (center_bot_of_equiv (subgroupOfEquivOfLe h.proper.le) hL),
        (QuotientGroup.mk' (pCore 2 I)).subgroupMap_surjective (L.subgroupOf I)⟩)

/-- The equivalence uses the original quotient map on every element of L. -/
theorem corePairComponentEquiv_apply (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) (hL : center L = ⊥) (x : L) :
    (corePairComponentEquiv hG h hL x : I ⧸ pCore 2 I) =
      QuotientGroup.mk' (pCore 2 I) ⟨x, h.proper.le x.property⟩ := by rfl

/-- The binary PSL₂ model is retained by the actual projection of L. -/
theorem corePairComponent_isPSL_two (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) {n : ℕ}
    (hL : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    ClassicalGroup.IsPSL (corePairComponent L I) 2 (2 ^ n) := by
  obtain ⟨F, hF, hfinite, hcard, ⟨e⟩⟩ := hL
  let := hF
  let := hfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hcenter : center L = ⊥ :=
    center_bot_of_equiv e (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot (F := F))
  exact ⟨F, hF, hfinite, hcard, ⟨(corePairComponentEquiv hG h hcenter).symm.trans e⟩⟩

/-- The quotient inherits quasisimplicity from the actual component I. -/
theorem core_quotient_quasisimple (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) : IsQuasisimple (I ⧸ pCore 2 I) := by
  let := h.component.quasisimple
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let e := QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)
  let : IsSimpleGroup (I ⧸ pCore 2 I) := e.symm.isSimpleGroup
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 I))
    (QuotientGroup.mk'_surjective _)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.GraphLinear
