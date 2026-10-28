module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Transport to the pointwise fixer of the actual residual

The conjugation map identifies H* = N_G(L)/C_G(L) with a subgroup of
Aut(L). Perfectness makes its action on every marked model of L/Z(L)
faithful. Its residual centralizer therefore embeds into the pointwise
fixer of the actual image of D = O²(C_L(r)), not an abstract group of the
same isomorphism type. The canonical `centerQuotientEquivActionImage`
identifies this marking with L*.

The fixed-residual projection theorem retains central covers and proves
that this image is O² of the fixed subgroup in the quotient model. An
odd-times-two bound for its pointwise fixer gives a Sylow subgroup of
C_H*(D*) of order two, since the actual r* has order two. Thus odd
residuals are permitted. The family-specific fixer calculations and the
exceptional E₄ cases remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2–16.1.5 and the proof of 16.4.9(1), printed pp.1170–1172 and 1189.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases
open OuterResidual

section
variable {G : Type*} [Group G] (L : Subgroup G)

/-- The actual faithful action of H* on L. -/
def quotientAction : ActionQuotient L →* MulAut L :=
  (QuotientGroup.kerLift L.normalizerMonoidHom).comp
    (QuotientGroup.quotientMulEquivOfEq L.normalizerMonoidHom_ker.symm).toMonoidHom

/-- The quotient removes exactly the kernel of conjugation on L. -/
theorem quotientAction_injective : Function.Injective (quotientAction L) := by
  intro a b hab
  apply (QuotientGroup.quotientMulEquivOfEq L.normalizerMonoidHom_ker.symm).injective
  exact QuotientGroup.kerLift_injective L.normalizerMonoidHom hab

/-- The induced action agrees with ambient conjugation on representatives. -/
theorem quotientAction_mk (a : normalizer (L : Set G)) :
    quotientAction L (quotientMap L a) = L.normalizerMonoidHom a := rfl

variable {S : Type*} [Group S]

/-- The induced action on a specified model of the central quotient. -/
def modelAction (e : (L ⧸ center L) ≃* S) : ActionQuotient L →* MulAut S :=
  (MulAut.centralQuotientAction e).comp (quotientAction L)

/-- Perfectness preserves faithfulness through the central quotient. -/
theorem modelAction_injective [Group.IsPerfect L] (e : (L ⧸ center L) ≃* S) :
    Function.Injective (modelAction L e) :=
  (MulAut.centralQuotientAction_injective e).comp (quotientAction_injective L)

/-- The canonical projection followed by the specified model marking. -/
def modelProjection (e : (L ⧸ center L) ≃* S) : L →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

/-- Identify the actual subgroup L* with the specified model of L/Z(L). -/
noncomputable def imageEquivModel (e : (L ⧸ center L) ≃* S) : actionImage L L ≃* S :=
  (centerQuotientEquivActionImage L).symm.trans e

/-- The identification of L* preserves the specified quotient map. -/
theorem imageEquivModel_mk (e : (L ⧸ center L) ≃* S) (x : L) :
    imageEquivModel L e
      ⟨actionMap (le_normalizer (H := L)) x, mem_actionImage _ x.property⟩ =
      modelProjection L e x := by
  change e ((centerQuotientEquivActionImage L).symm _) = e _
  congr 1
  apply (centerQuotientEquivActionImage L).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The model action and projection commute with the actual conjugation action. -/
theorem modelAction_apply (e : (L ⧸ center L) ≃* S)
    (a : normalizer (L : Set G)) (x : L) :
    modelAction L e (quotientMap L a) (modelProjection L e x) =
      modelProjection L e (L.normalizerMonoidHom a x) :=
  MulAut.centralQuotientAction_apply e _ x

/-- The actual embedded image of O²(C_L(r)) under the marked central quotient. -/
def modelResidual (e : (L ⧸ center L) ≃* S) (r : G) : Subgroup S :=
  ((involutionResidual L r).subgroupOf L).map (modelProjection L e)

/-- Commutation with D* is pointwise fixation of its marked model image. -/
theorem modelAction_mem_fixer (e : (L ⧸ center L) ≃* S) (r : G)
    (a : residualCentralizer L r) :
    modelAction L e a ∈ fixingSubgroup (MulAut S) (modelResidual L e r : Set S) := by
  rw [mem_fixingSubgroup_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective
    ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))) a.val
  change quotientMap L b = a.val at hb
  change modelAction L e a.val (modelProjection L e x) = modelProjection L e x
  rw [← hb, modelAction_apply]
  have hxD : actionMap (le_normalizer (H := L)) x ∈
      actionImage L (involutionResidual L r) := mem_actionImage _ hx
  have hc := mem_centralizer_iff.mp a.property _ hxD
  rw [← hb] at hc
  change quotientMap L ⟨x, le_normalizer x.property⟩ * quotientMap L b =
    quotientMap L b * quotientMap L ⟨x, le_normalizer x.property⟩ at hc
  have he : actionMap (le_normalizer (H := L)) (L.normalizerMonoidHom b x) =
      actionMap (le_normalizer (H := L)) x := by
    change quotientMap L (b * ⟨x, le_normalizer x.property⟩ * b⁻¹) = _
    rw [map_mul, map_mul, map_inv, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    rfl
  rw [← imageEquivModel_mk, ← imageEquivModel_mk]
  exact congrArg (imageEquivModel L e) (Subtype.ext he)

/-- The centralizer maps to the pointwise fixer of the actual residual image. -/
def centralizerToFixer (e : (L ⧸ center L) ≃* S) (r : G) :
    residualCentralizer L r →* fixingSubgroup (MulAut S) (modelResidual L e r : Set S) :=
  ((modelAction L e).comp (residualCentralizer L r).subtype).codRestrict _
    (modelAction_mem_fixer L e r)

/-- Faithfulness of the model action restricts to its residual centralizer. -/
theorem centralizerToFixer_injective [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* S) (r : G) : Function.Injective (centralizerToFixer L e r) := by
  intro a b hab
  apply Subtype.ext
  exact modelAction_injective L e (congrArg Subtype.val hab)

/-- An intrinsic model fixer bound controls the full residual centralizer. -/
theorem centralizer_card_dvd_fixer [Finite G] [Finite S] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* S) (r : G) :
    Nat.card (residualCentralizer L r) ∣
      Nat.card (fixingSubgroup (MulAut S) (modelResidual L e r : Set S)) :=
  card_dvd_of_injective (centralizerToFixer L e r) (centralizerToFixer_injective L e r)

/-- An element outside C_G(L)L induces an outer automorphism of L. -/
theorem action_not_inner {r : G} (hn : r ∈ normalizer (L : Set G))
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    ¬ ∃ x : L, ComponentTransfer.Intrinsic.action hn = MulAut.conj x := by
  rintro ⟨x, hx⟩
  let a : normalizer (L : Set G) := ⟨r, hn⟩
  let b : normalizer (L : Set G) := ⟨x, le_normalizer x.property⟩
  have hb : L.normalizerMonoidHom b = MulAut.conj x := by ext y; rfl
  have hk : a / b ∈ L.normalizerMonoidHom.ker := by
    change L.normalizerMonoidHom (a / b) = 1
    rw [map_div, hb]
    change ComponentTransfer.Intrinsic.action hn / MulAut.conj x = 1
    simp only [hx, div_eq_mul_inv, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hmem : r / x.val * x.val ∈ centralizer (L : Set G) ⊔ L :=
    (centralizer (L : Set G) ⊔ L).mul_mem
      ((le_sup_left : centralizer (L : Set G) ≤ centralizer (L : Set G) ⊔ L) hk)
      ((le_sup_right : L ≤ centralizer (L : Set G) ⊔ L) x.property)
  exact hout (by simpa only [div_mul_cancel] using hmem)

variable [Finite G] {T : Sylow 2 G} {z g : G} {R : Subgroup G}

/-- The given element centralizes its fixed two-residual in H*. -/
theorem involution_mem_residualCentralizer (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) :
    actionElement L r (h.sylow_normalizes (h.le_sylow hr)) ∈ residualCentralizer L r := by
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hc := (involutionResidual_le L r hx).2
  have he : x * (⟨r, h.sylow_normalizes (h.le_sylow hr)⟩ : normalizer (L : Set G)) =
      (⟨r, h.sylow_normalizes (h.le_sylow hr)⟩ : normalizer (L : Set G)) * x :=
    Subtype.ext (mem_centralizer_singleton_iff.mp hc)
  exact congrArg (quotientMap L) he

/-- Tight embedding preserves the order of every element of R in H*. -/
theorem actionElement_order (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) :
    orderOf (actionElement L r (h.sylow_normalizes (h.le_sylow hr))) = orderOf r := by
  exact (orderOf_injective
    (actionMap (h.le_sylow.trans h.sylow_normalizes))
    (actionMap_injective _ (faithful h)) (⟨r, hr⟩ : R)).trans (orderOf_coe _).symm

/-- The actual involution r* makes the residual centralizer even. -/
theorem two_dvd_centralizer_card (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2) :
    2 ∣ Nat.card (residualCentralizer L r) := by
  let a : residualCentralizer L r := ⟨_, involution_mem_residualCentralizer L h hr⟩
  have ha : orderOf a = 2 := (orderOf_coe a).symm.trans ((actionElement_order L h hr).trans hr2)
  exact ha ▸ orderOf_dvd_natCard a

/-- The two-part of an odd-times-two bound, with an actual Sylow witness. -/
theorem sylow_card_two_of_card_dvd_twice_odd (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2) {m : ℕ} (hm : Odd m)
    (hd : Nat.card (residualCentralizer L r) ∣ 2 * m) :
    ∃ P : Sylow 2 (residualCentralizer L r), Nat.card P = 2 := by
  classical
  let P : Sylow 2 (residualCentralizer L r) := Classical.choice inferInstance
  refine ⟨P, Nat.dvd_antisymm ?_ (P.dvd_card_of_dvd_card (two_dvd_centralizer_card L h hr hr2))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hPm : Nat.card P ∣ 2 * m := P.card_subgroup_dvd_card.trans hd
  rw [hn] at hPm ⊢
  exact ((hm.coprime_two_left.pow_left n).dvd_mul_right).mp hPm

/-- Projection of the actual fixed two-residual, including nontrivial central covers. -/
theorem modelResidual_eq_fixedTwoResidual [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (r : G) (hn : r ∈ normalizer (L : Set G))
    (hodd : pPrimeCore 2 L = ⊥) :
    modelResidual L e r = LiePreliminaries.fixedTwoResidual S
      (modelAction L e (actionElement L r hn)) := by
  have he : ((involutionResidual L r).subgroupOf L) =
      LiePreliminaries.fixedTwoResidual L (ComponentTransfer.Intrinsic.action hn) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((involutionResidual_le L r).trans inf_le_left)]
    let c := ComponentTransfer.Intrinsic.centralizerEquivFixed hn
    rw [LiePreliminaries.fixedTwoResidual, ← map_pResidual 2 c, map_map, map_map]
    rfl
  change ((involutionResidual L r).subgroupOf L).map (modelProjection L e) = _
  rw [he]
  exact LiePreliminaries.map_fixedTwoResidual hodd e _

omit [Finite G] in
/-- Outer automorphisms of a perfect group stay outer in the central quotient. -/
theorem modelAction_outer [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (r : G) (hn : r ∈ normalizer (L : Set G))
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    ¬ ∃ x : S, modelAction L e (actionElement L r hn) = MulAut.conj x := by
  exact fun hi => action_not_inner L hn hout ((MulAut.centralQuotientAction_inner_iff e _).mp hi)

/-- The marked quotient automorphism has the order of the original element of R. -/
theorem modelAction_order [IsQuasisimple L] (e : (L ⧸ center L) ≃* S)
    (h : IntersectionSetup T z L g R) {r : G} (hr : r ∈ R) :
    orderOf (modelAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))) =
      orderOf r :=
  (orderOf_injective _ (modelAction_injective L e) _).trans (actionElement_order L h hr)

/-- Case (I) follows from the pointwise-fixer bound in the actual quotient model. -/
theorem alternative_of_fixer_card_dvd_twice_odd [Finite S] [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2) {m : ℕ} (hm : Odd m)
    (hd : Nat.card (fixingSubgroup (MulAut S) (modelResidual L e r : Set S)) ∣ 2 * m) :
    ResidualCentralizerAlternative T L r :=
  Or.inl (sylow_card_two_of_card_dvd_twice_odd L h hr hr2 hm
    ((centralizer_card_dvd_fixer L e r).trans hd))

end

section
variable {G : Type*} [Group G] (L : Subgroup G) {S : Type*} [Group S]

/-- The canonical marking of L* carries D* onto the actual projected residual. -/
theorem image_modelResidual (e : (L ⧸ center L) ≃* S) (r : G) :
    ((actionImage L (involutionResidual L r)).subgroupOf (actionImage L L)).map
      (imageEquivModel L e).toMonoidHom = modelResidual L e r := by
  ext s
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := ha
    let x : L := ⟨b, (involutionResidual_le L r hb).1⟩
    refine ⟨x, hb, ?_⟩
    rw [← imageEquivModel_mk]
    exact congrArg (imageEquivModel L e) (Subtype.ext hba)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨actionMap (le_normalizer (H := L)) x, mem_actionImage _ x.property⟩,
      mem_actionImage _ hx, imageEquivModel_mk L e x⟩

/-- Identify D* with its marked model image, without identifying a central cover with its quotient. -/
noncomputable def residualImageEquivModelResidual (e : (L ⧸ center L) ≃* S) (r : G) :
    actionImage L (involutionResidual L r) ≃* modelResidual L e r :=
  (subgroupOfEquivOfLe (actionImage_mono L
    ((involutionResidual_le L r).trans inf_le_left))).symm.trans
      (((imageEquivModel L e).subgroupMap _).trans
        (MulEquiv.subgroupCongr (image_modelResidual L e r)))

variable [Finite G] {T : Sylow 2 G} {z g : G} {R : Subgroup G}

/-- Excluding divisibility by four suffices because the centralizer contains r*. -/
theorem sylow_card_two_of_not_four_dvd (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hd : ¬ 4 ∣ Nat.card (residualCentralizer L r)) :
    ∃ P : Sylow 2 (residualCentralizer L r), Nat.card P = 2 := by
  classical
  let P : Sylow 2 (residualCentralizer L r) := Classical.choice inferInstance
  have htwo : 2 ∣ Nat.card P := P.dvd_card_of_dvd_card (two_dvd_centralizer_card L h hr hr2)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hnlt : n < 2 := by
    by_contra! hn2
    apply hd
    have hh : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hn2
    rw [← hn] at hh
    exact hh.trans P.card_subgroup_dvd_card
  refine ⟨P, ?_⟩
  interval_cases n
  · rw [hn] at htwo
    norm_num at htwo
  · exact hn

/-- Case (I) needs only the intrinsic pointwise-fixer order to be indivisible by four. -/
theorem alternative_of_fixer_not_four_dvd [Finite S] [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (h : IntersectionSetup T z L g R)
    {r : G} (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hd : ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut S) (modelResidual L e r : Set S))) :
    ResidualCentralizerAlternative T L r :=
  Or.inl (sylow_card_two_of_not_four_dvd L h hr hr2
    (fun hc => hd (hc.trans (centralizer_card_dvd_fixer L e r))))


end

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases
