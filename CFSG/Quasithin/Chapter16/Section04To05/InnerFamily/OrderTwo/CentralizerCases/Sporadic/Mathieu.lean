module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Sporadic.Contracts
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The marked M₁₂ exception through a central cover

The C₂ × A₅ outer row of 16.1.5(4) identifies the actual projected
O²(C_L(r)) with A₅. Its central C₂ element gives a nonidentity inner
actor in C_H*(D*), distinct from the outer involution r*. Evenness then
gives the lower bound four inside H*. The intrinsic full A₅-fixer bound
supplies the reverse inequality and exponent two. Both actual image
isomorphisms are retained in `MathieuTwelveCase`; L is never identified
with its central quotient.

The last theorem is conditional on the earlier table and the independent
intrinsic A₅-fixer calculation, which the assembly owner must supply.
The product-residual argument follows the existing calculation in
`SylowSymmetry/ReverseDelta/Comparison/Products.lean`, reproduced privately
to avoid importing a later consumer of the order-two result.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4) and proof of 16.4.9(1), printed pp.1171 and 1189.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
open Subgroup Theory.GroupTheory OuterResidual
open OtherPreliminaries.Mathieu

variable {G : Type*} [Group G] {L : Subgroup G} {S : Type*} [Group S]

/-- On L*, the faithful model action is its genuine inner action. -/
theorem modelAction_inner_image (e : (L ⧸ center L) ≃* S) (x : actionImage L L) :
    modelAction L e x = MulAut.conj (imageEquivModel L e x) := by
  obtain ⟨b, hb, hbx⟩ := x.property
  let y : L := ⟨b, hb⟩
  have hx : x = ⟨actionMap (le_normalizer (H := L)) y,
      mem_actionImage _ y.property⟩ := Subtype.ext hbx.symm
  rw [hx, imageEquivModel_mk]
  change MulAut.centralQuotientAction e
    (quotientAction L (quotientMap L ⟨y, le_normalizer y.property⟩)) = _
  rw [quotientAction_mk]
  have hc : L.normalizerMonoidHom ⟨y, le_normalizer y.property⟩ = MulAut.conj y := by
    ext t
    rfl
  rw [hc]
  exact MulAut.centralQuotientAction_conj e y

/-- An element centralizing the marked residual lifts inside L* ⊆ H*. -/
theorem inner_image_mem_centralizer (e : (L ⧸ center L) ≃* S) (r : G)
    (s : S) (hs : s ∈ centralizer (modelResidual L e r : Set S)) :
    ((imageEquivModel L e).symm s : ActionQuotient L) ∈ residualCentralizer L r := by
  rw [residualCentralizer, mem_centralizer_iff]
  intro d hd
  have hdL := actionImage_mono L ((involutionResidual_le L r).trans inf_le_left) hd
  let dL : actionImage L L := ⟨d, hdL⟩
  have hdM : imageEquivModel L e dL ∈ modelResidual L e r := by
    rw [← image_modelResidual L e r]
    exact ⟨dL, hd, rfl⟩
  have hcomm := mem_centralizer_iff.mp hs _ hdM
  have he : dL * (imageEquivModel L e).symm s =
      (imageEquivModel L e).symm s * dL := by
    apply (imageEquivModel L e).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hcomm
  exact congrArg Subtype.val he

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

private noncomputable def botProdEquiv {H K : Type*} [Group H] [Group K]
    (N : Subgroup K) : (⊥ : Subgroup H).prod N ≃* N where
  toFun x := ⟨x.val.2, x.property.2⟩
  invFun x := ⟨(1, x), ⟨rfl, x.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (mem_bot.mp x.property.1).symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private noncomputable def productResidualEquiv : pResidual 2 (C2 × A5) ≃* A5 := by
  let N := (⊥ : Subgroup C2).prod (⊤ : Subgroup A5)
  let e : N ≃* A5 := (botProdEquiv (⊤ : Subgroup A5)).trans Subgroup.topEquiv
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPGroup 2 ((C2 × A5) ⧸ N) := by
    apply IsPGroup.of_card (n := 1)
    have hA : Nat.card A5 = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hn : Nat.card N = 60 := (Nat.card_congr e.toEquiv).trans hA
    have hg : Nat.card (C2 × A5) = 120 := by
      rw [Nat.card_prod, hA]
      norm_num [C2, Nat.card_eq_fintype_card]
    have hi := N.card_mul_index
    rw [hn, hg] at hi
    change Nat.card ((C2 × A5) ⧸ N) = 2
    rw [← Subgroup.index_eq_card]
    omega
  exact (MulEquiv.subgroupCongr
    (pResidual_eq_of_isPPerfect N perfect_twoPerfect hp)).trans e

private noncomputable def fixedResidualEquivA5 (a : MulAut S)
    (c : a.fixedSubgroup ≃* C2 × A5) : LiePreliminaries.fixedTwoResidual S a ≃* A5 :=
  ((pResidual 2 a.fixedSubgroup).equivMapOfInjective
    a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans
    (((c.subgroupMap _).trans (MulEquiv.subgroupCongr (map_pResidual 2 c))).trans
      productResidualEquiv)

private theorem product_center_nontrivial {H : Type*} [Group H]
    (c : H ≃* C2 × A5) : ∃ s : H, s ≠ 1 ∧ ∀ d : H, d * s = s * d := by
  let u : C2 := Multiplicative.ofAdd (1 : ZMod 2)
  refine ⟨c.symm (u, 1), ?_, ?_⟩
  · intro h
    have he := congrArg (fun x => (c x).1) h
    have hu : u ≠ 1 := by decide
    exact hu (by simpa only [MulEquiv.apply_symm_apply, map_one, Prod.fst_one] using he)
  · intro d
    apply c.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Prod.ext (mul_comm _ _) (by simp)

variable [Finite G] {T : Sylow 2 G} {z g r : G} {R : Subgroup G}

/-- The outer row forces the full ambient residual centralizer to have order at least four. -/
theorem centralizer_four_le_of_outer_product [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hodd : pPrimeCore 2 L = ⊥)
    (c : (modelAction L e (actionElement L r
      (h.sylow_normalizes (h.le_sylow hr)))).fixedSubgroup ≃* C2 × A5) :
    4 ≤ Nat.card (residualCentralizer L r) := by
  classical
  let a := modelAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr)))
  obtain ⟨s, hs, hc⟩ := product_center_nontrivial c
  have hsM : s.val ∈ centralizer (modelResidual L e r : Set S) := by
    rw [modelResidual_eq_fixedTwoResidual L e r
      (h.sylow_normalizes (h.le_sylow hr)) hodd, mem_centralizer_iff]
    rintro d ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hc v)
  let y : residualCentralizer L r :=
    ⟨(imageEquivModel L e).symm s.val, inner_image_mem_centralizer e r s.val hsM⟩
  let x : residualCentralizer L r := ⟨_, involution_mem_residualCentralizer L h hr⟩
  have hy : y ≠ 1 := by
    intro hy
    have he0 : ((imageEquivModel L e).symm s.val : ActionQuotient L) = 1 :=
      congrArg (fun v : residualCentralizer L r => (v : ActionQuotient L)) hy
    have he : (imageEquivModel L e).symm s.val = 1 := Subtype.ext he0
    have he' : s.val = 1 := by
      simpa only [MulEquiv.apply_symm_apply, map_one] using
        congrArg (imageEquivModel L e) he
    exact hs (Subtype.ext he')
  have hx : x ≠ 1 := by
    intro hx
    have ho := actionElement_order L h hr
    change orderOf x.val = orderOf r at ho
    rw [hx, OneMemClass.coe_one, orderOf_one, hr2] at ho
    norm_num at ho
  have hxy : x ≠ y := by
    intro hxy
    apply modelAction_outer L e r (h.sylow_normalizes (h.le_sylow hr)) hout
    refine ⟨s.val, ?_⟩
    have he := congrArg (fun v : residualCentralizer L r => modelAction L e v.val) hxy
    change a = modelAction L e ((imageEquivModel L e).symm s.val) at he
    simpa only [modelAction_inner_image, MulEquiv.apply_symm_apply] using he
  let := Fintype.ofFinite (residualCentralizer L r)
  have hthree : 3 ≤ Nat.card (residualCentralizer L r) := by
    have hh := Finset.card_le_card
      (Finset.subset_univ ({1, x, y} : Finset (residualCentralizer L r)))
    simpa [hx, hy, hxy, Ne.symm hx, Ne.symm hy, Nat.card_eq_fintype_card] using hh
  have heven := two_dvd_centralizer_card L h hr hr2
  omega

omit [Finite G] in
/-- Squares in the full model fixer control squares in the actual H* centralizer. -/
theorem elementary_of_fixer_square [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S)
    (hs : ∀ a : fixingSubgroup (MulAut S) (modelResidual L e r : Set S), a ^ 2 = 1) :
    IsElementaryAbelian 2 (residualCentralizer L r) := by
  have hsq (x : residualCentralizer L r) : x ^ 2 = 1 := by
    apply centralizerToFixer_injective L e r
    simpa only [map_pow, map_one] using hs (centralizerToFixer L e r x)
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

/-- The exact earlier outer row and intrinsic fixer calculation give every clause of case (III). -/
theorem mathieu_twelve_of_table_and_fixer
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e2 : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M12)
    (table : ∀ a : MulAut Sporadic.Mathieu.M12,
      orderOf a = 2 → M12InvolutionAlternative a)
    (fixer : M12FixerCalculation) :
    Nat.card (residualCentralizer L r) = 4 ∧
      IsElementaryAbelian 2 (residualCentralizer L r) ∧ MathieuTwelveCase L r := by
  let := h.component.quasisimple
  have hodd := component_oddCore hG h.toCentralComponentSetup
  let e := (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans e2
  let hn := h.sylow_normalizes (h.le_sylow hr)
  let a := modelAction L e (actionElement L r hn)
  have ha : orderOf a = 2 := (modelAction_order L e h hr).trans hr2
  have ho : ¬ ∃ x, a = MulAut.conj x := modelAction_outer L e r hn hout
  have hc : Nonempty (a.fixedSubgroup ≃* C2 × A5) := by
    rcases table a ha with ⟨hi, _⟩ | ⟨_, hc⟩
    · exact (ho hi).elim
    · exact hc
  obtain ⟨c⟩ := hc
  have heq : modelResidual L e r = LiePreliminaries.fixedTwoResidual _ a :=
    modelResidual_eq_fixedTwoResidual L e r hn hodd
  let d : modelResidual L e r ≃* A5 :=
    (MulEquiv.subgroupCongr heq).trans (fixedResidualEquivA5 a c)
  have hlo : 4 ≤ Nat.card (residualCentralizer L r) :=
    centralizer_four_le_of_outer_product e h hr hr2 hout hodd c
  have hi : Nat.card (residualCentralizer L r) ≤
      Nat.card (fixingSubgroup (MulAut Sporadic.Mathieu.M12) (modelResidual L e r : Set Sporadic.Mathieu.M12)) :=
    by
      apply Nat.card_le_card_of_injective (fun x : residualCentralizer L r => centralizerToFixer L e r x)
      exact centralizerToFixer_injective L e r
  obtain ⟨hcard, hsquare⟩ := fixer (modelResidual L e r) ⟨d⟩ (hlo.trans hi)
  exact ⟨le_antisymm (hi.trans hcard) hlo, elementary_of_fixer_square e hsquare,
    ⟨⟨imageEquivModel L e⟩, ⟨(residualImageEquivModelResidual L e r).trans d⟩⟩⟩

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Sporadic
