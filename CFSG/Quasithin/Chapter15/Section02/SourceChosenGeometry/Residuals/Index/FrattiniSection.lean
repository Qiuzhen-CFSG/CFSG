module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.CoreAction
public import Theory.GroupTheory.CharacteristicFrattiniAction
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# The actual elementary-nine action on the residual core section

Put Q = O₂(K) and W = Q/Φ(Q). Characteristic two and the Burnside basis
kernel theorem identify the image E of K on W with the literal K/Q.
Thus E is elementary of order nine. When Kc = K, the partner action
normalizes E, and its centralizer of E is exactly the kernel of its
action on K/Q. In particular every three-element centralizes E.

If Mc contains an element of order nine, its faithful action on W has
order nine, centralizes E, and has a nonidentity cube in E. The final
applications discharge the original residual identity and index once this
specific root is excluded in the actual partner image. This exclusion
still needs the ambient chosen-module hypotheses; no bound on the whole
core section is inferred from the dimension of the chosen module.

The root exclusion and ambient Held exclusion remain with
`qt-e-152-residual-geometry`. The parent `qt-e-152-plane-geometry` supplies
the earlier premises of `ResidualInput` and owns final source assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4), printed p.1111, the equality-row centralizer calculation.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The intrinsic image of K on the Frattini quotient of its own two-core. -/
@[expose] noncomputable def residualCoreFrattiniImage (H : Subgroup G) :
    Subgroup (MulAut (pCore 2 (residual H) ⧸ frattini (pCore 2 (residual H)))) :=
  (frattiniConjugation (pCore 2 (residual H))).range

/-- Characteristic two makes the intrinsic section-action kernel exactly O₂(K). -/
theorem ResidualInput.residualCoreFrattini_kernel
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    (frattiniConjugation (pCore 2 (residual H))).ker = pCore 2 (residual H) :=
  pCore_frattini_action_kernel 2 d.residual_characteristic_two

/-- The actual quotient K/O₂(K) identifies with its intrinsic action image. -/
noncomputable def ResidualInput.residualCoreFrattiniEquiv
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    XiQuotient (residual H) ≃* residualCoreFrattiniImage H :=
  (QuotientGroup.quotientMulEquivOfEq d.residualCoreFrattini_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange (frattiniConjugation (pCore 2 (residual H))))

/-- The image equivalence preserves the original quotient map and conjugation. -/
theorem ResidualInput.residualCoreFrattiniEquiv_mk
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) (x : residual H) :
    (d.residualCoreFrattiniEquiv (QuotientGroup.mk' (pCore 2 (residual H)) x) :
      MulAut (pCore 2 (residual H) ⧸ frattini (pCore 2 (residual H)))) =
        frattiniConjugation (pCore 2 (residual H)) x := by
  simp only [ResidualInput.residualCoreFrattiniEquiv]
  rfl

/-- The intrinsic action image is elementary abelian of exponent three. -/
theorem ResidualInput.residualCoreFrattini_elementary
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    IsElementaryAbelian 3 (residualCoreFrattiniImage H) := by
  let e := d.residualCoreFrattiniEquiv.symm.trans (residualQuotientEquiv H d.quotient.some)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

/-- The intrinsic action image has order nine. -/
theorem ResidualInput.residualCoreFrattini_card
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    Nat.card (residualCoreFrattiniImage H) = 9 := by
  let e := d.residualCoreFrattiniEquiv.symm.trans (residualQuotientEquiv H d.quotient.some)
  exact (Nat.card_congr e.toEquiv).trans WreathModel.cubicBase_card

omit [Finite G] in
private theorem coreFrattiniAction_restriction
    (he : partnerSpan H Mc = residual H) (hKM : residual H ≤ Mc) (x : residual H) :
    partnerCoreFrattiniAction H Mc he (inclusion hKM x) =
      frattiniConjugation (pCore 2 (residual H)) x := by
  apply MulEquiv.ext
  intro y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini (pCore 2 (residual H))) y
  rfl

omit [Finite G] in
/-- Partner conjugation intertwines the intrinsic residual action. -/
theorem partnerCoreFrattiniAction_conj
    (he : partnerSpan H Mc = residual H) (x : Mc) (y : residual H) :
    partnerCoreFrattiniAction H Mc he x * frattiniConjugation (pCore 2 (residual H)) y *
      (partnerCoreFrattiniAction H Mc he x)⁻¹ =
        frattiniConjugation (pCore 2 (residual H))
          ((residual H).normalizerMonoidHom
            (inclusion (partner_normalizes_of_eq H Mc he) x) y) := by
  have hh := congrArg (quotientAut (frattini (pCore 2 (residual H))))
    (characteristic_conjNormal_equivariant (pCore 2 (residual H))
      ((residual H).normalizerMonoidHom
        (inclusion (partner_normalizes_of_eq H Mc he) x)) y)
  simpa only [map_mul,map_inv,partnerCoreFrattiniAction,partnerCoreAction,
    frattiniConjugation,MonoidHom.comp_apply] using hh

omit [Finite G] in
/-- The actual partner image normalizes the residual image on the same section. -/
theorem partnerCoreFrattiniImage_normalizes
    (he : partnerSpan H Mc = residual H) :
    (partnerCoreFrattiniAction H Mc he).range ≤
      normalizer (residualCoreFrattiniImage H : Set _) := by
  rintro _ ⟨x,rfl⟩
  rw [mem_normalizer_iff]
  intro b
  let a := (residual H).normalizerMonoidHom
    (inclusion (partner_normalizes_of_eq H Mc he) x)
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨a y,(partnerCoreFrattiniAction_conj he x y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨a.symm y,?_⟩
    have hh := partnerCoreFrattiniAction_conj he x (a.symm y)
    change _ = frattiniConjugation (pCore 2 (residual H)) (a (a.symm y)) at hh
    rw [a.apply_symm_apply,hy] at hh
    exact mul_left_cancel (mul_right_cancel hh)

/-- The elementary-nine residual image lies in the actual partner image. -/
theorem ResidualInput.residualCoreFrattini_le_partner_image
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    residualCoreFrattiniImage H ≤ (partnerCoreFrattiniAction H Mc he).range := by
  obtain ⟨P,hP⟩ := d.localInput
  have hKM : residual H ≤ Mc := le_sup_left.trans hP.overgroup
  rintro _ ⟨x,rfl⟩
  exact ⟨inclusion hKM x,coreFrattiniAction_restriction he hKM x⟩

/-- Centralizing the section image is equivalent to acting trivially on K/O₂(K). -/
theorem ResidualInput.coreFrattini_centralizer_iff
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (x : Mc) :
    partnerCoreFrattiniAction H Mc he x ∈
      centralizer (residualCoreFrattiniImage H : Set _) ↔
        partnerQuotientAction H Mc he x = 1 := by
  let a := (residual H).normalizerMonoidHom
    (inclusion (partner_normalizes_of_eq H Mc he) x)
  constructor
  · intro hx
    apply MulEquiv.ext
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual H)) y
    change quotientAut (pCore 2 (residual H)) a (QuotientGroup.mk' _ y) = _
    rw [quotientAut_apply_mk,MulAut.one_apply]
    apply d.residualCoreFrattiniEquiv.injective
    apply Subtype.ext
    rw [d.residualCoreFrattiniEquiv_mk,d.residualCoreFrattiniEquiv_mk]
    have hc := (hx (frattiniConjugation (pCore 2 (residual H)) y) ⟨y,rfl⟩).symm
    calc
      frattiniConjugation (pCore 2 (residual H)) (a y) =
          partnerCoreFrattiniAction H Mc he x *
            frattiniConjugation (pCore 2 (residual H)) y *
              (partnerCoreFrattiniAction H Mc he x)⁻¹ :=
        (partnerCoreFrattiniAction_conj he x y).symm
      _ = frattiniConjugation (pCore 2 (residual H)) y := by
        rw [hc,mul_inv_cancel_right]
  · intro hx
    exact quotient_kernel_frattiniImage_le_centralizer (pCore 2 (residual H))
      (pCore_isPGroup (p := 2) (G := residual H)) ⟨a,hx,rfl⟩

/-- The literal prime-to-three residual centralizes the intrinsic image. -/
theorem ResidualInput.threeResidual_coreFrattini_centralizes
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    (primeToResidual 3 Mc).map (partnerCoreFrattiniAction H Mc he) ≤
      centralizer (residualCoreFrattiniImage H : Set _) := by
  rintro _ ⟨x,hx,rfl⟩
  exact (d.coreFrattini_centralizer_iff he x).mpr
    (d.threeResidual_le_action_kernel_of_eq he hx)

/-- Every three-element of the partner centralizes the intrinsic image. -/
theorem ResidualInput.three_element_coreFrattini_centralizes
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (x : Mc) {n : ℕ}
    (hx : x ^ (3 ^ n) = 1) :
    partnerCoreFrattiniAction H Mc he x ∈
      centralizer (residualCoreFrattiniImage H : Set _) :=
  d.threeResidual_coreFrattini_centralizes he
    ⟨x,mem_primeToResidual_of_pow hx,rfl⟩

/-- An order-nine partner element gives a nontrivial cubic root in the intrinsic image. -/
theorem ResidualInput.order_nine_coreFrattini_root
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (x : Mc) (hx : orderOf x = 9) :
    let a := partnerCoreFrattiniAction H Mc he x
    orderOf a = 9 ∧ a ∈ centralizer (residualCoreFrattiniImage H : Set _) ∧
      a ^ 3 ∈ residualCoreFrattiniImage H ∧ a ^ 3 ≠ 1 := by
  have hp : x ^ (3 ^ 2) = 1 := by
    rw [show 3 ^ 2 = 9 by decide,← hx,pow_orderOf_eq_one]
  have hp3 : (x ^ 3) ^ 3 = 1 := by simpa only [← pow_mul, show 3 * 3 = 3 ^ 2 from rfl] using hp
  have hxK := d.cubic_mem_residual_of_eq he (x ^ 3) hp3
  have ho : orderOf (partnerCoreFrattiniAction H Mc he x) = 9 :=
    (d.partnerCoreFrattiniAction_preserves_three_order he x hp).trans hx
  refine ⟨ho,d.three_element_coreFrattini_centralizes he x hp,?_,?_⟩
  · obtain ⟨P,hP⟩ := d.localInput
    have hKM : residual H ≤ Mc := le_sup_left.trans hP.overgroup
    rw [← map_pow]
    exact ⟨⟨(x ^ 3 : Mc),hxK⟩,
      (coreFrattiniAction_restriction he hKM ⟨(x ^ 3 : Mc),hxK⟩).symm⟩
  · exact pow_ne_one_of_lt_orderOf (by decide) (by rw [ho]; decide)

/-- Excluding such roots in the actual partner image gives the original residual identity.
The ambient root exclusion remains with this module's owner. -/
theorem ResidualInput.residual_equality_of_no_coreFrattini_root
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (hroot : ∀ he : partnerSpan H Mc = residual H,
      ∀ a : MulAut (pCore 2 (residual H) ⧸ frattini (pCore 2 (residual H))),
      a ∈ (partnerCoreFrattiniAction H Mc he).range →
      a ∈ centralizer (residualCoreFrattiniImage H : Set _) →
      a ^ 3 ∈ residualCoreFrattiniImage H → a ^ 3 ≠ 1 → orderOf a ≠ 9) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  apply d.residual_equality_of_no_order_nine
  intro he x hx
  obtain ⟨ho,hc,hp,hn⟩ := d.order_nine_coreFrattini_root he x hx
  exact hroot he _ ⟨x,rfl⟩ hc hp hn ho

/-- The same root exclusion supplies the literal index bound consumed by full support. -/
theorem ResidualInput.index_coprime_of_no_coreFrattini_root
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (hroot : ∀ he : partnerSpan H Mc = residual H,
      ∀ a : MulAut (pCore 2 (residual H) ⧸ frattini (pCore 2 (residual H))),
      a ∈ (partnerCoreFrattiniAction H Mc he).range →
      a ∈ centralizer (residualCoreFrattiniImage H : Set _) →
      a ^ 3 ∈ residualCoreFrattiniImage H → a ^ 3 ≠ 1 → orderOf a ≠ 9) :
    Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index := by
  apply d.index_coprime_of_no_order_nine
  intro he x hx
  obtain ⟨ho,hc,hp,hn⟩ := d.order_nine_coreFrattini_root he x hx
  exact hroot he _ ⟨x,rfl⟩ hc hp hn ho

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
