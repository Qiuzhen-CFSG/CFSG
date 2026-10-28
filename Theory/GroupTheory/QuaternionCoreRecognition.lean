module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.SpecificGroups.QuaternionEightResidual
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Product.CubicGeneration
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient

/-!
# Recognition above a self-centralizing quaternion subgroup

For a normal Q₈ with centralizer of order two, conjugation bounds the ambient
order by 48. If 16 divides the ambient order and its six order-four elements
are fused, orbit-stabilizer forces a factor three, so the order is exactly 48
and conjugation covers Aut(Q₈).

An element of order three acts nontrivially on Q₈. The existing quaternion
cubic model identifies their join with SL₂(3). Its index two and the cubic
difference generators identify that join with the literal two-residual,
which is characteristic. No splitting over the quaternion subgroup is assumed.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.4.3, printed pp.416–417, the automorphism and local model step.
-/

open Subgroup
namespace Theory.GroupTheory.QuaternionCoreRecognition
variable {G : Type*} [Group G] [Finite G]


omit [Finite G] in
/-- Fusing the six elements of order four in a normal quaternion subgroup
forces a factor three in the ambient order. -/
public theorem three_dvd_card (Q : Subgroup G) [Q.Normal]
    (e : Q ≃* QuaternionGroup 2)
    (hf : ∀ x y : Q, orderOf x = 4 → orderOf y = 4 → IsConj (x : G) y) :
    3 ∣ Nat.card G := by
  let : MulAction G Q := MulAction.compHom Q (MulAut.conjNormal : G →* MulAut Q)
  let x : Q := e.symm (QuaternionGroup.a 1)
  have hx : orderOf x = 4 := (e.symm.orderOf_eq _).trans QuaternionGroup.orderOf_a_one
  have horbit : MulAction.orbit G x = {y : Q | orderOf y = 4} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ((MulAut.conjNormal g).orderOf_eq x).trans hx
    · intro hy
      obtain ⟨g, hg⟩ := isConj_iff.mp (hf x y hx hy)
      exact ⟨g, Subtype.ext hg⟩
  have hcard : Nat.card (MulAction.orbit G x) = 6 := by
    rw [horbit]
    let E : {y : Q // orderOf y = 4} ≃ {y : QuaternionGroup 2 // orderOf y = 4} :=
      e.toEquiv.subtypeEquiv (fun y => (e.orderOf_eq y).symm ▸ Iff.rfl)
    change Nat.card {y : Q // orderOf y = 4} = 6
    rw [Nat.card_congr E]
    have hiff (y : QuaternionGroup 2) : orderOf y = 4 ↔ y ^ 2 ≠ 1 := by
      cases y with
      | a i => rw [QuaternionGroup.orderOf_a]; fin_cases i <;> decide
      | xa i => rw [QuaternionGroup.orderOf_xa]; fin_cases i <;> decide
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card]
    decide
  have hmul := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)
  rw [Nat.card_prod, hcard] at hmul
  exact (show 3 ∣ 6 by decide).trans ⟨_, hmul.symm⟩


/-- The exact order and full conjugation action above the quaternion subgroup. -/
public theorem full_automizer (Q : Subgroup G) [Q.Normal]
    (e : Q ≃* QuaternionGroup 2)
    (hc : Nat.card (centralizer (Q : Set G)) = 2)
    (h16 : 16 ∣ Nat.card G)
    (hf : ∀ x y : Q, orderOf x = 4 → orderOf y = 4 → IsConj (x : G) y) :
    Nat.card G = 48 ∧ Function.Surjective (MulAut.conjNormal : G →* MulAut Q) := by
  let f : G →* MulAut Q := MulAut.conjNormal
  have hk : Nat.card f.ker = 2 := by rw [MulAut.conjNormal_ker_eq_centralizer, hc]
  have hAut : Nat.card (MulAut Q) = 24 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans QuaternionGroup.card_mulAut_two
  have hmul := f.ker.card_mul_index
  rw [index_ker, hk] at hmul
  have hd : Nat.card G ∣ 48 := by
    rw [← hmul]
    exact Nat.mul_dvd_mul_left 2 (hAut ▸ f.range.card_subgroup_dvd_card)
  have h48 : 48 ∣ Nat.card G :=
    (show Nat.Coprime 16 3 by decide).mul_dvd_of_dvd_of_dvd h16 (three_dvd_card Q e hf)
  have heq : Nat.card G = 48 := Nat.dvd_antisymm hd h48
  refine ⟨heq, MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq ?_)⟩
  rw [hAut]
  omega

/-- The actual two-residual is SL₂(3); its characteristicity is inherited
from the residual construction. -/
public theorem residual_model (Q : Subgroup G) [Q.Normal]
    (e : Q ≃* QuaternionGroup 2)
    (hc : Nat.card (centralizer (Q : Set G)) = 2)
    (hG : Nat.card G = 48) :
    Nonempty ((pResidual 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) 3 (by
    rw [← Nat.card_eq_fintype_card, hG]; decide)
  let f : G →* MulAut Q := MulAut.conjNormal
  have hk : Nat.card f.ker = 2 := by rw [MulAut.conjNormal_ker_eq_centralizer, hc]
  have hne : f x ≠ 1 := by
    intro h
    have hm : x ∈ f.ker := h
    have hd := orderOf_dvd_natCard (⟨x, hm⟩ : f.ker)
    rw [← Subgroup.orderOf_coe, hx, hk] at hd
    norm_num at hd
  have hpow : (f x) ^ 3 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  obtain ⟨⟨eL⟩, _⟩ := quaternion_cubic_extension_recognition Q ⟨e⟩ x hx (f x)
    (fun q => MulAut.conjNormal_apply x q) hne
  let L := Q ⊔ zpowers x
  have hLcard : Nat.card L = 24 := by
    rw [Nat.card_congr eL.toEquiv,
      ← Nat.card_congr GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toEquiv]
    exact GLS3.Chapter5.SchurPresentation.binaryTetrahedral_card
  have hLi : L.index = 2 := by
    have h := L.card_mul_index
    rw [hLcard, hG] at h
    omega
  let : L.Normal := L.normal_of_index_eq_two hLi
  have hRle : pResidual 2 G ≤ L := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    exact hLi
  have hxR : x ∈ pResidual 2 G := mem_pResidual_of_orderOf_coprime (by rw [hx]; decide)
  have hQR : Q ≤ pResidual 2 G := quaternion_le_normal_of_cubic_actor
    Q (pResidual 2 G) e x hxR (f x) hpow hne (fun q => MulAut.conjNormal_apply x q)
  have hRL : pResidual 2 G = L := le_antisymm hRle (sup_le hQR (zpowers_le.mpr hxR))
  exact ⟨(MulEquiv.subgroupCongr hRL).trans eL⟩

end Theory.GroupTheory.QuaternionCoreRecognition
