module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Product.CubicGeneration
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.IndexNormal

/-!
# The residual product of independent cubic extensions

Adjoin each independent cubic actor to its quaternion factor. The resulting
subgroups commute and each has order 24. Their joint subgroup is the product
of the normal quaternion group of order 32 with the actor group of order nine,
so it has order 288 and index two. It therefore contains the two-residual.
Conversely, the cubic actors belong to the residual, and their action
differences generate both quaternion factors. The product-order formula then
identifies the common intersection with the original center of order two.

The joins are retained as actual ambient subgroups, independently of any
recognition of their isomorphism types. No self-centralizer assumption is
needed once independent actors have been supplied.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace Subgroup

/-- Independent cubic extensions of commuting factors commute elementwise. -/
public theorem QuaternionIndependentCubics.extensions_commute
    {G : Type*} [Group G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) :
    ∀ l ∈ B ⊔ zpowers (actors.x : G), ∀ r ∈ C ⊔ zpowers (actors.y : G), l*r=r*l := by
  have hBR : C ⊔ zpowers (actors.y : G) ≤ centralizer (B : Set G) :=
    sup_le (fun c hc b hb => hcomm b hb c hc) (zpowers_le.mpr actors.y_centralizes)
  have hxR : C ⊔ zpowers (actors.y : G) ≤ centralizer {(actors.x : G)} := by
    apply sup_le
    · intro c hc
      exact mem_centralizer_singleton_iff.mpr (actors.x_centralizes c hc)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr actors.commute.symm.eq)
  have hLR : B ⊔ zpowers (actors.x : G) ≤
      centralizer ((C ⊔ zpowers (actors.y : G) : Subgroup G) : Set G) := by
    apply sup_le (le_centralizer_iff.mp hBR)
    apply zpowers_le.mpr
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hxR hr)
  intro l hl r hr
  exact (hLR hl r hr).symm

private theorem extension_card {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : Nat.card B = 8) (x : G) (hx : orderOf x = 3)
    (hn : x ∈ normalizer (B : Set G)) : Nat.card (B ⊔ zpowers x : Subgroup G) = 24 := by
  have hc : Nat.card (zpowers x) = 3 := (Nat.card_zpowers x).trans hx
  rw [card_sup_eq_mul_of_normalizes_of_disjoint B (zpowers x) (zpowers_le.mpr hn)
    (disjoint_of_coprime_natCard (by rw [hB, hc]; decide)), hB, hc]

/-- The specified quaternion-cubic joins have order 24, commute, intersect
in the original center, and generate the actual two-residual. -/
public theorem QuaternionIndependentCubics.extensions_product
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hG : Nat.card G = 576)
    (actors : QuaternionIndependentCubics (d.left.map Q.subtype) (d.right.map Q.subtype)) :
    let L := d.left.map Q.subtype ⊔ zpowers (actors.x : G)
    let R := d.right.map Q.subtype ⊔ zpowers (actors.y : G)
    Nat.card L = 24 ∧ Nat.card R = 24 ∧
    (∀ l ∈ L, ∀ r ∈ R, l * r = r * l) ∧
    L ⊓ R = (center Q).map Q.subtype ∧ L ⊔ R = pResidual 2 G := by
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  let L := B ⊔ zpowers (actors.x : G)
  let R := C ⊔ zpowers (actors.y : G)
  change Nat.card L = 24 ∧ Nat.card R = 24 ∧ _
  let eB : B ≃* QuaternionGroup 2 :=
    (d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some
  let eC : C ≃* QuaternionGroup 2 :=
    (d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hC : Nat.card C = 8 := by
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hL : Nat.card L = 24 := extension_card B hB _ actors.x_order
    (actors.normalizes_left actors.x.property)
  have hR : Nat.card R = 24 := extension_card C hC _ actors.y_order
    (actors.normalizes_right actors.y.property)
  have hj : B ⊔ C = Q := by
    rw [show B ⊔ C = (d.left ⊔ d.right).map Q.subtype from (map_sup _ _ _).symm, d.span]
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, mem_top _, rfl⟩⟩
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  have hLRcomm := actors.extensions_commute hcomm
  have hjLR : L ⊔ R = Q ⊔ actors.A := by
    calc
      L ⊔ R = (B ⊔ C) ⊔ (zpowers (actors.x : G) ⊔ zpowers (actors.y : G)) := by
        dsimp [L, R]
        ac_rfl
      _ = Q ⊔ actors.A := congrArg₂ (· ⊔ ·) hj actors.generated
  have hQA : Nat.card (Q ⊔ actors.A : Subgroup G) = 288 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Q actors.A
      (by rw [Q.normalizer_eq_top]; exact le_top)
      (disjoint_of_coprime_natCard (by rw [d.card, actors.card]; decide)), d.card, actors.card]
  have hLR : Nat.card (L ⊔ R : Subgroup G) = 288 := hjLR ▸ hQA
  have hI : Nat.card (L ⊓ R : Subgroup G) = 2 := by
    have hn : R ≤ centralizer (L : Set G) := fun r hr l hl => hLRcomm l hl r hr
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes L R
      (hn.trans (centralizer_le_normalizer _))
    rw [hL, hR, hLR] at hc
    omega
  have hZ : (center Q).map Q.subtype = B ⊓ C := by
    rw [d.center_eq, map_inf _ _ Q.subtype Q.subtype_injective]
  have hinter : L ⊓ R = (center Q).map Q.subtype := by
    symm
    apply eq_of_le_of_card_ge
    · rw [hZ]
      exact inf_le_inf le_sup_left le_sup_left
    · rw [card_map_of_injective Q.subtype_injective, d.center_card, hI]
  have hindex : (L ⊔ R).index = 2 := by
    have hc := (L ⊔ R).card_mul_index
    rw [hLR, hG] at hc
    omega
  let : (L ⊔ R).Normal := normal_of_index_eq_two hindex
  have hresle : pResidual 2 G ≤ L ⊔ R := by
    apply sInf_le
    refine ⟨inferInstance, ?_⟩
    apply IsPGroup.of_card (n := 1)
    exact hindex
  have hxres : (actors.x : G) ∈ pResidual 2 G :=
    mem_pResidual_of_orderOf_coprime (by rw [actors.x_order]; decide)
  have hyres : (actors.y : G) ∈ pResidual 2 G :=
    mem_pResidual_of_orderOf_coprime (by rw [actors.y_order]; decide)
  have hx3 : actors.x^3=1 := by
    apply actors.A.subtype_injective
    simpa using (orderOf_dvd_iff_pow_eq_one.mp (actors.x_order ▸ dvd_rfl))
  have hy3 : actors.y^3=1 := by
    apply actors.A.subtype_injective
    simpa using (orderOf_dvd_iff_pow_eq_one.mp (actors.y_order ▸ dvd_rfl))
  have hBres : B ≤ pResidual 2 G :=
    quaternion_le_normal_of_cubic_actor B (pResidual 2 G) eB _ hxres (actors.actionB actors.x)
      (by rw [← map_pow, hx3, map_one]) actors.x_actionB_ne_one (actors.actionB_apply actors.x)
  have hCres : C ≤ pResidual 2 G :=
    quaternion_le_normal_of_cubic_actor C (pResidual 2 G) eC _ hyres (actors.actionC actors.y)
      (by rw [← map_pow, hy3, map_one]) actors.y_actionC_ne_one (actors.actionC_apply actors.y)
  exact ⟨hL, hR, hLRcomm, hinter, le_antisymm
    (sup_le (sup_le hBres (zpowers_le.mpr hxres)) (sup_le hCres (zpowers_le.mpr hyres))) hresle⟩

end Subgroup
