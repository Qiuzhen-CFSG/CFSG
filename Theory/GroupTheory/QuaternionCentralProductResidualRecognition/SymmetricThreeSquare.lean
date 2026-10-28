module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.QuaternionCentralProductNineAction

/-!
# The SL₂(3) factors above a symmetric-three square

A self-centralizing normal quaternion central product with quotient S₃ × S₃
has two independent cubic actors. Their quaternion-cubic extensions are
actual commuting SL₂(3) subgroups and generate exactly the two-residual.
The quotient calculation bounds that residual by 288; this avoids treating
an arbitrary subgroup of index four as normal.

Source: Aschbacher–Smith, 13.5.15(9) and 13.5.16, printed pp.920–921;
Aschbacher, Sporadic Groups (1994), Hypothesis45.1, printed p.242.
-/

@[expose] public section
namespace Subgroup

private theorem extension_card {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : Nat.card B = 8) (x : G) (hx : orderOf x = 3)
    (hn : x ∈ normalizer (B : Set G)) : Nat.card (B ⊔ zpowers x : Subgroup G) = 24 := by
  have hc : Nat.card (zpowers x) = 3 := (Nat.card_zpowers x).trans hx
  rw [card_sup_eq_mul_of_normalizes_of_disjoint B (zpowers x) (zpowers_le.mpr hn)
    (disjoint_of_coprime_natCard (by rw [hB, hc]; decide)), hB, hc]

/-- The specified quaternion-cubic joins have order 24, commute, intersect
in the original center, and generate the actual two-residual. -/
private theorem extensions_product_of_bound
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hbound : Nat.card (pResidual 2 G) ≤ 288)
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
  have hle : L ⊔ R ≤ pResidual 2 G :=
    sup_le (sup_le hBres (zpowers_le.mpr hxres)) (sup_le hCres (zpowers_le.mpr hyres))
  exact ⟨hL, hR, hLRcomm, hinter,
    eq_of_le_of_card_ge hle (hLR ▸ hbound)⟩

private theorem residual_card_le_of_quotient
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcore : Q = pCore 2 G)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nat.card (pResidual 2 G) ≤ 288 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : f.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by rw [hk, hcore]; exact pCore_isPGroup
  have hquot := SymmetricThreeProductResidual.residual_core_quotient_card_of_surjective f hf hp
  have hle : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ Q := by
    rw [hcore]
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  have hcard : Nat.card (pCore 2 (pResidual 2 G)) ≤ 32 := by
    have h := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rwa [card_map_of_injective (pResidual 2 G).subtype_injective, d.card] at h
  have hmul := (pCore 2 (pResidual 2 G)).index_mul_card
  rw [index_eq_card, hquot] at hmul
  omega

/-- The original quaternion core and S₃ × S₃ quotient give the correct
centralizer order, 1152. -/
theorem card_eq_1152_of_quaternion_product_quotient_symmetricThree_square
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nat.card G = 1152 := by
  have hidx : Q.index = 36 := by
    rw [index_eq_card, Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have h := Q.card_mul_index
  rw [d.card, hidx] at h
  exact h.symm

/-- The actual Sylow three-subgroup supplies independent actors on the
original two quaternion factors. -/
theorem independent_cubics_of_quaternion_product_quotient_symmetricThree_square
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nonempty (QuaternionIndependentCubics
      (d.left.map Q.subtype) (d.right.map Q.subtype)) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hP : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity,
      card_eq_1152_of_quaternion_product_quotient_symmetricThree_square Q d e]
    decide +kernel
  have hj : d.left.map Q.subtype ⊔ d.right.map Q.subtype = Q := by
    rw [← map_sup, d.span, ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨a, _⟩ := independent_cubics_of_nine_subgroup
    (d.left.map Q.subtype) (d.right.map Q.subtype) (P : Subgroup G)
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
    (by rw [← map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective, d.intersection_card])
    (by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      exact congrArg Subtype.val (d.commute b hb c hc))
    (by rwa [hj]) hP (by rw [hj, Q.normalizer_eq_top]; exact le_top)
  exact ⟨a⟩

/-- The two actual SL₂(3) factors and their common center are constructed
from the quaternion core and the symmetric-three-square quotient. -/
theorem quaternion_residual_central_product_of_symmetricThree_square
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcore : Q = pCore 2 G)
    (hcentral : centralizer (Q : Set G) ≤ Q)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nonempty (QuaternionResidualCentralProduct Q d) := by
  obtain ⟨actors⟩ :=
    independent_cubics_of_quaternion_product_quotient_symmetricThree_square Q d hcentral e
  have hB : Nonempty (d.left.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
  have hC : Nonempty (d.right.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
  obtain ⟨hLmodel, hLcore⟩ := quaternion_cubic_extension_recognition
    (d.left.map Q.subtype) hB (actors.x : G) actors.x_order (actors.actionB actors.x)
    (actors.actionB_apply actors.x) actors.x_actionB_ne_one
  obtain ⟨hRmodel, hRcore⟩ := quaternion_cubic_extension_recognition
    (d.right.map Q.subtype) hC (actors.y : G) actors.y_order (actors.actionC actors.y)
    (actors.actionC_apply actors.y) actors.y_actionC_ne_one
  obtain ⟨_, _, hcomm, hinter, hspan⟩ := extensions_product_of_bound Q d
    (residual_card_le_of_quotient Q d hcore e) actors
  exact ⟨{
    left := d.left.map Q.subtype ⊔ zpowers (actors.x : G)
    right := d.right.map Q.subtype ⊔ zpowers (actors.y : G)
    left_model := hLmodel
    right_model := hRmodel
    left_contains := le_sup_left
    right_contains := le_sup_left
    left_core := hLcore
    right_core := hRcore
    commute := hcomm
    intersection := hinter
    span := hspan }⟩

end Subgroup
end
