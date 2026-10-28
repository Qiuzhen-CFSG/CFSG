module
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Product
public import Theory.GroupTheory.CommutingCentralizerFactors

/-!
# Order-four centralizers in quaternion extensions of order 288

A self-centralizing normal Q₈ * Q₈ in a group of order 288 admits independent
cubic actors. Their quaternion-cubic joins are commuting copies of SL₂(3)
and exhaust the group. Every order-four element of the original quaternion
product lies in one factor, where its centralizer is its cyclic subgroup.
Its whole centralizer is therefore C₄ * SL₂(3), with intersection generated
by its square. The cyclic factor and the two original quaternion embeddings
are retained throughout.

Source: Aschbacher--Smith, 14.3.22, printed p.999. The square dichotomy used
below is the calculation from `QuaternionCentralProductFactors`; the cubic
extensions use the existing binary tetrahedral recognition.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem quaternion_square_dichotomy (B : Subgroup G)
    (e : B ≃* QuaternionGroup 2) (z : G) (hz : z ∈ B)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (b : G) (hb : b ∈ B) :
    (b = 1 ∨ b = z) ∨ b ^ 2 = z := by
  have hfinite : ∀ z b : QuaternionGroup 2, z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z := by decide
  let zz : B := ⟨z, hz⟩
  let bb : B := ⟨b, hb⟩
  have hz1' : e zz ≠ 1 := by
    intro hh
    apply hz1
    exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
  have hz2' : (e zz) ^ 2 = 1 := by
    rw [← map_pow]
    have hh : zz ^ 2 = 1 := Subtype.ext hz2
    rw [hh, map_one]
  rcases hfinite (e zz) (e bb) hz1' hz2' with (hb1 | hbz) | hb2
  · exact Or.inl (Or.inl (congrArg Subtype.val
      (e.injective (hb1.trans e.map_one.symm))))
  · exact Or.inl (Or.inr (congrArg Subtype.val (e.injective hbz)))
  · apply Or.inr
    have hh : bb ^ 2 = zz := e.injective (by rw [map_pow]; exact hb2)
    exact congrArg Subtype.val hh

omit [Finite G] in
theorem quaternion_product_order_four_mem_factor (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) (hx : x ∈ B ⊔ C) (hx4 : orderOf x = 4) : x ∈ B ∨ x ∈ C := by
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := hC
  obtain ⟨zz, hz1, _⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  let z : G := zz
  have hz1' : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hz2 : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := zz)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hx' : x ∈ (↑(B ⊔ C) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hx'
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  rcases quaternion_square_dichotomy B eB z zz.property.1 hz1' hz2 b hb with
    (hb1 | hbz) | hb2
  · exact Or.inr (by simpa [hb1] using hc)
  · exact Or.inr (C.mul_mem (hbz ▸ zz.property.2) hc)
  rcases quaternion_square_dichotomy C eC z zz.property.2 hz1' hz2 c hc with
    (hc1 | hcz) | hc2
  · exact Or.inl (by simpa [hc1] using hb)
  · exact Or.inl (B.mul_mem hb (hcz ▸ zz.property.1))
  have hsq : (b * c) ^ 2 = 1 := by
    rw [(show Commute b c from hcomm b hb c hc).mul_pow, hb2, hc2, ← pow_two, hz2]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [hx4] at hdvd
  norm_num at hdvd


private abbrev BT := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action] Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

private theorem bt_four_centralizer :
    ∀ x y : BT, x^2 ≠ 1 → x^4 = 1 → y*x=x*y →
      y=1 ∨ y=x ∨ y=x^2 ∨ y=x^3 := by decide +kernel

omit [Finite G] in
/-- An order-four element of SL₂(3) has precisely its own cyclic centralizer. -/
theorem sl23_centralizer_four (L : Subgroup G)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (t : G) (ht : t ∈ L) (ht4 : orderOf t = 4) :
    L ⊓ centralizer ({t} : Set G) = zpowers t := by
  let f := e.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  let x : L := ⟨t,ht⟩
  have ho : orderOf (f x) = 4 := (f.orderOf_eq x).trans ((orderOf_coe x).symm.trans ht4)
  have h2 : (f x)^2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ho] at hd
    norm_num at hd
  have h4 : (f x)^4 = 1 := ho ▸ pow_orderOf_eq_one (f x)
  apply le_antisymm
  · rintro y ⟨hy,hyc⟩
    let yy : L := ⟨y,hy⟩
    have hh : f yy * f x = f x * f yy := by
      rw [←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp hyc))
    have hpow (n : ℕ) (hn : f yy = (f x)^n) : y = t^n :=
      congrArg Subtype.val (f.injective (hn.trans (map_pow f x n).symm))
    rcases bt_four_centralizer (f x) (f yy) h2 h4 hh with h | h | h | h
    · have he : y=1 := congrArg Subtype.val (f.injective (h.trans (map_one f).symm))
      exact he ▸ (zpowers t).one_mem
    · have he : y=t := congrArg Subtype.val (f.injective h)
      exact he ▸ mem_zpowers t
    · exact (hpow 2 h) ▸ (zpowers t).pow_mem (mem_zpowers t) 2
    · exact (hpow 3 h) ▸ (zpowers t).pow_mem (mem_zpowers t) 3
  · exact zpowers_le.mpr ⟨ht,mem_centralizer_singleton_iff.mpr rfl⟩

private theorem card_sl23 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [←Nat.card_congr GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  change 8 * Nat.card (ZMod 3) = 24
  rw [Nat.card_zmod]

/-- Independent cubic actors exhaust an order-288 quaternion extension by
its two commuting binary tetrahedral factors. -/
theorem quaternion_binary_tetrahedral_factors
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcard : Nat.card G = 288)
    (hself : centralizer (Q : Set G) ≤ Q) :
    ∃ L R : Subgroup G,
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty (R ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      d.left.map Q.subtype ≤ L ∧ d.right.map Q.subtype ≤ R ∧
      (∀ l ∈ L, ∀ r ∈ R, l*r=r*l) ∧
      L ⊓ R = (center Q).map Q.subtype ∧ L ⊔ R = ⊤ := by
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
  have hC : Nonempty (C ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
  have hinter : Nat.card (B ⊓ C : Subgroup G) = 2 := by
    rw [←map_inf _ _ Q.subtype Q.subtype_injective,card_map_of_injective Q.subtype_injective]
    exact d.intersection_card
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  have hjoin : B ⊔ C = Q := by
    rw [←map_sup,d.span,←MonoidHom.range_eq_map, Q.range_subtype]
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := default
  have hP : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity,hcard]
    decide +kernel
  obtain ⟨actors⟩ := exists_independent_cubics_of_order_nine B C P hB hC hinter hcomm
    (by simpa only [hjoin] using hself) hP
    (by rw [hjoin,Q.normalizer_eq_top]; exact le_top)
  let L := B ⊔ zpowers (actors.x : G)
  let R := C ⊔ zpowers (actors.y : G)
  obtain ⟨hLm,_⟩ := quaternion_cubic_extension_recognition B hB _ actors.x_order
    (actors.actionB actors.x) (actors.actionB_apply actors.x) actors.x_actionB_ne_one
  obtain ⟨hRm,_⟩ := quaternion_cubic_extension_recognition C hC _ actors.y_order
    (actors.actionC actors.y) (actors.actionC_apply actors.y) actors.y_actionC_ne_one
  have hLRcomm := actors.extensions_commute hcomm
  have hQA : Nat.card (Q ⊔ actors.A : Subgroup G) = 288 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Q actors.A
      (by rw [Q.normalizer_eq_top]; exact le_top)
      (disjoint_of_coprime_natCard (by rw [d.card,actors.card]; decide)),d.card,actors.card]
  have hgen : L ⊔ R = ⊤ := by
    have he : L ⊔ R = Q ⊔ actors.A := by
      calc
        L ⊔ R = (B ⊔ C) ⊔ (zpowers (actors.x : G) ⊔ zpowers (actors.y : G)) := by
          dsimp only [L,R]; ac_rfl
        _ = Q ⊔ actors.A := congrArg₂ (· ⊔ ·) hjoin actors.generated
    rw [he]
    apply eq_top_of_card_eq
    exact hQA.trans hcard.symm
  have hLc : Nat.card L = 24 := (Nat.card_congr hLm.some.toEquiv).trans
    card_sl23
  have hRc : Nat.card R = 24 := (Nat.card_congr hRm.some.toEquiv).trans
    card_sl23
  have hIc : Nat.card (L ⊓ R : Subgroup G) = 2 := by
    have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes L R
      ((show R ≤ centralizer (L : Set G) from fun r hr l hl => hLRcomm l hl r hr).trans
        (centralizer_le_normalizer _))
    rw [hLc,hRc,hgen,Nat.card_congr topEquiv.toEquiv,hcard] at he
    omega
  refine ⟨L,R,hLm,hRm,le_sup_left,le_sup_left,hLRcomm,?_,hgen⟩
  symm
  apply eq_of_le_of_card_ge
  · rw [d.center_eq,map_inf _ _ Q.subtype Q.subtype_injective]
    exact inf_le_inf le_sup_left le_sup_left
  · rw [card_map_of_injective Q.subtype_injective,d.center_card,hIc]

/-- The marked order-four centralizer in an order-288 quaternion extension
is a central product of its own cyclic group and an actual SL₂(3). -/
theorem quaternion_extension_order_four_centralizer
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcard : Nat.card G = 288)
    (hself : centralizer (Q : Set G) ≤ Q)
    (t : Q) (ht : orderOf t = 4) :
    ∃ B : Subgroup G,
      Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      zpowers (t : G) ≤ centralizer (B : Set G) ∧
      zpowers (t : G) ⊓ B = zpowers ((t : G)^2) ∧
      zpowers (t : G) ⊔ B = centralizer ({(t : G)} : Set G) := by
  obtain ⟨L,R,hL,hR,hBL,hCR,hcomm,hinter,hgen⟩ :=
    quaternion_binary_tetrahedral_factors Q d hcard hself
  have ht4 : orderOf (t : G) = 4 := (orderOf_coe t).trans ht
  have hz : (center Q).map Q.subtype = zpowers ((t : G)^2) := by
    symm
    apply eq_of_le_of_card_ge
    · exact zpowers_le.mpr (mem_map_of_mem Q.subtype (d.square_mem_center t))
    · rw [card_map_of_injective Q.subtype_injective,d.center_card,
        Nat.card_zpowers,orderOf_pow,ht4]
      decide
  have step (L R : Subgroup G)
      (hL : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
      (hR : Nonempty (R ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
      (hc : ∀ l ∈ L, ∀ r ∈ R, l*r=r*l)
      (hi : L ⊓ R = zpowers ((t : G)^2)) (hg : L ⊔ R = ⊤)
      (htL : (t : G) ∈ L) :
      ∃ B : Subgroup G,
        Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
        zpowers (t : G) ≤ centralizer (B : Set G) ∧
        zpowers (t : G) ⊓ B = zpowers ((t : G)^2) ∧
        zpowers (t : G) ⊔ B = centralizer ({(t : G)} : Set G) := by
    have hRC : R ≤ centralizer (L : Set G) := fun r hr l hl => hc l hl r hr
    refine ⟨R,hR,zpowers_le.mpr (fun r hr => (hc t htL r hr).symm),?_,?_⟩
    · apply le_antisymm
      · exact (inf_le_inf_right R (zpowers_le.mpr htL)).trans_eq hi
      · exact le_inf (zpowers_le.mpr ((zpowers (t : G)).pow_mem (mem_zpowers _) 2))
          (hi ▸ inf_le_right)
    · have he := sup_inf_centralizer_singleton_of_centralizing_supplement L R (t : G)
        (hRC.trans (centralizer_le_normalizer _))
        (fun r hr => mem_centralizer_singleton_iff.mpr (hc t htL r hr).symm)
      rw [hg,top_inf_eq,sl23_centralizer_four L hL.some t htL ht4] at he
      exact he.symm
  rcases quaternion_product_order_four_mem_factor d.left d.right d.left_model d.right_model
      d.intersection_card d.commute t (d.span ▸ mem_top t) ht with h | h
  · exact step L R hL hR hcomm (hinter.trans hz) hgen (hBL (mem_map_of_mem Q.subtype h))
  · exact step R L hR hL (fun r hr l hl => (hcomm l hl r hr).symm)
      (by rw [inf_comm,hinter,hz]) (by rw [sup_comm,hgen]) (hCR (mem_map_of_mem Q.subtype h))

end Subgroup
