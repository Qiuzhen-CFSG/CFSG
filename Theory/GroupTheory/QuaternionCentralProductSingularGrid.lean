module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.PGroup.ExtraspecialInvolutionCosetAction

/-!
# Singular grid of an intrinsic quaternion central product

The two actual quaternion factors have central quotient images of order four.
Multiplication identifies their product with the whole central quotient, and
restricts to an equivalence from pairs of nonidentity factor points to the
nonzero singular cosets. The restriction uses the quaternion square criterion
and the common central involution, rather than an abstract nine-point census.

The factor point actions are restrictions of actual quotient automorphisms.
The multiplication equivalence intertwines them with the canonical action on
central involution cosets. An additional coprime observation lifts a fixed
central coset of a cubic automorphism to a fixed element.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3, especially 2.3(2)(b).
-/

namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

public abbrev factorQuotient (R : Subgroup Q) : Subgroup (Q ⧸ center Q) :=
  R.map (QuotientGroup.mk' (center Q))
public abbrev FactorPoints (R : Subgroup Q) := {v : factorQuotient R // v ≠ 1}

omit [Finite Q] in
public theorem factor_model (R : Subgroup Q) (hR : R = d.left ∨ R = d.right) :
    Nonempty (R ≃* QuaternionGroup 2) := by
  rcases hR with rfl | rfl
  · exact d.left_model
  · exact d.right_model

public theorem center_le_factor (R : Subgroup Q) (hR : R = d.left ∨ R = d.right) :
    center Q ≤ R := by
  rw [d.center_eq]
  rcases hR with rfl | rfl
  · exact inf_le_left
  · exact inf_le_right

public theorem factor_center_image (R : Subgroup Q) (hR : R = d.left ∨ R = d.right) :
    (center R).map R.subtype = center Q := by
  rw [d.center_eq]
  rcases hR with rfl | rfl
  · exact (intersection_eq_factor_center d.left d.right d.left_model
      d.intersection_card d.commute).symm
  · rw [inf_comm]
    exact (intersection_eq_factor_center d.right d.left d.right_model
      (by simpa only [inf_comm] using d.intersection_card)
      (fun c hc b hb => (d.commute b hb c hc).symm)).symm

public theorem factorQuotient_card (R : Subgroup Q) (hR : R = d.left ∨ R = d.right) :
    Nat.card (factorQuotient R) = 4 := by
  let f := (QuotientGroup.mk' (center Q)).comp R.subtype
  have hk : f.ker = (center Q).subgroupOf R := by
    ext x
    exact QuotientGroup.eq_one_iff (x : Q)
  have hr : f.range = factorQuotient R := by
    rw [MonoidHom.range_comp, range_subtype]
  have hc := f.ker.card_mul_index
  rw [index_ker, hr, hk,
    Nat.card_congr (subgroupOfEquivOfLe (d.center_le_factor R hR)).toEquiv,
    d.center_card, Nat.card_congr (d.factor_model R hR).some.toEquiv,
    show Nat.card (QuaternionGroup 2) = 8 by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]] at hc
  omega

public theorem factorPoints_card (R : Subgroup Q) (hR : R = d.left ∨ R = d.right) :
    Nat.card (FactorPoints R) = 3 := by
  classical
  let := Fintype.ofFinite (factorQuotient R)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, d.factorQuotient_card R hR]

public noncomputable def factorPointsEquivFin (R : Subgroup Q)
    (hR : R = d.left ∨ R = d.right) : FactorPoints R ≃ Fin 3 :=
  Finite.equivFinOfCardEq (d.factorPoints_card R hR)

public theorem factor_square_eq_one_iff (R : Subgroup Q) (hR : R = d.left ∨ R = d.right)
    (x : Q) (hx : x ∈ R) : x ^ 2 = 1 ↔ x ∈ center Q := by
  constructor
  · intro hx2
    have hq : ∀ x y : QuaternionGroup 2, x ^ 2 = 1 → y * x = x * y := by decide
    let e := (d.factor_model R hR).some
    have hz : (⟨x, hx⟩ : R) ∈ center R := by
      apply mem_center_iff.mpr
      intro y
      apply e.injective
      simp only [map_mul]
      apply hq
      simpa only [map_pow, map_one] using congrArg e (show (⟨x, hx⟩ : R) ^ 2 = 1 from Subtype.ext hx2)
    rw [← d.factor_center_image R hR]
    exact mem_map_of_mem R.subtype hz
  · intro hxZ
    exact congrArg Subtype.val (d.center_square ⟨x, hxZ⟩)

public theorem quotientProduct_bijective : Function.Bijective
    (fun p : factorQuotient d.left × factorQuotient d.right =>
      (p.1 : Q ⧸ center Q) * p.2) := by
  have hs : Function.Surjective
      (fun p : factorQuotient d.left × factorQuotient d.right =>
        (p.1 : Q ⧸ center Q) * p.2) := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
    have hn : d.left ≤ normalizer (d.right : Set Q) := by
      apply le_trans ?_ (centralizer_le_normalizer _)
      exact fun b hb c hc => (d.commute b hb c hc).symm
    have hx : x ∈ (↑(d.left ⊔ d.right) : Set Q) := d.span ▸ mem_top x
    rw [coe_mul_of_left_le_normalizer_right d.left d.right hn] at hx
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    exact ⟨(⟨_, mem_map_of_mem _ hb⟩, ⟨_, mem_map_of_mem _ hc⟩), (map_mul _ _ _).symm⟩
  apply hs.bijective_of_nat_card_le
  rw [Nat.card_prod, d.factorQuotient_card _ (Or.inl rfl),
    d.factorQuotient_card _ (Or.inr rfl), d.quotient_card]

public noncomputable def quotientProduct :
    factorQuotient d.left × factorQuotient d.right ≃ Q ⧸ center Q :=
  Equiv.ofBijective _ d.quotientProduct_bijective

@[simp] public theorem quotientProduct_apply (p : factorQuotient d.left × factorQuotient d.right) :
    d.quotientProduct p = (p.1 : Q ⧸ center Q) * p.2 := by rfl


public theorem singular_not_mem_factor (R : Subgroup Q) (hR : R = d.left ∨ R = d.right)
    (v : CentralInvolutionCosets Q) : v.val ∉ factorQuotient R := by
  rintro ⟨r, hr, he⟩
  obtain ⟨x, hx, hex⟩ := v.property.2
  have hr2 : r ^ 2 = 1 := (d.square_eq_of_quotient_eq r x (he.trans hex.symm)).trans hx
  have hrZ := (d.factor_square_eq_one_iff R hR r hr).mp hr2
  exact v.property.1 (he.symm.trans ((QuotientGroup.eq_one_iff r).mpr hrZ))

public theorem mixed_square (b c : Q) (hb : b ∈ d.left) (hc : c ∈ d.right)
    (hbZ : b ∉ center Q) (hcZ : c ∉ center Q) : (b * c) ^ 2 = 1 := by
  have hb2 : b ^ 2 ≠ 1 := fun h => hbZ ((d.factor_square_eq_one_iff _ (Or.inl rfl) b hb).mp h)
  have hc2 : c ^ 2 ≠ 1 := fun h => hcZ ((d.factor_square_eq_one_iff _ (Or.inr rfl) c hc).mp h)
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
  have hs : b ^ 2 = c ^ 2 := congrArg Subtype.val
    ((hz ⟨_, d.square_mem_center b⟩ (fun h => hb2 (congrArg Subtype.val h))).trans
      (hz ⟨_, d.square_mem_center c⟩ (fun h => hc2 (congrArg Subtype.val h))).symm)
  rw [(show Commute b c from d.commute b hb c hc).mul_pow, hs, ← pow_two]
  exact congrArg Subtype.val (d.center_square ⟨_, d.square_mem_center c⟩)

private noncomputable def singularProductMap (p : FactorPoints d.left × FactorPoints d.right) :
    CentralInvolutionCosets Q := by
  refine ⟨d.quotientProduct (p.1.val, p.2.val), ?_, ?_⟩
  · intro he
    have hp : (p.1.val, p.2.val) = (1, 1) := d.quotientProduct.injective (by simpa using he)
    exact p.1.property (congrArg Prod.fst hp)
  · obtain ⟨b, hb, heB⟩ := p.1.val.property
    obtain ⟨c, hc, heC⟩ := p.2.val.property
    have hbZ : b ∉ center Q := by
      intro hbZ
      apply p.1.property
      exact Subtype.ext (heB.symm.trans ((QuotientGroup.eq_one_iff b).mpr hbZ))
    have hcZ : c ∉ center Q := by
      intro hcZ
      apply p.2.property
      exact Subtype.ext (heC.symm.trans ((QuotientGroup.eq_one_iff c).mpr hcZ))
    exact ⟨b * c, d.mixed_square b c hb hc hbZ hcZ, by
      rw [map_mul, heB, heC, quotientProduct_apply]⟩

@[simp] private theorem singularProductMap_val (p : FactorPoints d.left × FactorPoints d.right) :
    (d.singularProductMap p).val = (p.1.val : Q ⧸ center Q) * p.2.val := by rfl

private theorem singularProductMap_bijective : Function.Bijective d.singularProductMap := by
  constructor
  · intro p q hpq
    have hh : (p.1.val, p.2.val) = (q.1.val, q.2.val) :=
      d.quotientProduct.injective (congrArg Subtype.val hpq)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  · intro v
    obtain ⟨p, hp⟩ := d.quotientProduct.surjective v.val
    have hleft : p.1 ≠ 1 := by
      intro he
      apply d.singular_not_mem_factor d.right (Or.inr rfl) v
      rw [← hp, quotientProduct_apply, he, coe_one, one_mul]
      exact p.2.property
    have hright : p.2 ≠ 1 := by
      intro he
      apply d.singular_not_mem_factor d.left (Or.inl rfl) v
      rw [← hp, quotientProduct_apply, he, coe_one, mul_one]
      exact p.1.property
    exact ⟨(⟨p.1, hleft⟩, ⟨p.2, hright⟩), Subtype.ext hp⟩

public noncomputable def singularProduct :
    FactorPoints d.left × FactorPoints d.right ≃ CentralInvolutionCosets Q :=
  Equiv.ofBijective _ d.singularProductMap_bijective

@[simp] public theorem singularProduct_val (p : FactorPoints d.left × FactorPoints d.right) :
    (d.singularProduct p).val = (p.1.val : Q ⧸ center Q) * p.2.val := by rfl


omit [Finite Q] in
private def nonidentityPerm : MulAut Q →* Equiv.Perm {x : Q // x ≠ 1} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (fun _ => a.map_ne_one_iff)
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

omit [Finite Q] in
public def factorPointAction {A : Type*} [Group A] (R : Subgroup Q)
    (f : A →* MulAut (Q ⧸ center Q))
    (hf : ∀ a, (factorQuotient R).map (f a).toMonoidHom = factorQuotient R) :
    A →* Equiv.Perm (FactorPoints R) :=
  nonidentityPerm.comp
    { toFun a := ((f a).subgroupMap (factorQuotient R)).trans (MulEquiv.subgroupCongr (hf a))
      map_one' := by ext x; exact DFunLike.congr_fun f.map_one (x : Q ⧸ center Q)
      map_mul' a b := by ext x; exact DFunLike.congr_fun (f.map_mul a b) (x : Q ⧸ center Q) }

omit [Finite Q] in
@[simp] public theorem factorPointAction_val {A : Type*} [Group A] (R : Subgroup Q)
    (f : A →* MulAut (Q ⧸ center Q))
    (hf : ∀ a, (factorQuotient R).map (f a).toMonoidHom = factorQuotient R)
    (a : A) (p : FactorPoints R) :
    ((factorPointAction R f hf a p).val : Q ⧸ center Q) = f a p.val := by rfl

public theorem singularProduct_natural (a : MulAut Q)
    (p q : FactorPoints d.left × FactorPoints d.right)
    (hl : (q.1.val : Q ⧸ center Q) = quotientAut (center Q) a p.1.val)
    (hr : (q.2.val : Q ⧸ center Q) = quotientAut (center Q) a p.2.val) :
    d.singularProduct q = centralInvolutionCosetAction a (d.singularProduct p) := by
  apply Subtype.ext
  rw [singularProduct_val, centralInvolutionCosetAction_val, singularProduct_val,
    map_mul, hl, hr]


include d in
public theorem cubic_fixed_of_quotient_fixed (a : MulAut Q) (ha : a ^ 3 = 1)
    (x : Q) (hx : quotientAut (center Q) a (QuotientGroup.mk' (center Q) x) =
      QuotientGroup.mk' (center Q) x) : a x = x := by
  let c := x⁻¹ * a x
  rw [quotientAut_apply_mk] at hx
  have hc : c ∈ center Q := QuotientGroup.eq.mp hx.symm
  have hfix : a c = c := d.fixes_center a ⟨c, hc⟩
  have hc2 : c ^ 2 = 1 := congrArg Subtype.val (d.center_square ⟨c, hc⟩)
  have hax : a x = x * c := by simp [c]
  have h3 : a (a (a x)) = x := by
    simpa [pow_succ] using DFunLike.congr_fun ha x
  calc
    a x = x * c := hax
    _ = x * (c ^ 2 * c) := by rw [hc2, one_mul]
    _ = a (a (a x)) := by simp only [hax, map_mul, hfix, pow_two, mul_assoc]
    _ = x := h3

end Subgroup.QuaternionCentralProductData
