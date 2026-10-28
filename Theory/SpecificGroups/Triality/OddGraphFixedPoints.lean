module

public import Theory.SpecificGroups.Triality.ElementaryNine
import all Theory.SpecificGroups.Triality.ElementaryNine
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients

/-!
# A genuine triality graph automorphism and its fixed elementary nine

The q-Frobenius on the cubic coefficient field restricts to the elementary
fixed points and descends through their center to `Standard.Carrier`. On the
fixed matrices it is inverse to the pinned D₄ diagram cycle. For every positive
binary exponent its action and its actual outer image have order three. The
proved separation of coefficient and inner actions supplies outerness, including
q = 2, without an assumed automorphism classification.

The four signed central and folded-arm root elements at parameter one are fixed
by every coefficient automorphism. Thus the two explicit independent cubic
words in `ElementaryNine` give a pointwise fixed elementary subgroup of order
nine. This continues the internal word calculation of `ElementaryNine`: the
private `import all` supplies its unexposed definition bodies to these proofs,
without exposing them or changing that module. All exported statements use
public names. We transport that actual subgroup through compatible model isomorphisms,
automorphism conjugacies, and the inclusion of a normal subgroup in its ambient
group.

GLS graph automorphisms need not all have the same fixed group. The final
overgroup selection uses a supplied inner-times-coefficient expression: cancel
the inner factor, then choose an order-three element of the cyclic coefficient
subgroup. All coefficient representatives fix the constructed nine. The
extension `OddGraphFixedPoints.Overgroups` discharges the expression using the
existing coverage theorem under the source's simplicity and perfectness inputs.

Sources: Aschbacher–Smith, Notation A.2.5 and Corollary A.2.6, printed pp.33–34
(`refs/quasithin.pdf`); GLS98 2.5.12 and Definition 2.5.13(c)(2), and the root
parametrizations of §2.4 (`refs/KGroup/GLS3/chapter2.tex`). Only the genuine
`StandardModel` carrier is used.
-/

public section

noncomputable section
namespace Triality.Standard.OddGraph
open OuterOdd ElementaryCentralKernel Parabolics

/-- The q-Frobenius on the genuine carrier, inverse to the pinned diagram cycle. -/
@[expose] def automorphism (P : Parameters) : MulAut (Carrier P) :=
  coefficientAction P (fieldFrobenius P)

/-- The coefficient action agrees with the inverse diagram action on fixed matrices. -/
theorem diagram_coefficientElementary (P : Parameters) (g : ElementaryGroup P) :
    diagramAutomorphism P
      (elementaryInclusion P (coefficientElementary P (fieldFrobenius P) g)) =
        elementaryInclusion P g := by
  change diagramAutomorphism P (fieldAutomorphism P (elementaryInclusion P g)) = _
  exact (diagram_field_commute P (elementaryInclusion P g)).trans g.val.property

theorem automorphism_cube (P : Parameters) : automorphism P ^ 3 = 1 := by
  rw [automorphism, ← map_pow, fieldFrobenius_pow_three, map_one]

private theorem fieldFrobenius_ne_one (P : Parameters) : fieldFrobenius P ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_frobenius_moved P
  intro h
  exact ht (DFunLike.congr_fun h t)

/-- This order-three action is outer even for the smallest field. -/
theorem automorphism_not_inner (n : ℕ) (hn : 0 < n) :
    automorphism (binaryParameters n hn) ∉ MulAut.innerSubgroup (BinaryCarrier n hn) := by
  intro h
  exact fieldFrobenius_ne_one _
    ((EvenField.NormalForm.coefficientAction_mem_inner_iff n hn _).mp h)

theorem automorphism_order (n : ℕ) (hn : 0 < n) :
    orderOf (automorphism (binaryParameters n hn)) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime (automorphism_cube _)
  intro h
  exact automorphism_not_inner n hn (h ▸ (MulAut.innerSubgroup _).one_mem)


/-- The image in the actual outer automorphism group has order three, as required
by GLS98 Definition 2.5.13(c)(2) for the triality graph convention. -/
theorem automorphism_outer_order (n : ℕ) (hn : 0 < n) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
      (automorphism (binaryParameters n hn))) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow, automorphism_cube, map_one]
  · intro h
    exact automorphism_not_inner n hn ((QuotientGroup.eq_one_iff _).mp h)

private theorem coefficient_seed (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (k : Fin 4) :
    coefficientElementary P e (ElementaryNine.seed P hp k) = ElementaryNine.seed P hp k := by
  have hc (s : Bool) : coefficientElementary P e (centralElementary P s 1 (map_one _)) =
      centralElementary P s 1 (map_one _) := by
    apply Subtype.ext
    apply Subtype.ext
    change coefficientSplit P e (simpleRoot P s 1 1) = simpleRoot P s 1 1
    cases s <;> simp only [simpleRoot, Bool.false_eq_true, ↓reduceIte, positiveRoot,
      negativeRoot, coefficientSplit_positive, coefficientSplit_negative, map_one]
  have ha (s : Bool) : coefficientElementary P e (foldedElementary P hp s 1) =
      foldedElementary P hp s 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change coefficientSplit P e (foldedRoot P s 1) = foldedRoot P s 1
    cases s <;> simp only [foldedRoot, simpleRoot, Bool.false_eq_true, ↓reduceIte, positiveRoot,
      negativeRoot, map_mul, coefficientSplit_positive, coefficientSplit_negative, map_one]
  fin_cases k
  · exact hc true
  · exact hc false
  · exact ha true
  · exact ha false

private theorem coefficient_first (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    coefficientElementary P e (ElementaryNine.first P hp) = ElementaryNine.first P hp := by
  simp only [ElementaryNine.first, ElementaryNine.Binary.firstWord, map_mul, coefficient_seed]

private theorem coefficient_second (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    coefficientElementary P e (ElementaryNine.second P hp) = ElementaryNine.second P hp := by
  simp only [ElementaryNine.second, ElementaryNine.Binary.secondWord, map_mul, coefficient_seed]

/-- Every coefficient automorphism fixes the actual nine-element embedding. -/
theorem coefficient_embedding (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (v : ElementaryNine.Coordinates) :
    coefficientAction P e (ElementaryNine.embedding P hp v) =
      ElementaryNine.embedding P hp v := by
  change toCarrier P (coefficientElementary P e (ElementaryNine.elementaryEmbedding P hp v)) =
    toCarrier P (ElementaryNine.elementaryEmbedding P hp v)
  apply congrArg (toCarrier P)
  simp only [ElementaryNine.elementaryEmbedding_apply P hp v, map_mul, map_pow,
    coefficient_first P hp e, coefficient_second P hp e]

/-- The fixed subgroup witness retains the explicit root-word range. -/
theorem subgroup_le_coefficient_fixed (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    ElementaryNine.subgroup P hp ≤ (coefficientAction P e).fixedSubgroup := by
  rintro _ ⟨v, rfl⟩
  exact (MulAut.mem_fixedSubgroup _ _).mpr (coefficient_embedding P hp e v)

/-- The genuine cubic graph automorphism fixes an elementary abelian group of order nine. -/
theorem exists_fixed_nine (n : ℕ) (hn : 0 < n) :
    ∃ E : Subgroup (BinaryCarrier n hn), IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ (automorphism (binaryParameters n hn)).fixedSubgroup :=
  ⟨ElementaryNine.subgroup (binaryParameters n hn) rfl,
    ElementaryNine.subgroup_elementary _ _, ElementaryNine.card_subgroup _ _,
    subgroup_le_coefficient_fixed _ _ _⟩

/-- Intertwining transports the literal subgroup and its pointwise fixation. -/
theorem exists_fixed_nine_of_compatible {H : Type*} [Group H]
    (P : Parameters) (hp : P.prime = 2) (c : CoefficientAut P)
    (e : Carrier P ≃* H) (a : MulAut H)
    (he : ∀ x, e (coefficientAction P c x) = a (e x)) :
    ∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧ E ≤ a.fixedSubgroup := by
  let E := ElementaryNine.subgroup P hp
  let d := E.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨E.map e.toMonoidHom, ?_, ?_, ?_⟩
  · exact IsElementaryAbelian.of_surjective d.toMonoidHom d.surjective
  · exact (Nat.card_congr d.toEquiv).symm.trans (ElementaryNine.card_subgroup P hp)
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    change a (e x) = e x
    rw [← he, show coefficientAction P c x = x from
      (MulAut.mem_fixedSubgroup _ _).mp (subgroup_le_coefficient_fixed P hp c hx)]

/-- Actual group isomorphisms transport coefficient graph representatives. -/
theorem exists_fixed_nine_congr {H : Type*} [Group H]
    (P : Parameters) (hp : P.prime = 2) (c : CoefficientAut P) (e : Carrier P ≃* H) :
    ∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ (MulAut.congr e (coefficientAction P c)).fixedSubgroup := by
  apply exists_fixed_nine_of_compatible P hp c e
  intro x
  change e (coefficientAction P c x) = e (coefficientAction P c (e.symm (e x)))
  rw [e.symm_apply_apply]

/-- Automorphism conjugacy is a special case of compatible transport. -/
theorem exists_fixed_nine_conjugate (P : Parameters) (hp : P.prime = 2)
    (c : CoefficientAut P) (b : MulAut (Carrier P)) :
    ∃ E : Subgroup (Carrier P), IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ (b * coefficientAction P c * b⁻¹).fixedSubgroup := by
  apply exists_fixed_nine_of_compatible P hp c b
  intro x
  change b (coefficientAction P c x) = b (coefficientAction P c (b.symm (b x)))
  rw [b.symm_apply_apply]

/-- A compatible coefficient action in an ambient group fixes a literal subgroup of L. -/
theorem exists_fixed_nine_in_ambient {G : Type*} [Group G]
    (L : Subgroup G) [L.Normal] (P : Parameters) (hp : P.prime = 2)
    (c : CoefficientAut P) (e : Carrier P ≃* L) (x : G)
    (he : ∀ z, e (coefficientAction P c z) = MulAut.conjNormal x (e z)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ L ∧ E ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_nine_of_compatible P hp c e _ he
  let := hE
  let d := E.equivMapOfInjective L.subtype L.subtype_injective
  refine ⟨E.map L.subtype, IsElementaryAbelian.of_surjective d.toMonoidHom d.surjective,
    (Nat.card_congr d.toEquiv).symm.trans hcard, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : x * (y : G) * x⁻¹ = y := congrArg Subtype.val
      ((MulAut.mem_fixedSubgroup _ _).mp (hfix hy))
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- The source overgroup can select a pure coefficient representative, without
claiming that arbitrary graph classes have the same fixed group. -/
theorem exists_order_three_coefficient_in_overgroup
    (n : ℕ) (hn : 0 < n) (U : Subgroup (MulAut (BinaryCarrier n hn)))
    (hU : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ U)
    (a : MulAut (BinaryCarrier n hn)) (ha : a ∈ U)
    (g : BinaryCarrier n hn) (c : CoefficientAut (binaryParameters n hn))
    (hform : a = MulAut.conj g * coefficientAction (binaryParameters n hn) c)
    (hthree : 3 ∣ orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn)) a)) :
    ∃ d : CoefficientAut (binaryParameters n hn),
      coefficientAction (binaryParameters n hn) d ∈ U ∧
      orderOf (coefficientAction (binaryParameters n hn) d) = 3 ∧
      coefficientAction (binaryParameters n hn) d ∉ MulAut.innerSubgroup (BinaryCarrier n hn) ∧
      ElementaryNine.subgroup (binaryParameters n hn) rfl ≤
        (coefficientAction (binaryParameters n hn) d).fixedSubgroup := by
  let P := binaryParameters n hn
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
  have hconj : MulAut.conj g ∈ U := hU ⟨g, rfl⟩
  have hcU : coefficientAction P c ∈ U := by
    have h := U.mul_mem (U.inv_mem hconj) ha
    rw [hform, inv_mul_cancel_left] at h
    exact h
  have hqa : q a = q (coefficientAction P c) := by
    rw [hform, map_mul, show q (MulAut.conj g) = 1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩, one_mul]
  have hthreec : 3 ∣ orderOf c := by
    change 3 ∣ orderOf (q a) at hthree
    rw [hqa] at hthree
    exact hthree.trans ((orderOf_map_dvd q _).trans (orderOf_map_dvd (coefficientAction P) c))
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Finite (CoefficientAut P) := Finite.of_injective
    (fun f : CoefficientAut P => (f : ExtensionField P → ExtensionField P))
    DFunLike.coe_injective
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers c) 3
    (by simpa only [Nat.card_zpowers] using hthreec)
  have hdorder : orderOf (d : CoefficientAut P) = 3 := (Subgroup.orderOf_coe d).trans hd
  have hdne : (d : CoefficientAut P) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdorder
    contradiction
  have hdouter : coefficientAction P d ∉ MulAut.innerSubgroup (Carrier P) :=
    fun h => hdne ((EvenField.NormalForm.coefficientAction_mem_inner_iff n hn d).mp h)
  have hdU : coefficientAction P d ∈ U :=
    (Subgroup.zpowers_le.mpr hcU : Subgroup.zpowers c ≤ U.comap (coefficientAction P)) d.property
  refine ⟨d, hdU, ?_, hdouter, subgroup_le_coefficient_fixed P rfl d⟩
  apply orderOf_eq_prime
  · rw [← map_pow, (orderOf_eq_prime_iff.mp hdorder).1, map_one]
  · intro h
    exact hdouter (h ▸ (MulAut.innerSubgroup _).one_mem)

/-- A nonidentity coefficient action comes from outside the original normal subgroup. -/
theorem not_mem_of_compatible_coefficient {G : Type*} [Group G]
    (L : Subgroup G) [L.Normal] (n : ℕ) (hn : 0 < n)
    (c : CoefficientAut (binaryParameters n hn)) (hc : c ≠ 1)
    (e : BinaryCarrier n hn ≃* L) (x : G)
    (he : ∀ z, e (coefficientAction (binaryParameters n hn) c z) =
      MulAut.conjNormal x (e z)) : x ∉ L := by
  intro hx
  have hcongr : MulAut.congr e (coefficientAction (binaryParameters n hn) c) =
      MulAut.conjNormal x := by
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    change e (coefficientAction (binaryParameters n hn) c (e.symm (e z))) = _
    rw [e.symm_apply_apply]
    exact he z
  obtain ⟨z, hz⟩ := (MulAut.congr_inner_iff e _).mp
    ⟨⟨x, hx⟩, hcongr.trans (MulAut.conjNormal_val (h := ⟨x, hx⟩))⟩
  exact hc (EvenField.NormalForm.coefficient_eq_one_of_inner n hn c z hz)

/-- Specialization to the explicit cubic graph action. -/
theorem not_mem_of_compatible_graph {G : Type*} [Group G]
    (L : Subgroup G) [L.Normal] (n : ℕ) (hn : 0 < n)
    (e : BinaryCarrier n hn ≃* L) (x : G)
    (he : ∀ z, e (automorphism (binaryParameters n hn) z) =
      MulAut.conjNormal x (e z)) : x ∉ L :=
  not_mem_of_compatible_coefficient L n hn _ (fieldFrobenius_ne_one _) e x he

/-- Order is unchanged by the actual model isomorphism. -/
theorem automorphism_order_congr {H : Type*} [Group H]
    (n : ℕ) (hn : 0 < n) (e : BinaryCarrier n hn ≃* H) :
    orderOf (MulAut.congr e (automorphism (binaryParameters n hn))) = 3 :=
  (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).trans
    (automorphism_order n hn)

/-- Outerness is unchanged by the same model isomorphism. -/
theorem automorphism_not_inner_congr {H : Type*} [Group H]
    (n : ℕ) (hn : 0 < n) (e : BinaryCarrier n hn ≃* H) :
    MulAut.congr e (automorphism (binaryParameters n hn)) ∉ MulAut.innerSubgroup H := by
  rintro ⟨h, hh⟩
  obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff e _).mp ⟨h, hh.symm⟩
  exact automorphism_not_inner n hn ⟨g, hg.symm⟩

end Triality.Standard.OddGraph
