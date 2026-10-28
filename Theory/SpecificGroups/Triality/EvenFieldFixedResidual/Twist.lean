module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldDegree
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# The scalar involution and half-parameter triality twist

A nontrivial involution of the coefficient field GF(2^(3n)) forces n = 2m
with m positive. Its fixed field is isomorphic to GF(2^(3m)), and the
involution is exactly the 3m-th prime Frobenius. This includes m = 1.

Write D for the pinned triality cycle and F for prime Frobenius on the
split D4 group. The half-parameter map is T = D² F^m: because D³ = 1,
T² = D F^(2m) is the original defining twist and T³ = F^(3m) is the
coefficient involution. Hence their joint fixed points are precisely Fix(T).
The last equivalence retains the ambient elements, before the elementary
subgroup and its central quotient. Identifying those quotient fixed points
with the canonical smaller carrier additionally requires the inverse-diagram
comparison and descent through the elementary construction.

Sources: GLS3 2.5.12(d), 2.5.13(c), and 2.5.17,
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith, Notation 16.1.3 and
16.1.4(4), printed p.1171, `refs/quasithin.pdf`. The outer involutions
are field automorphisms in the GLS convention.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.EvenField
open OuterOdd

/-- Prime Frobenius iterates on the actual cubic coefficient field. -/
def coefficientFrobenius (n : ℕ) (hn : 0 < n) (k : ℕ) :
    CoefficientAut (binaryParameters n hn) :=
  iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 k

@[simp] theorem coefficientFrobenius_apply (n : ℕ) (hn : 0 < n) (k : ℕ)
    (x : ExtensionField (binaryParameters n hn)) :
    coefficientFrobenius n hn k x = x ^ (2 ^ k) := rfl

theorem coefficientFrobenius_add (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    coefficientFrobenius n hn (k+l) =
      coefficientFrobenius n hn k * coefficientFrobenius n hn l := by
  ext x
  exact iterateFrobeniusEquiv_add_apply (GaloisField 2 (3*n)) 2 k l x

theorem orderOf_primeFrobenius (n : ℕ) (hn : 0 < n) :
    orderOf (frobeniusEquiv (GaloisField 2 (3*n)) 2) = 3*n := by
  let F := GaloisField 2 (3*n)
  let f : (F ≃ₐ[ZMod 2] F) →* (F ≃+* F) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h => AlgEquiv.ext fun x =>
    DFunLike.congr_fun h x
  have he : f (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) =
      frobeniusEquiv F 2 := by
    ext x
    change x ^ Fintype.card (ZMod 2) = x ^ 2
    rw [ZMod.card]
  rw [← he, orderOf_injective f hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact GaloisField.finrank 2 (by omega)

/-- The scalar involution is the `3m`-th prime Frobenius, not the `m`-th. -/
theorem coefficientFrobenius_order_two (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    orderOf (coefficientFrobenius n hn (3*m)) = 2 := by
  change orderOf (iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 (3*m)) = 2
  rw [iterateFrobeniusEquiv_eq_pow, orderOf_pow_of_dvd (Nat.mul_ne_zero (by decide) hm.ne')]
  · rw [orderOf_primeFrobenius n hn, hnm]
    rw [show 3*(2*m) = 2*(3*m) by omega, Nat.mul_div_cancel _ (by omega)]
  · rw [orderOf_primeFrobenius n hn, hnm]
    exact ⟨2, by omega⟩

/-- A nontrivial involution of GF(2^(3n)) forces `n` even, and its fixed
field is genuinely isomorphic to the cubic field for the smaller parameter. -/
theorem coefficient_fixedField_model (n : ℕ) (hn : 0 < n)
    (e : CoefficientAut (binaryParameters n hn)) (he : e ^ 2 = 1) (hne : e ≠ 1) :
    ∃ (m : ℕ) (hm : 0 < m), n = 2*m ∧
      Nonempty (FixedBy.subfield (ExtensionField (binaryParameters n hn)) e ≃+*
        ExtensionField (binaryParameters m hm)) := by
  have hi : Function.Involutive e := fun x => DFunLike.congr_fun he x
  obtain ⟨k, hk, hnk, hF⟩ := Theory.PSL2.binary_fixedField_model
    (show 0 < 3*n by omega) e hi hne
  have hnEven : Even n := (Nat.even_mul.mp (show Even (3*n) from ⟨k, by omega⟩)).resolve_left
    (by decide)
  obtain ⟨m, hm⟩ := hnEven
  have hnm : n = 2*m := by omega
  have hmp : 0 < m := by omega
  have hk3 : k = 3*m := by omega
  subst k
  exact ⟨m, hmp, hnm, hF⟩

/-- Uniqueness identifies any coefficient involution with the explicit Frobenius. -/
theorem coefficient_involution_eq (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (e : CoefficientAut (binaryParameters n hn)) (he : e ^ 2 = 1) (hne : e ≠ 1) :
    e = coefficientFrobenius n hn (3*m) := by
  classical
  let F := ExtensionField (binaryParameters n hn)
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : Fintype (F ≃+* F) := Fintype.ofFinite _
  let s := coefficientFrobenius n hn (3*m)
  have hs : orderOf s = 2 := coefficientFrobenius_order_two n hn m hm hnm
  have hsne : s ≠ 1 := by intro h; simp [h] at hs
  have hssq : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  by_contra hes
  change e ≠ s at hes
  have hsub : ({1, e, s} : Finset (F ≃+* F)) ⊆
      {a ∈ (Finset.univ : Finset (F ≃+* F)) | a^2 = 1} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact he
    · exact hssq
  have hle := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) (by decide))
  simp [hes, Ne.symm hne, Ne.symm hsne] at hle


/-- Entrywise coefficient action on the split D4 group, as a homomorphism. -/
def splitCoefficientAction (P : Parameters) : CoefficientAut P →* MulAut (SplitGroup P) where
  toFun := coefficientSplit P
  map_one' := MulEquiv.ext (coefficientSplit_one P)
  map_mul' e f := MulEquiv.ext (coefficientSplit_mul P e f)

/-- The prime Frobenius iterates acting on the split group. -/
def splitFrobenius (n : ℕ) (hn : 0 < n) (k : ℕ) :
    MulAut (SplitGroup (binaryParameters n hn)) :=
  splitCoefficientAction _ (coefficientFrobenius n hn k)

theorem splitFrobenius_add (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    splitFrobenius n hn (k+l) = splitFrobenius n hn k * splitFrobenius n hn l :=
  (congrArg (splitCoefficientAction (binaryParameters n hn))
    (coefficientFrobenius_add n hn k l)).trans
      ((splitCoefficientAction (binaryParameters n hn)).map_mul _ _)

theorem splitFrobenius_mul (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    splitFrobenius n hn (k*l) = splitFrobenius n hn k ^ l := by
  have h : coefficientFrobenius n hn (k*l) = coefficientFrobenius n hn k ^ l := by
    change iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 (k*l) =
      iterateFrobeniusEquiv (GaloisField 2 (3*n)) 2 k ^ l
    simp only [iterateFrobeniusEquiv_eq_pow, pow_mul]
  exact (congrArg (splitCoefficientAction (binaryParameters n hn)) h).trans
    (map_pow (splitCoefficientAction (binaryParameters n hn)) _ _)

private theorem diagram_commute_splitFrobenius (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Commute (diagramAutomorphism (binaryParameters n hn)) (splitFrobenius n hn k) := by
  apply MulEquiv.ext
  intro x
  exact RootPairing.SimpleGeckGroup.diagramEquiv_equiv _ _ _ _ x

private theorem diagram_pow_three (P : Parameters) : diagramAutomorphism P ^ 3 = 1 := by
  apply MulEquiv.ext
  exact diagramAutomorphism_three P

/-- The half-parameter Steinberg map has the inverse diagram cycle.
Its square is the original twist and its cube is the coefficient involution. -/
def inverseGraphHalf (n : ℕ) (hn : 0 < n) (m : ℕ) :
    MulAut (SplitGroup (binaryParameters n hn)) :=
  diagramAutomorphism (binaryParameters n hn) ^ 2 * splitFrobenius n hn m

private theorem twist_square {A : Type*} [Group A] (d f : A) (hc : Commute d f)
    (hd : d^3 = 1) : (d^2*f)^2 = d*f^2 := by
  rw [(hc.pow_left 2).mul_pow, ← pow_mul, show 2*2 = 3+1 from rfl, pow_succ, hd,
    one_mul]

private theorem twist_cube {A : Type*} [Group A] (d f : A) (hc : Commute d f)
    (hd : d^3 = 1) : (d^2*f)^3 = f^3 := by
  rw [(hc.pow_left 2).mul_pow, ← pow_mul, show 2*3 = 3*2 from rfl, pow_mul,
    hd, one_pow, one_mul]

theorem inverseGraphHalf_square (n : ℕ) (hn : 0 < n) (m : ℕ) (hnm : n = 2*m) :
    inverseGraphHalf n hn m ^ 2 = graphFieldAutomorphism (binaryParameters n hn) := by
  let d := diagramAutomorphism (binaryParameters n hn)
  have ht := twist_square d (splitFrobenius n hn m)
    (diagram_commute_splitFrobenius n hn m) (diagram_pow_three _)
  have hf : splitFrobenius n hn m ^ 2 = splitFrobenius n hn n :=
    (splitFrobenius_mul n hn m 2).symm.trans
      (congrArg (splitFrobenius n hn) (by omega : m*2=n))
  have hg : d * splitFrobenius n hn n = graphFieldAutomorphism (binaryParameters n hn) := by
    apply MulEquiv.ext
    exact diagram_field_commute _
  exact ht.trans ((congrArg (fun a => d*a) hf).trans hg)

theorem inverseGraphHalf_cube (n : ℕ) (hn : 0 < n) (m : ℕ) :
    inverseGraphHalf n hn m ^ 3 = splitFrobenius n hn (3*m) :=
  (twist_cube _ _ (diagram_commute_splitFrobenius n hn m) (diagram_pow_three _)).trans
    ((splitFrobenius_mul n hn m 3).symm.trans
      (congrArg (splitFrobenius n hn) (Nat.mul_comm m 3)))

private theorem fixed_iff_square_cube {G : Type*} [Group G] (t : MulAut G) (x : G) :
    t x = x ↔ (t^2) x = x ∧ (t^3) x = x := by
  change t x = x ↔ t (t x) = x ∧ t (t (t x)) = x
  constructor
  · intro h
    simp only [h, and_self]
  · rintro ⟨h2,h3⟩
    rwa [h2] at h3

private theorem fixed_iff_of_square_cube {G : Type*} [Group G] (t s c : MulAut G)
    (hs : t^2 = s) (hc : t^3 = c) (x : G) :
    t x = x ↔ s x = x ∧ c x = x := by
  subst s
  subst c
  exact fixed_iff_square_cube t x

/-- Joint fixed points of the defining twist and the coefficient involution
are exactly the fixed points of the inverse-diagram half-parameter twist. -/
theorem inverseGraphHalf_fixed_iff (n : ℕ) (hn : 0 < n) (m : ℕ) (hnm : n = 2*m)
    (x : SplitGroup (binaryParameters n hn)) :
    inverseGraphHalf n hn m x = x ↔
      graphFieldAutomorphism (binaryParameters n hn) x = x ∧
        splitFrobenius n hn (3*m) x = x :=
  fixed_iff_of_square_cube _ _ _ (inverseGraphHalf_square n hn m hnm)
    (inverseGraphHalf_cube n hn m) x

/-- The inverse diagram occurring in the half-parameter twist. -/
theorem diagram_square_eq_inverse (P : Parameters) :
    diagramAutomorphism P ^ 2 = (diagramAutomorphism P)⁻¹ := by
  have hd := diagram_pow_three P
  exact eq_inv_iff_mul_eq_one.mpr hd

/-- Before taking the elementary subgroup and central quotient, the coefficient
fixed points are exactly the inverse-diagram half-parameter fixed group. -/
def coefficientFixedEquivInverseGraph (n : ℕ) (hn : 0 < n) (m : ℕ) (hnm : n = 2*m) :
    MulAut.fixedSubgroup (coefficientFixed (binaryParameters n hn) (coefficientFrobenius n hn (3*m))) ≃*
      (inverseGraphHalf n hn m).fixedSubgroup where
  toFun x := ⟨x.val.val, (MulAut.mem_fixedSubgroup _ _).mpr
    ((inverseGraphHalf_fixed_iff n hn m hnm x.val.val).mpr
      ⟨x.val.property, congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)⟩)⟩
  invFun x := ⟨⟨x.val, ((inverseGraphHalf_fixed_iff n hn m hnm x.val).mp
      ((MulAut.mem_fixedSubgroup _ _).mp x.property)).1⟩,
    (MulAut.mem_fixedSubgroup _ _).mpr
      (Subtype.ext (((inverseGraphHalf_fixed_iff n hn m hnm x.val).mp
        ((MulAut.mem_fixedSubgroup _ _).mp x.property)).2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Triality.Standard.EvenField

