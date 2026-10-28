module

public import Theory.GroupTheory.PGroup.SmallFrattiniForms
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Binary bilinear and quadratic forms from a small Frattini subgroup

The group-valued commutator and square maps are marked in the binary line
and packaged as actual `ZMod 2` bilinear and quadratic forms. The radical on
the Frattini quotient is the center image. On the central quotient the
commutator form is alternating and nondegenerate; when the center has
trivial Frattini subgroup, the square form descends with this same polar.
Automorphisms preserve all forms and the literal quotient projection.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 12.8.8(2), printed pp.851–852.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace SmallFrattini

/-- A biadditive map of elementary binary groups is a binary bilinear form.
Its reduction rule retains the original marked values. -/
def bilinearOfMultiplicative {E : Type*} [Group E]
    [IsElementaryAbelian 2 E] (b : E → E → Multiplicative (ZMod 2))
    (hl : ∀ x y z, b (x*y) z = b x z * b y z)
    (hr : ∀ x y z, b x (y*z) = b x y * b x z) :
    LinearMap.BilinForm (ZMod 2) (Additive E) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := fun x => AddMonoidHom.toZModLinearMap 2 {
      toFun := fun y => (b x.toMul y.toMul).toAdd
      map_zero' := by
        have h := hr x.toMul 1 1
        have hb : b x.toMul 1 = 1 := by simpa using h.symm
        exact congrArg Multiplicative.toAdd hb
      map_add' := fun y z => congrArg Multiplicative.toAdd (hr x.toMul y.toMul z.toMul) }
    map_zero' := by
      ext y
      have h := hl 1 1 y.toMul
      have hb : b 1 y.toMul = 1 := by simpa using h.symm
      exact congrArg Multiplicative.toAdd hb
    map_add' := by
      intro x z
      ext y
      exact congrArg Multiplicative.toAdd (hl x.toMul z.toMul y.toMul) }

variable {Q : Type*} [Group Q] [Finite Q]

theorem quotientElementary (htwo : IsPGroup 2 Q) :
    IsElementaryAbelian 2 (Q ⧸ frattini Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  exact isElementaryAbelian_quotient_frattini

theorem centralElementary (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) : IsElementaryAbelian 2 (Q ⧸ center Q) :=
  elementary_quotient_of_frattini_le htwo _ (central_of_normal_card_two _ hphi)

noncomputable def binaryMark (hphi : Nat.card (frattini Q) = 2) :
    frattini Q ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq hphi (by simp)

noncomputable def quotientBilinearForm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    letI : Fact (IsPGroup 2 Q) := ⟨htwo⟩
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
      isElementaryAbelian_quotient_frattini
    LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ frattini Q)) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini
  exact bilinearOfMultiplicative (fun x y => binaryMark hphi (quotientPolar htwo hphi x y))
    (by intro x y z; rw [quotientPolar_mul_left, map_mul])
    (by intro x y z; rw [quotientPolar_mul_right, map_mul])

theorem quotientBilinearForm_apply (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ frattini Q) :
    quotientBilinearForm htwo hphi (Additive.ofMul x) (Additive.ofMul y) =
      (binaryMark hphi (quotientPolar htwo hphi x y)).toAdd := rfl

noncomputable def quotientQuadraticForm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    letI : Fact (IsPGroup 2 Q) := ⟨htwo⟩
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
      isElementaryAbelian_quotient_frattini
    QuadraticForm (ZMod 2) (Additive (Q ⧸ frattini Q)) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini
  refine {
    toFun := fun x => (binaryMark hphi (quotientSquare htwo hphi x.toMul)).toAdd
    toFun_smul := ?_
    exists_companion' := ⟨quotientBilinearForm htwo hphi, ?_⟩ }
  · intro a x
    classical
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp only [zero_smul, zero_mul]
      change (binaryMark hphi (quotientSquare htwo hphi 1)).toAdd = _
      have h : quotientSquare htwo hphi 1 = 1 :=
        SmallNonabelianTwoGroup.frattiniSquare_one htwo hphi
      simp [h]
    · simp
  · intro x y
    change (binaryMark hphi (quotientSquare htwo hphi (x.toMul * y.toMul))).toAdd = _
    rw [quotientSquare_mul, (binaryMark hphi).map_mul, (binaryMark hphi).map_mul]
    rfl


noncomputable def centralBilinearForm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) :=
      elementary_quotient_of_frattini_le htwo _ (central_of_normal_card_two _ hphi)
    LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ center Q)) := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    elementary_quotient_of_frattini_le htwo _ (central_of_normal_card_two _ hphi)
  exact bilinearOfMultiplicative (fun x y => binaryMark hphi (centralCommutator htwo x y))
    (by intro x y z; rw [centralCommutator_mul_left htwo hphi, (binaryMark hphi).map_mul])
    (by intro x y z; rw [centralCommutator_mul_right htwo hphi, (binaryMark hphi).map_mul])

theorem centralBilinearForm_apply (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ center Q) :
    centralBilinearForm htwo hphi (Additive.ofMul x) (Additive.ofMul y) =
      (binaryMark hphi (centralCommutator htwo x y)).toAdd := rfl

noncomputable def centralQuadraticForm (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥) :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) :=
      elementary_quotient_of_frattini_le htwo _ (central_of_normal_card_two _ hphi)
    QuadraticForm (ZMod 2) (Additive (Q ⧸ center Q)) := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    elementary_quotient_of_frattini_le htwo _ (central_of_normal_card_two _ hphi)
  refine {
    toFun := fun x => (binaryMark hphi (centralSquare htwo hcenterPhi x.toMul)).toAdd
    toFun_smul := ?_
    exists_companion' := ⟨centralBilinearForm htwo hphi, ?_⟩ }
  · intro a x
    classical
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp only [zero_smul, zero_mul]
      have h : centralSquare htwo hcenterPhi 1 = 1 := by
        apply Subtype.ext
        exact one_pow 2
      change (binaryMark hphi (centralSquare htwo hcenterPhi 1)).toAdd = _
      simp [h]
    · simp
  · intro x y
    change (binaryMark hphi (centralSquare htwo hcenterPhi (x.toMul * y.toMul))).toAdd = _
    rw [centralSquare_mul htwo hphi, (binaryMark hphi).map_mul, (binaryMark hphi).map_mul,
      centralPolar_eq_centralCommutator htwo hphi]
    rfl

@[simp] theorem quotientQuadraticForm_apply (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x : Q ⧸ frattini Q) :
    quotientQuadraticForm htwo hphi (Additive.ofMul x) =
      (binaryMark hphi (quotientSquare htwo hphi x)).toAdd := rfl

@[simp] theorem centralQuadraticForm_apply (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (x : Q ⧸ center Q) :
    centralQuadraticForm htwo hphi hcenterPhi (Additive.ofMul x) =
      (binaryMark hphi (centralSquare htwo hcenterPhi x)).toAdd := rfl

section QuotientProperties
variable (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)

theorem quotientBilinearForm_isAlt :
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
    (quotientBilinearForm htwo hphi).IsAlt := by
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
  intro x
  change (binaryMark hphi (quotientPolar htwo hphi x.toMul x.toMul)).toAdd = 0
  rw [quotientPolar_self, (binaryMark hphi).map_one]
  rfl

theorem quotientBilinearForm_isSymm :
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
    (quotientBilinearForm htwo hphi).IsSymm := by
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
  constructor
  intro x y
  exact congrArg (fun z => (binaryMark hphi z).toAdd)
    (quotientPolar_symm htwo hphi x.toMul y.toMul)

theorem quotientQuadraticForm_polar :
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
    (quotientQuadraticForm htwo hphi).polarBilin = quotientBilinearForm htwo hphi := by
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
  ext x y
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change (binaryMark hphi (quotientSquare htwo hphi (x.toMul * y.toMul))).toAdd -
      (binaryMark hphi (quotientSquare htwo hphi x.toMul)).toAdd -
      (binaryMark hphi (quotientSquare htwo hphi y.toMul)).toAdd = _
  rw [quotientSquare_mul, (binaryMark hphi).map_mul, (binaryMark hphi).map_mul]
  simp only [toAdd_mul]
  change (_ + _ + (binaryMark hphi _).toAdd) - _ - _ = (binaryMark hphi _).toAdd
  abel

theorem quotientBilinearForm_radical (x : Q ⧸ frattini Q) :
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
    (∀ y : Additive (Q ⧸ frattini Q),
      quotientBilinearForm htwo hphi (Additive.ofMul x) y = 0) ↔ x ∈ centerImage Q := by
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
  have hzero (a : frattini Q) : (binaryMark hphi a).toAdd = 0 ↔ a = 1 := by
    change binaryMark hphi a = 1 ↔ a = 1
    exact (binaryMark hphi).map_eq_one_iff
  have hrad := Set.ext_iff.mp (quotientPolar_radical_eq_centerImage htwo hphi) x
  change (∀ y, quotientPolar htwo hphi x y = 1) ↔ x ∈ centerImage Q at hrad
  rw [← hrad]
  constructor
  · intro h y
    exact (hzero _).mp (h (Additive.ofMul y))
  · intro h y
    exact (hzero _).mpr (h y.toMul)

end QuotientProperties

section CentralProperties
variable (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)

theorem centralBilinearForm_isAlt :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
    (centralBilinearForm htwo hphi).IsAlt := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
  intro x
  change (binaryMark hphi (centralCommutator htwo x.toMul x.toMul)).toAdd = 0
  rw [centralCommutator_self, (binaryMark hphi).map_one]
  rfl

theorem centralBilinearForm_isSymm :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
    (centralBilinearForm htwo hphi).IsSymm := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
  constructor
  intro x y
  exact congrArg (fun z => (binaryMark hphi z).toAdd)
    (centralCommutator_symm htwo hphi x.toMul y.toMul)

theorem centralBilinearForm_nondegenerate :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
    (centralBilinearForm htwo hphi).Nondegenerate := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
  have hsep : ∀ x : Additive (Q ⧸ center Q),
      (∀ y, centralBilinearForm htwo hphi x y = 0) → x = 0 := by
    intro x hx
    apply Additive.toMul.injective
    apply centralCommutator_nondegenerate htwo
    intro y
    apply (binaryMark hphi).injective
    rw [(binaryMark hphi).map_one]
    exact hx (Additive.ofMul y)
  exact ⟨hsep, fun y hy => hsep y (fun x => by
    rw [(centralBilinearForm_isSymm htwo hphi).eq]; exact hy x)⟩

theorem centralQuadraticForm_polar (hcenterPhi : frattini (center Q) = ⊥) :
    letI : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
    (centralQuadraticForm htwo hphi hcenterPhi).polarBilin =
      centralBilinearForm htwo hphi := by
  let : IsElementaryAbelian 2 (Q ⧸ center Q) := centralElementary htwo hphi
  ext x y
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change (binaryMark hphi (centralSquare htwo hcenterPhi (x.toMul * y.toMul))).toAdd -
      (binaryMark hphi (centralSquare htwo hcenterPhi x.toMul)).toAdd -
      (binaryMark hphi (centralSquare htwo hcenterPhi y.toMul)).toAdd = _
  rw [centralSquare_mul htwo hphi, (binaryMark hphi).map_mul, (binaryMark hphi).map_mul,
    centralPolar_eq_centralCommutator htwo hphi]
  simp only [toAdd_mul]
  change (_ + _ + (binaryMark hphi _).toAdd) - _ - _ = (binaryMark hphi _).toAdd
  abel

end CentralProperties


theorem quotientBilinearForm_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (x y : Q ⧸ frattini Q) :
    quotientBilinearForm htwo hphi
      (Additive.ofMul (quotientAut (frattini Q) aut x))
      (Additive.ofMul (quotientAut (frattini Q) aut y)) =
      quotientBilinearForm htwo hphi (Additive.ofMul x) (Additive.ofMul y) :=
  congrArg (fun z => (binaryMark hphi z).toAdd) (quotientPolar_invariant htwo hphi aut x y)

theorem quotientQuadraticForm_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (x : Q ⧸ frattini Q) :
    quotientQuadraticForm htwo hphi
      (Additive.ofMul (quotientAut (frattini Q) aut x)) =
      quotientQuadraticForm htwo hphi (Additive.ofMul x) :=
  congrArg (fun z => (binaryMark hphi z).toAdd) (quotientSquare_invariant htwo hphi aut x)

theorem centralBilinearForm_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (aut : MulAut Q)
    (x y : Q ⧸ center Q) :
    centralBilinearForm htwo hphi
      (Additive.ofMul (quotientAut (center Q) aut x))
      (Additive.ofMul (quotientAut (center Q) aut y)) =
      centralBilinearForm htwo hphi (Additive.ofMul x) (Additive.ofMul y) :=
  congrArg (fun z => (binaryMark hphi z).toAdd) (centralCommutator_invariant htwo hphi aut x y)

theorem centralQuadraticForm_invariant (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (aut : MulAut Q) (x : Q ⧸ center Q) :
    centralQuadraticForm htwo hphi hcenterPhi
      (Additive.ofMul (quotientAut (center Q) aut x)) =
      centralQuadraticForm htwo hphi hcenterPhi (Additive.ofMul x) :=
  congrArg (fun z => (binaryMark hphi z).toAdd)
    (centralSquare_invariant htwo hphi hcenterPhi aut x)

theorem centralBilinearForm_descent (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (x y : Q ⧸ frattini Q) :
    centralBilinearForm htwo hphi (Additive.ofMul (frattiniToCentral hphi x))
      (Additive.ofMul (frattiniToCentral hphi y)) =
      quotientBilinearForm htwo hphi (Additive.ofMul x) (Additive.ofMul y) :=
  congrArg (fun z => (binaryMark hphi z).toAdd)
    (centralCommutator_frattiniToCentral htwo hphi x y)

theorem centralQuadraticForm_descent (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) (hcenterPhi : frattini (center Q) = ⊥)
    (x : Q ⧸ frattini Q) :
    centralQuadraticForm htwo hphi hcenterPhi (Additive.ofMul (frattiniToCentral hphi x)) =
      quotientQuadraticForm htwo hphi (Additive.ofMul x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) x
  rfl

end SmallFrattini

