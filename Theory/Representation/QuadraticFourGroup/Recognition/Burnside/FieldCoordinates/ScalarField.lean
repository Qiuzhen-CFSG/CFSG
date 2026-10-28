module

public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside.FieldCoordinates.Data
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The field of the regular abelian scalar action

The two-point stabilizer D acts by conjugation regularly on the nonidentity
root elements. After choosing one such element, its orbit identifies D with
the nonzero additive coordinates. Adjoining zero and transporting addition
therefore gives a field: conjugation proves left distributivity, while
commutativity of D proves right distributivity. Finite-field uniqueness then
identifies this field with `GaloisField 2 n`, where the root group has order
`2 ^ n` and `1 < n`.

`exists_scalarCoordinates` constructs both equivalences for the actual
subgroups P and `twoPoint P Q`. Its compatibility formula uses direct
conjugation, so scalars multiply on the left. The transport construction
follows the pattern of `BenderSuzuki/External/Huppert/XI/SharpNearField.lean`,
with this orientation and with an abelian multiplicative group; no theorem
from that higher layer is imported.

Source: W. Burnside, *On a Class of Groups of Finite Order* (1900),
pp. 274–276, `refs/original/burnside-1900.pdf`.
-/

namespace Representation.QuadraticFourGroup.Burnside

universe u v

private structure ScalarCarrier (D : Type*) where
  val : WithZero D

private def scalarCarrierEquiv (D : Type*) : ScalarCarrier D ≃ WithZero D where
  toFun := ScalarCarrier.val
  invFun := ScalarCarrier.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The orbit of a nonzero vector under a regular abelian automorphism group
constructs a field, with the given action becoming scalar multiplication. -/
private theorem field_of_regular_action {A : Type u} {D : Type v}
    [AddCommGroup A] [CommGroup D] (ρ : D → A ≃+ A)
    (hρ : ∀ d r x, ρ (d * r) x = ρ d (ρ r x))
    (z : A) (hz : z ≠ 0) (hreg : ∀ x : A, x ≠ 0 → ∃! d : D, ρ d z = x) :
    ∃ (K : Type v) (_ : Field K) (e : A ≃+ K) (f : D ≃* Kˣ),
      ∀ (d : D) (x : A), e (ρ d x) = (f d : K) * e x := by
  classical
  have hρz (d : D) : ρ d z ≠ 0 :=
    fun he => hz ((ρ d).injective (he.trans (map_zero (ρ d)).symm))
  let q : D ≃ {x : A // x ≠ 0} := Equiv.ofBijective
    (fun d => ⟨ρ d z, hρz d⟩) (by
      constructor
      · intro d r hdr
        obtain ⟨s, _, hs⟩ := hreg (ρ d z) (hρz d)
        exact (hs d rfl).trans (hs r (congrArg Subtype.val hdr).symm).symm
      · intro x
        obtain ⟨d, hd, _⟩ := hreg x x.property
        exact ⟨d, Subtype.ext hd⟩)
  let w : WithZero D ≃ A :=
    (Equiv.optionCongr q).trans (Equiv.optionSubtypeNe 0)
  have hw0 : w 0 = 0 := rfl
  have hwq (d : D) : w (d : WithZero D) = ρ d z := rfl
  let K := ScalarCarrier D
  let m : K ≃ WithZero D := scalarCarrierEquiv D
  let a : K ≃ A := m.trans w
  let : AddCommGroup K := a.addCommGroup
  let e : A ≃+ K := a.addEquiv.symm
  have hm0 : m (0 : K) = 0 := by
    apply w.injective
    change a (0 : K) = w 0
    rw [hw0]
    exact a.addEquiv.map_zero
  let : One K := m.one
  let : Mul K := m.mul
  let : Inv K := m.Inv
  let : Div K := m.div
  let : Pow K ℕ := m.pow ℕ
  let : Pow K ℤ := m.pow ℤ
  let : CommGroupWithZero K :=
    m.injective.commGroupWithZero m hm0
      (by simp [Equiv.one_def])
      (by intro x y; simp [Equiv.mul_def])
      (by intro x; simp [Equiv.inv_def])
      (by intro x y; simp [Equiv.div_def])
      (by intro x n; simp [Equiv.pow_def])
      (by intro x n; simp [Equiv.pow_def])
  let s (d : D) : K := m.symm (d : WithZero D)
  have hms (d : D) : m (s d) = (d : WithZero D) := m.apply_symm_apply _
  have hes (d : D) : e.symm (s d) = ρ d z := by
    change w (m (s d)) = ρ d z
    rw [hms, hwq]
  have hsmul (d r : D) : s d * s r = s (d * r) := by
    apply m.injective
    rw [Equiv.mul_def, m.apply_symm_apply, hms, hms, hms, WithZero.coe_mul]
  have hex (x : K) (hx : x ≠ 0) : ∃ d : D, x = s d := by
    have hxe : e.symm x ≠ 0 := by
      intro he
      exact hx (e.symm.injective (by simpa using he))
    obtain ⟨d, hd, _⟩ := hreg (e.symm x) hxe
    exact ⟨d, e.symm.injective ((hes d).trans hd).symm⟩
  have hact (d : D) (x : K) : s d * x = e (ρ d (e.symm x)) := by
    by_cases hx : x = 0
    · subst x
      simp
    · obtain ⟨r, rfl⟩ := hex x hx
      apply e.symm.injective
      rw [hsmul, hes, e.symm_apply_apply, hes, hρ]
  have hleft (c x y : K) : c * (x + y) = c * x + c * y := by
    by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨d, rfl⟩ := hex c hc
      rw [hact, hact, hact, e.symm.map_add, map_add, e.map_add]
  let hK : Field K :=
    { (inferInstance : AddCommGroup K), (inferInstance : CommGroupWithZero K) with
      left_distrib := hleft
      right_distrib := fun x y c => by simpa only [mul_comm] using hleft c x y
      nnqsmul := _
      qsmul := _ }
  let : Field K := hK
  let f : D ≃* Kˣ :=
    ((Units.mapEquiv m.mulEquiv).trans WithZero.unitsWithZeroEquiv).symm
  have hf (d : D) : (f d : K) = s d := by
    apply m.injective
    rw [hms]
    simp [f]
  refine ⟨K, hK, e, f, fun d x => ?_⟩
  rw [hf, hact, e.symm_apply_apply]

open Theory.GroupTheory Theory.GroupTheory.InvolutionOddSpectrum

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]

/-- Construct finite-field coordinates from the actual regular abelian
two-point stabilizer, without assuming field coordinates or recognition. -/
public theorem exists_scalarCoordinates (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P Q : Sylow 2 G) (hPQ : P ≠ Q) :
    ∃ n : ℕ, 1 < n ∧ Nonempty (ScalarCoordinates P Q (GaloisField 2 n)) := by
  classical
  let : IsElementaryAbelian 2 P := (hG.subgroup P).elementaryAbelian P.isPGroup'
  let : CommGroup P := IsMulCommutative.instCommGroup
  let : IsMulCommutative (twoPoint P Q) := hG.twoPoint_commutative t ht P Q hPQ
  let : CommGroup (twoPoint P Q) := IsMulCommutative.instCommGroup
  let ρ (d : twoPoint P Q) : Additive P ≃+ Additive P :=
    (twoPointConj P Q d).toAdditive
  have hρ (d r : twoPoint P Q) (x : Additive P) :
      ρ (d * r) x = ρ d (ρ r x) := by
    change Additive.ofMul (twoPointConj P Q (d * r) x.toMul) =
      Additive.ofMul (twoPointConj P Q d (twoPointConj P Q r x.toMul))
    rw [map_mul]
    rfl
  obtain ⟨z, _, hz, _, _⟩ := hG.sylow_distinct_involutions t ht P
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hreg (x : Additive P) (hx : x ≠ 0) :
      ∃! d : twoPoint P Q, ρ d (Additive.ofMul z) = x := by
    have hx1 : x.toMul ≠ 1 := hx
    obtain ⟨d, hd, huniq⟩ := hG.twoPoint_conj_regular t ht P Q hPQ z x.toMul hz1 hx1
    refine ⟨d, ?_, fun r hr => huniq r ?_⟩
    · exact congrArg Additive.ofMul (Subtype.ext hd)
    · exact congrArg (fun a : Additive P => (a.toMul : G)) hr
  obtain ⟨K, hK, e, f, he⟩ := field_of_regular_action ρ hρ (Additive.ofMul z) hz1 hreg
  let : Field K := hK
  let : Finite K := Finite.of_equiv (Additive P) e.toEquiv
  obtain ⟨n, hn, hcard⟩ := sylow_card t ht P
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let j : K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      ← Nat.card_congr e.toEquiv, Nat.card_congr Additive.toMul,
      hcard, GaloisField.card 2 n (by omega)])
  refine ⟨n, hn, ⟨{
    additive := e.trans j.toAddEquiv
    scalars := f.trans (Units.mapEquiv j.toMulEquiv)
    conjugation := ?_ }⟩⟩
  intro d x
  change j (e (ρ d (Additive.ofMul x))) =
    j (f d : K) * j (e (Additive.ofMul x))
  rw [he, map_mul]

end Representation.QuadraticFourGroup.Burnside
