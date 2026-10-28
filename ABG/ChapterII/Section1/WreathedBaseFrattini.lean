module
public import ABG.ChapterII.Section1.WreathedBaseProduct
public import Theory.GroupTheory.PGroup.HomocyclicFrattini
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The Frattini quotient of the wreathed base

For a chosen wreathed presentation of height at least two, the base subgroup
has Klein four Frattini quotient, and the classes of its two distinguished
generators are distinct. This is the base-quotient input in the proof of ABG
Chapter II Section 1 Proposition 2, article p.12, used to detect the
nontrivial action that interchanges the two generators.

The product coordinates identify the base with two cyclic groups of order
`2^n`. Reindexing this product by `Bool` permits use of the standard homocyclic
Frattini theorem: its Frattini subgroup is precisely the kernel of coordinate
reduction modulo two. Transporting that identity gives a quotient equivalence
with the two-dimensional mod-two group. Its cardinality and exponent establish
the Klein four structure, and the first reduced coordinate separates the
presentation generators.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private def pairCoordinates (q : ℕ) :
    (Multiplicative (ZMod q) × Multiplicative (ZMod q)) ≃*
      StandardHomocyclicCover Bool q where
  toFun x := Multiplicative.ofAdd (fun b => if b then x.1.toAdd else x.2.toAdd)
  invFun x := (Multiplicative.ofAdd (x.toAdd true), Multiplicative.ofAdd (x.toAdd false))
  left_inv x := by simp
  right_inv x := by ext b; cases b <;> rfl
  map_mul' x y := by ext b; cases b <;> rfl

private noncomputable def coordinates : P.U ≃* StandardHomocyclicCover Bool (2 ^ n) :=
  P.baseEquiv.trans (pairCoordinates (2 ^ n))

private theorem frattini_coordinates :
    frattini P.U = (frattini (StandardHomocyclicCover Bool (2 ^ n))).comap
      P.coordinates.toMonoidHom := by
  apply le_antisymm (frattini_le_comap_frattini_of_surjective P.coordinates.surjective)
  intro x hx
  have h := frattini_le_comap_frattini_of_surjective
    (φ := P.coordinates.symm.toMonoidHom) P.coordinates.symm.surjective hx
  simpa using h

private noncomputable def reduction : P.U →* StandardHomocyclicCover Bool 2 :=
  (standardHomocyclicCoverReduction Bool 2 n (by have := P.height; omega)).comp
    P.coordinates.toMonoidHom

private theorem reduction_surjective : Function.Surjective P.reduction :=
  (standardHomocyclicCoverReduction_surjective Bool 2 n (by have := P.height; omega)).comp
    P.coordinates.surjective

private theorem frattini_eq_kernel : frattini P.U = P.reduction.ker := by
  rw [P.frattini_coordinates,
    standardHomocyclicCover_frattini_eq_reduction_ker Bool 2 n (by have := P.height; omega)]
  rfl

private noncomputable def quotientCoordinates :
    P.U ⧸ frattini P.U ≃* StandardHomocyclicCover Bool 2 :=
  (QuotientGroup.quotientMulEquivOfEq P.frattini_eq_kernel).trans
    (QuotientGroup.quotientKerEquivOfSurjective P.reduction P.reduction_surjective)

/-- The wreathed base has Klein four Frattini quotient, with distinct generator classes. -/
public theorem base_frattini_structure :
    IsKleinFour (P.U ⧸ frattini P.U) ∧
      ∀ s t : P.U, (s : S) = P.s → (t : S) = P.t →
        QuotientGroup.mk' (frattini P.U) s ≠ QuotientGroup.mk' (frattini P.U) t := by
  constructor
  · constructor
    · rw [Nat.card_congr P.quotientCoordinates.toEquiv]
      simp [StandardHomocyclicCover, Nat.card_eq_fintype_card]
    · rw [Monoid.exponent_eq_of_mulEquiv P.quotientCoordinates]
      exact standardHomocyclicCover_exponent Bool 2
  · intro s t hs ht he
    have hs' := P.baseEquiv_apply_eq s 1 0 (by simpa using hs.symm)
    have ht' := P.baseEquiv_apply_eq t 0 1 (by simpa using ht.symm)
    have hr : P.reduction s = P.reduction t := by
      have hk := QuotientGroup.eq.mp he
      rw [P.frattini_eq_kernel] at hk
      simpa only [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] using hk
    have hc := congrArg (fun x : StandardHomocyclicCover Bool 2 => x.toAdd true) hr
    simp [reduction, coordinates, pairCoordinates, hs', ht',
      standardHomocyclicCoverReduction, standardHomocyclicCoverAddReduction] at hc
    rw [ZMod.cast_one (dvd_pow_self 2 (by have := P.height; omega))] at hc
    norm_num at hc

end ABG.Wreathed.Presentation
