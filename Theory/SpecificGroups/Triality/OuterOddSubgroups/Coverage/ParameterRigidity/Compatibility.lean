module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.Torus

/-!
# Compatibility of the two triality root-field automorphisms

A scalar-semilinear map on both signed roots of a rank-one subgroup carries
its coroot word h(t) to h(e(t)); the scalar cancels in the product of the two
Weyl words. The central coroot h(t) acts on the arm root by multiplication
by t⁻¹, viewed in the cubic extension. Applying the ambient automorphism to
this folded D₄ relation proves that the two recovered field automorphisms
agree on the actual q-Frobenius fixed subfield.

This is the common-field step of Steinberg Theorem 30(4) in the triality
case of Theorem 36 (`refs/KGroup/GLS3/Chapter2St1.tex`, pp.163–164 and
197–198), using the explicit coroot relations of GLS3 §2.4
(`refs/KGroup/GLS3/chapter2.tex`). It uses neither global generation nor
simplicity, and places no restriction on the cubic automorphism at q = 2.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Parabolics ConcreteBruhat TorusCoordinates ElementaryCentralKernel
noncomputable section

/-- The actual descended coroot word at one folded node. -/
def nodeTorus (P : Parameters) (hp : P.prime = 2) (i : Node)
    (t : (RootField P i)ˣ) : Carrier P :=
  toCarrier P (foldedTorusElementary P hp i t)

theorem nodeTorus_eq_rankOne (P : Parameters) (hp : P.prime = 2) (i : Node)
    (t : (RootField P i)ˣ) :
    nodeTorus P hp i t = rankOne P hp i (weyl t.val * weyl 1) := by
  let := rootField_charTwo P hp i
  have hpos (r) : rankOne P hp i (upper r) = rootElement P hp true i r :=
    rankOne_signed P hp true i r
  have hneg (r) : rankOne P hp i (lower r) = rootElement P hp false i r :=
    rankOne_signed P hp false i r
  simp only [nodeTorus, foldedTorusElementary, foldedWeylElementary,
    weyl, map_mul, hpos, hneg, CharTwo.neg_eq, inv_one, rootElement]

private theorem weyl_scaled {F : Type*} [Field F] [CharP F 2]
    (c t : F) (hc : c ≠ 0) (ht : t ≠ 0) :
    weyl (c * t) * weyl c = weyl t * weyl 1 := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, weyl_val (c*t) (mul_ne_zero hc ht),
    weyl_val c hc, weyl_val t ht, weyl_val (1 : F) one_ne_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, _root_.mul_inv_rev, mul_assoc]
  rw [mul_left_comm, mul_inv_cancel₀ hc, mul_one]

theorem map_nodeTorus (P : Parameters) (hp : P.prime = 2) (a : MulAut (Carrier P))
    (i : Node) (c : (RootField P i)ˣ) (e : RootField P i ≃+* RootField P i)
    (hpos : ∀ r, a (rootElement P hp true i r) = rootElement P hp true i (c.val * e r))
    (hneg : ∀ r, a (rootElement P hp false i r) = rootElement P hp false i (c.val⁻¹ * e r))
    (t : (RootField P i)ˣ) :
    a (nodeTorus P hp i t) = nodeTorus P hp i (Units.map e.toMonoidHom t) := by
  let := rootField_charTwo P hp i
  have hupper (r) : a (rankOne P hp i (upper r)) = rankOne P hp i (upper (c.val * e r)) := by
    change a (rankOne P hp i (signed true r)) = rankOne P hp i (signed true (c.val * e r))
    simpa only [rankOne_signed] using hpos r
  have hlower (r) : a (rankOne P hp i (lower r)) = rankOne P hp i (lower (c.val⁻¹ * e r)) := by
    change a (rankOne P hp i (signed false r)) = rankOne P hp i (signed false (c.val⁻¹ * e r))
    simpa only [rankOne_signed] using hneg r
  have hw (r) : a (rankOne P hp i (weyl r)) = rankOne P hp i (weyl (c.val * e r)) := by
    simp only [weyl, map_mul, hupper, hlower, map_inv₀, _root_.mul_inv_rev]
    rw [mul_comm (c.val⁻¹)]
  rw [nodeTorus_eq_rankOne, nodeTorus_eq_rankOne, map_mul, map_mul, hw, hw]
  rw [map_one, mul_one, ← map_mul]
  exact congrArg (rankOne P hp i) (weyl_scaled c.val (e t.val) c.ne_zero
    (by exact e.injective.ne t.ne_zero |>.trans_eq (map_zero e)))

private theorem centralTorus_arms (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (r : ExtensionField P) :
    nodeTorus P hp .central t * rootElement P hp true .arms r *
      (nodeTorus P hp .central t)⁻¹ = rootElement P hp true .arms (t.val.val⁻¹ * r) := by
  apply congrArg (toCarrier P) (α := ElementaryGroup P)
  apply Subtype.ext
  apply Subtype.ext
  change torusWord P 1 (fixedUnit P t) * foldedRoot P true r *
    (torusWord P 1 (fixedUnit P t))⁻¹ = foldedRoot P true (t.val.val⁻¹ * r)
  have hconj (g x y : SplitGroup P) :
      g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
  simp only [foldedRoot, hconj, torusWord_signed P hp]
  simp [Theory.AlgebraicGroup.StandardRootSystem.typeDCartanMatrix,
    fixedUnit, map_mul, map_inv₀, ht, -fieldFrobenius_apply]

/-- The central coroot action on the arm root identifies the two field maps. -/
theorem fields_compatible (P : Parameters) (hp : P.prime = 2) (a : MulAut (Carrier P))
    (c : (i : Node) → (RootField P i)ˣ)
    (e : (i : Node) → RootField P i ≃+* RootField P i)
    (hpos : ∀ i r, a (rootElement P hp true i r) = rootElement P hp true i ((c i).val * e i r))
    (hneg : ∀ i r, a (rootElement P hp false i r) = rootElement P hp false i ((c i).val⁻¹ * e i r)) :
    coefficientFixedField P (e .arms) = e .central := by
  apply RingEquiv.ext
  intro r
  apply Subtype.ext
  change e .arms r.val = (e .central r).val
  by_cases hr : r = 0
  · simp [hr]
  let t : (fixedField P)ˣ := (Units.mk0 r hr)⁻¹
  have ht : t.val.val⁻¹ = r.val := by simp [t]
  have h := congrArg a (centralTorus_arms P hp t 1)
  simp only [map_mul, map_inv] at h
  simp only [map_nodeTorus P hp a .central (c .central) (e .central)
    (hpos .central) (hneg .central), hpos, map_one, mul_one] at h
  rw [centralTorus_arms, ht] at h
  have he := rootElement_injective P hp true .arms h
  have htc : (Units.map (e .central).toMonoidHom t).val.val⁻¹ = (e .central r).val := by
    simp [t, -fieldFrobenius_apply]
  rw [htc, mul_comm] at he
  exact mul_left_cancel₀ (c .arms).ne_zero he.symm

end
end Triality.Standard.OuterOdd.Coverage.ParameterRigidity
