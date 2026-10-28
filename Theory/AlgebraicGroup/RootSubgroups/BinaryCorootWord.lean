module

public import Theory.AlgebraicGroup.Tori.Basic
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore

/-!
# Regular coroot words in characteristic two

For two regular additive curves, form the regular word
`n(t) = x(t)y(t⁻¹)x(t)` and normalize it as `n(1)⁻¹n(t)`.
No rank-one relation is assumed in its construction. In characteristic two
this is the usual Chevalley coroot word (GLS3, Theorem 1.12.1(c)--(d)).
If both curves lift with the same parameter power, this word lifts with
that power as well. Multiplicativity is deliberately a separate conclusion.
-/

public section
universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]

/-- The regular inclusion of the punctured affine line into the affine line. -/
private def kMultParameter : Variety.Morphism (KMult k) (KPlus k) where
  toFun := fun t => kPlusPoint (dPointEquiv 1 t 0 : k)
  regular := by
    intro i
    refine ⟨MvPolynomial.X (Sum.inl (ULift.up 0)), ?_⟩
    intro t
    rw [evalPolynomial_X]
    rfl

private noncomputable def binaryNormalizerWord {G : Variety k} [AlgebraicGroup G]
    (x y : Variety.Morphism (KPlus k) G) : Variety.Morphism (KMult k) G :=
  let xp := x.comp kMultParameter
  let ym := y.comp (kMultParameter.comp (invMorphism (KMult k)))
  (mulMorphism G).comp (((mulMorphism G).comp (xp.pair ym)).pair xp)

/-- The normalized regular word of two opposite additive curves. -/
noncomputable def binaryCorootWord {G : Variety k} [AlgebraicGroup G]
    (x y : Variety.Morphism (KPlus k) G) : Variety.Morphism (KMult k) G :=
  let n := binaryNormalizerWord x y
  (leftMulMorphism G (n.toFun 1)⁻¹).comp n

private theorem kMultParameter_inv (t : Variety.Point (KMult k)) :
    kMultParameter.toFun t⁻¹ = kPlusPoint ((dPointEquiv 1 t 0 : k)⁻¹) := by
  change kPlusPoint (dPointEntryInv 1 t 0) = kPlusPoint ((dPointEntry 1 t 0)⁻¹)
  rw [dPoint_entry_inv]

private theorem kMultParameter_one :
    kMultParameter.toFun (1 : Variety.Point (KMult k)) = kPlusPoint (1 : k) := by
  change kPlusPoint (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = _
  rw [dPointEquiv_one]
  rfl

/-- Pointwise form of the normalized word. -/
theorem binaryCorootWord_apply {G : Variety k} [AlgebraicGroup G]
    (x y : Variety.Morphism (KPlus k) G) (t : Variety.Point (KMult k)) :
    (binaryCorootWord x y).toFun t =
      (x.toFun (kPlusPoint 1) * y.toFun (kPlusPoint 1) * x.toFun (kPlusPoint 1))⁻¹ *
      (x.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) *
        y.toFun (kPlusPoint ((dPointEquiv 1 t 0 : k)⁻¹)) *
        x.toFun (kPlusPoint (dPointEquiv 1 t 0 : k))) := by
  change (x.toFun (kMultParameter.toFun 1) *
    y.toFun (kMultParameter.toFun (1 : Variety.Point (KMult k))⁻¹) *
    x.toFun (kMultParameter.toFun 1))⁻¹ *
    (x.toFun (kMultParameter.toFun t) * y.toFun (kMultParameter.toFun t⁻¹) *
    x.toFun (kMultParameter.toFun t)) = _
  rw [inv_one, kMultParameter_one, kMultParameter_inv t]
  rfl

@[simp] theorem binaryCorootWord_one {G : Variety k} [AlgebraicGroup G]
    (x y : Variety.Morphism (KPlus k) G) :
    (binaryCorootWord x y).toFun 1 = 1 := inv_mul_cancel _

/-- A common power on the two additive parameters induces the same power on
the multiplicative parameter of the normalized word. -/
theorem binaryCorootWord_map_of_parameter_power
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G)
    (x y : Variety.Morphism (KPlus k) G)
    (xH yH : Variety.Morphism (KPlus k) H) (n : ℕ)
    (hx : ∀ s, φ.onPoints (xH.toFun (kPlusPoint s)) = x.toFun (kPlusPoint (s ^ n)))
    (hy : ∀ s, φ.onPoints (yH.toFun (kPlusPoint s)) = y.toFun (kPlusPoint (s ^ n)))
    (t : Variety.Point (KMult k)) :
    φ.onPoints ((binaryCorootWord xH yH).toFun t) =
      (binaryCorootWord x y).toFun (t ^ n) := by
  rw [binaryCorootWord_apply, binaryCorootWord_apply]
  simp only [map_mul, map_inv, hx, hy, one_pow, inv_pow]
  have ht : (dPointEquiv 1 (t ^ n) 0 : k) = (dPointEquiv 1 t 0 : k) ^ n :=
    congrArg Units.val (congrFun (dPointEquiv_pow 1 n t) 0)
  rw [ht]

private def affineParameterPower (n : ℕ) : Variety.Morphism (KPlus k) (KPlus k) where
  toFun := fun t => kPlusPoint (t.val PUnit.unit ^ n)
  regular := by
    intro i
    refine ⟨MvPolynomial.X PUnit.unit ^ n, ?_⟩
    intro t
    change t.val PUnit.unit ^ n = evalPolynomial t.val (MvPolynomial.X PUnit.unit ^ n)
    simp [evalPolynomial]

/-- Different characteristic powers on two lifted curves can be increased
to a common power by regular reparametrization. -/
theorem exists_common_binary_parameter_lifts
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (x y : Variety.Morphism (KPlus k) G)
    (hx : ∃ a : ℕ, ∃ xH : Variety.Morphism (KPlus k) H,
      ∀ s, φ.onPoints (xH.toFun (kPlusPoint s)) = x.toFun (kPlusPoint (s ^ (2 ^ a))))
    (hy : ∃ b : ℕ, ∃ yH : Variety.Morphism (KPlus k) H,
      ∀ s, φ.onPoints (yH.toFun (kPlusPoint s)) = y.toFun (kPlusPoint (s ^ (2 ^ b)))) :
    ∃ a : ℕ, ∃ xH yH : Variety.Morphism (KPlus k) H,
      (∀ s, φ.onPoints (xH.toFun (kPlusPoint s)) = x.toFun (kPlusPoint (s ^ (2 ^ a)))) ∧
      (∀ s, φ.onPoints (yH.toFun (kPlusPoint s)) = y.toFun (kPlusPoint (s ^ (2 ^ a)))) := by
  obtain ⟨a, xH, hx⟩ := hx
  obtain ⟨b, yH, hy⟩ := hy
  refine ⟨a + b, xH.comp (affineParameterPower (2 ^ b)),
    yH.comp (affineParameterPower (2 ^ a)), ?_, ?_⟩
  · intro s
    change φ.onPoints (xH.toFun (kPlusPoint (s ^ (2 ^ b)))) = _
    rw [hx, ← pow_mul, pow_add, Nat.mul_comm (2 ^ b) (2 ^ a)]
  · intro s
    change φ.onPoints (yH.toFun (kPlusPoint (s ^ (2 ^ a)))) = _
    rw [hy, ← pow_mul, pow_add]

end Theory.AlgebraicGroup
