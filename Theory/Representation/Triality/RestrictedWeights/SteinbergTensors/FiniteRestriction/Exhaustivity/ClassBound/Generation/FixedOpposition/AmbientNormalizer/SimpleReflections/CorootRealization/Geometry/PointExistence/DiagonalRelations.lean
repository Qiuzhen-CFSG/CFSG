module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointExistence.Relations
public import Theory.AlgebraicGroup.Solvable.CentralCommutatorExponent

/-!
# Diagonal words for a swapping actual root pair

The actual cocharacter supplies every nonzero scaling of the upper root
curve and the inverse scaling of the lower curve. Transporting the assumed
swap through those torus conjugations proves square scaling for the
right-normalized word `d(a) = x(a)y(a⁻¹)x(a)w`.

The resulting sandwich identity `d(a²b) = d(a)d(b)d(a)` gives all natural
power identities and shows that commutators of diagonal words centralize
all diagonal words. Algebraic closedness makes each diagonal word divisible
inside this family. The uniform exponent bound for central commutators in
the actual opposite-pair algebraic subgroup then kills these commutators.
Commutation and the sandwich identity prove multiplicativity, completing
both diagonal relations from the swapping premise.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and §1.12,
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg §6,
`refs/KGroup/GLS3/Chapter2St2.tex`. The raw GLS word is normalized on the
left and has the inverse orientation to the word used here.
-/

namespace SwappedDiagonalWords
variable {k G : Type*} [Field k] [Group G]
variable (x y : k → G)
private def n (a : k) := x a * y a⁻¹ * x a
private def d (a : k) := n x y a * n x y 1
variable (hx : ∀ a, x a * x a = 1) (hy : ∀ a, y a * y a = 1)
include hx hy
private lemma n_sq (a : k) : n x y a * n x y a = 1 := by
  unfold n
  calc
    _ = x a * y a⁻¹ * (x a * x a) * y a⁻¹ * x a := by group
    _ = 1 := by rw [hx, mul_one, mul_assoc (x a), hy, mul_one, hx]
private lemma n_inv (a : k) : (n x y a)⁻¹ = n x y a :=
  inv_eq_of_mul_eq_one_left (n_sq x y hx hy a)

variable (hs : ∀ b, n x y 1 * x b * n x y 1 = y b)
variable (ht : ∀ a : k, a ≠ 0 → ∃ f : G ≃* G,
  (∀ b, f (x b) = x (a * b)) ∧ (∀ b, f (y b) = y (a⁻¹ * b)))

include hs ht
private lemma scaled_swap (a : k) (ha : a ≠ 0) (b : k) :
    n x y a * x b * n x y a = y ((a⁻¹)^2 * b) ∧
    n x y a * y b * n x y a = x (a^2 * b) := by
  obtain ⟨f, hf, hg⟩ := ht a ha
  have hn : f (n x y 1) = n x y a := by simp [n, hf, hg]
  have hrev (c : k) : n x y 1 * y c * n x y 1 = x c := by
    rw [← hs c]
    calc
      _ = (n x y 1 * n x y 1) * x c * (n x y 1 * n x y 1) := by group
      _ = _ := by rw [n_sq x y hx hy]; simp
  constructor
  · have h := congrArg f (hs (a⁻¹ * b))
    simpa only [map_mul, hn, hf, hg, ← mul_assoc, mul_inv_cancel₀ ha,
      one_mul, pow_two] using h
  · have h := congrArg f (hrev (a * b))
    simpa only [map_mul, hn, hf, hg, ← mul_assoc, inv_mul_cancel₀ ha,
      one_mul, pow_two] using h

private lemma scaling (a : k) (ha : a ≠ 0) (b : k) :
    d x y a * x b * (d x y a)⁻¹ = x (a^2 * b) ∧
    d x y a * y b * (d x y a)⁻¹ = y ((a⁻¹)^2 * b) := by
  have hswap := scaled_swap x y hx hy hs ht 1 one_ne_zero b
  simp only [one_pow, one_mul, inv_one] at hswap
  constructor
  · calc
      _ = n x y a * (n x y 1 * x b * n x y 1) * n x y a := by
        simp only [d, mul_inv_rev, n_inv x y hx hy]; group
      _ = _ := by rw [hs b]; exact (scaled_swap x y hx hy hs ht a ha b).2
  · calc
      _ = n x y a * (n x y 1 * y b * n x y 1) * n x y a := by
        simp only [d, mul_inv_rev, n_inv x y hx hy]; group
      _ = _ := by rw [hswap.2]; exact (scaled_swap x y hx hy hs ht a ha b).1

private lemma sandwich (a b : k) (ha : a ≠ 0) :
    d x y (a^2 * b) = d x y a * d x y b * d x y a := by
  have hn : d x y a * n x y b * (d x y a)⁻¹ = n x y (a^2 * b) := by
    calc
      _ = (d x y a * x b * (d x y a)⁻¹) *
          (d x y a * y b⁻¹ * (d x y a)⁻¹) *
          (d x y a * x b * (d x y a)⁻¹) := by unfold n; group
      _ = _ := by
        rw [(scaling x y hx hy hs ht a ha b).1,
          (scaling x y hx hy hs ht a ha b⁻¹).2]
        simp only [n, mul_inv, inv_pow]
  rw [d, ← hn]
  simp only [d, mul_inv_rev, n_inv x y hx hy]
  group

end SwappedDiagonalWords

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K] {S : Geometry K} {i : Fin 4}
namespace SimpleRootSL2Parameters
variable (P : SimpleRootSL2Parameters S i)
private noncomputable def ambient (_P : SimpleRootSL2Parameters S i) : Target (S := S) (i := i) →* Variety.Point K :=
  (oppositePairGeneratedSubgroup
    (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).inclusion.onPoints
omit [IsAlgClosed k] in
private lemma ambient_injective : Function.Injective P.ambient :=
  ClosedSubgroup.inclusion_injective _
omit [IsAlgClosed k] in
private lemma ambient_upper (b : k) : P.ambient (P.upper b) =
    (S.roots.rootSubgroup (S.simpleRoot i).val).includePoint (P.plus.value b) := by
  rw [P.upper_eq]
  exact oppositePairPlusMorphism_inclusion_apply _ _ _
omit [IsAlgClosed k] in
private lemma ambient_lower (b : k) : P.ambient (P.lower b) =
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint
      (P.minus.value b) := by
  rw [P.lower_eq]
  exact oppositePairMinusMorphism_inclusion_apply _ _ _

private lemma ambientScaling (a : k) (ha : a ≠ 0) :
    ∃ f : Variety.Point K ≃* Variety.Point K,
      (∀ b, f (P.ambient (P.upper b)) = P.ambient (P.upper (a * b))) ∧
      (∀ b, f (P.ambient (P.lower b)) = P.ambient (P.lower (a⁻¹ * b))) := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq a zero_lt_two
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht; exact ha ht.symm
  let r := (S.simpleRoot i).val
  let q : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => Units.mk0 t ht0)
  let s := (S.roots.rootCocharacter r).onPoints q
  have hc : (S.roots.rootWeight r).pointCharacter s = a := by
    have he := S.realized.rootWeight_rootCocharacter r r q
    have hr : S.roots.pairing r r = 2 := S.realized.2.2.2.2.2.2.1 r
    rw [hr] at he
    simpa [s, q, ht] using he
  have hci : (S.roots.rootWeight (S.roots.neg r)).pointCharacter s = a⁻¹ := by
    rw [S.realized.2.2.2.1 r]
    change ((torusPointEval S.torus.carrierVariety s ((S.roots.rootWeight r)⁻¹) : kˣ) : k) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact congrArg Inv.inv hc
  refine ⟨MulAut.conj (S.torus.includePoint s)⁻¹, ?_, ?_⟩
  · intro b
    simp only [MulAut.conj_apply, inv_inv, P.ambient_upper]
    have h := (S.realized.2.2.1 r).2 P.plus b s
    rwa [hc] at h
  · intro b
    simp only [MulAut.conj_apply, inv_inv, P.ambient_lower]
    have h := (S.realized.2.2.1 (S.roots.neg r)).2 P.minus b s
    rwa [hci] at h

/-- Direct conjugation by the diagonal word scales the two actual root
parameters by reciprocal squares. -/
public lemma diagonal_conjugation_of_weylSwaps (hP : P.WeylSwaps)
    (a : k) (ha : a ≠ 0) (b : k) :
    P.diagonal a * P.upper b * (P.diagonal a)⁻¹ = P.upper (a^2*b) ∧
    P.diagonal a * P.lower b * (P.diagonal a)⁻¹ = P.lower ((a⁻¹)^2*b) := by
  let x := fun t => P.ambient (P.upper t)
  let y := fun t => P.ambient (P.lower t)
  have hx (t : k) : x t * x t = 1 := by
    dsimp [x]; rw [← map_mul, P.upper_sq, map_one]
  have hy (t : k) : y t * y t = 1 := by
    dsimp [y]; rw [← map_mul, P.lower_sq, map_one]
  have hs (t : k) : SwappedDiagonalWords.n x y 1 * x t *
      SwappedDiagonalWords.n x y 1 = y t := by
    simpa only [SwappedDiagonalWords.n, x, y, inv_one, ← map_mul, weyl]
      using congrArg P.ambient (hP t)
  have h := SwappedDiagonalWords.scaling x y hx hy hs P.ambientScaling a ha b
  constructor
  · apply P.ambient_injective
    simpa only [SwappedDiagonalWords.d, SwappedDiagonalWords.n, x, y,
      diagonal, weyl, inv_one, map_mul, map_inv] using h.1
  · apply P.ambient_injective
    simpa only [SwappedDiagonalWords.d, SwappedDiagonalWords.n, x, y,
      diagonal, weyl, inv_one, map_mul, map_inv] using h.2
/-- The word satisfies the multiplicative sandwich identity, before any
multiplication law for two arbitrary diagonal words is assumed. -/
public lemma diagonal_sandwich_of_weylSwaps (hP : P.WeylSwaps)
    (a b : k) (ha : a ≠ 0) :
    P.diagonal (a^2 * b) = P.diagonal a * P.diagonal b * P.diagonal a := by
  let x := fun t => P.ambient (P.upper t)
  let y := fun t => P.ambient (P.lower t)
  have hx (t : k) : x t * x t = 1 := by
    dsimp [x]; rw [← map_mul, P.upper_sq, map_one]
  have hy (t : k) : y t * y t = 1 := by
    dsimp [y]; rw [← map_mul, P.lower_sq, map_one]
  have hs (t : k) : SwappedDiagonalWords.n x y 1 * x t *
      SwappedDiagonalWords.n x y 1 = y t := by
    simpa only [SwappedDiagonalWords.n, x, y, inv_one, ← map_mul, weyl]
      using congrArg P.ambient (hP t)
  apply P.ambient_injective
  simpa only [SwappedDiagonalWords.d, SwappedDiagonalWords.n, x, y,
    diagonal, weyl, inv_one, map_mul] using
    SwappedDiagonalWords.sandwich x y hx hy hs P.ambientScaling a b ha

/-- Natural powers of a diagonal word agree with powers of its parameter. -/
public lemma diagonal_pow_of_weylSwaps (hP : P.WeylSwaps)
    (a : k) (ha : a ≠ 0) (m : ℕ) : P.diagonal (a^m) = (P.diagonal a)^m := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [pow_zero, P.diagonal_one]
  | one => simp only [pow_one]
  | more n ih _ =>
    rw [show a^(n+2) = a^2 * a^n by ring,
      P.diagonal_sandwich_of_weylSwaps hP a (a^n) ha, ih]
    group

open scoped commutatorElement
/-- The subgroup generated by the nonzero diagonal words has central
commutators: each commutator already centralizes every generating word. -/
public lemma diagonal_commutator_commute_of_weylSwaps (hP : P.WeylSwaps)
    (a b c : k) (ha : a ≠ 0) (hb : b ≠ 0) :
    Commute ⁅P.diagonal a, P.diagonal b⁆ (P.diagonal c) := by
  have he (t : k) :
      P.diagonal a * P.diagonal b * P.diagonal t * P.diagonal b * P.diagonal a =
      P.diagonal b * P.diagonal a * P.diagonal t * P.diagonal a * P.diagonal b := by
    calc
      _ = P.diagonal (a^2 * (b^2 * t)) := by
        rw [P.diagonal_sandwich_of_weylSwaps hP _ _ ha,
          P.diagonal_sandwich_of_weylSwaps hP _ _ hb]
        group
      _ = P.diagonal (b^2 * (a^2 * t)) := by congr 1; ring
      _ = _ := by
        rw [P.diagonal_sandwich_of_weylSwaps hP _ _ hb,
          P.diagonal_sandwich_of_weylSwaps hP _ _ ha]
        group
  have hc : Commute (P.diagonal a * P.diagonal b) (P.diagonal b * P.diagonal a) := by
    change (P.diagonal a * P.diagonal b) * (P.diagonal b * P.diagonal a) =
      (P.diagonal b * P.diagonal a) * (P.diagonal a * P.diagonal b)
    simpa only [P.diagonal_one, mul_one, mul_assoc] using he 1
  change ⁅P.diagonal a, P.diagonal b⁆ * P.diagonal c =
    P.diagonal c * ⁅P.diagonal a, P.diagonal b⁆
  calc
    _ = (P.diagonal a * P.diagonal b) *
        (P.diagonal b * P.diagonal a)⁻¹ * P.diagonal c := by
      simp only [commutatorElement_def]; group
    _ = (P.diagonal b * P.diagonal a)⁻¹ *
        (P.diagonal a * P.diagonal b) * P.diagonal c := by rw [hc.inv_right.eq]
    _ = (P.diagonal b * P.diagonal a)⁻¹ *
        (P.diagonal a * P.diagonal b * P.diagonal c * P.diagonal b * P.diagonal a) *
        (P.diagonal b * P.diagonal a)⁻¹ := by group
    _ = (P.diagonal b * P.diagonal a)⁻¹ *
        (P.diagonal b * P.diagonal a * P.diagonal c * P.diagonal a * P.diagonal b) *
        (P.diagonal b * P.diagonal a)⁻¹ := by rw [he c]
    _ = _ := by simp only [commutatorElement_def]; group

private lemma central_commutator_pow_left {H : Type*} [Group H]
    (x y : H) (hc : Commute ⁅x, y⁆ x) (m : ℕ) : ⁅x^m, y⁆ = ⁅x, y⁆^m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', commutatorElement_mul_left_eq_conj_mul, ih,
      (hc.symm.pow_right n).eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one, pow_succ]

/-- A uniform exponent for central commutators kills the commutators of these
infinitely divisible diagonal words. The exponent premise remains explicit. -/
public lemma diagonal_commute_of_weylSwaps_of_centralCommutatorBound (hP : P.WeylSwaps)
    (hbound : ∃ m : ℕ, 0 < m ∧ ∀ x y : Target (S := S) (i := i),
      Commute ⁅x, y⁆ x → Commute ⁅x, y⁆ y → ⁅x, y⁆^m = 1)
    (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : Commute (P.diagonal a) (P.diagonal b) := by
  obtain ⟨m, hm, hbound⟩ := hbound
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a hm
  have hr0 : r ≠ 0 := by
    intro hz
    have : a = 0 := by rw [← hr, hz, zero_pow (Nat.ne_of_gt hm)]
    exact ha this
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← hr, P.diagonal_pow_of_weylSwaps hP r hr0 m,
    central_commutator_pow_left _ _
      (P.diagonal_commutator_commute_of_weylSwaps hP r b r hr0 hb)]
  exact hbound _ _ (P.diagonal_commutator_commute_of_weylSwaps hP r b r hr0 hb)
    (P.diagonal_commutator_commute_of_weylSwaps hP r b b hr0 hb)

/-- Pairwise commutation, together with the proved sandwich identity, gives
multiplicativity; square scaling already follows from the swapping premise. -/
public lemma diagonalRelations_of_weylSwaps_of_commute (hP : P.WeylSwaps)
    (hc : ∀ a b : k, a ≠ 0 → b ≠ 0 → Commute (P.diagonal a) (P.diagonal b)) :
    P.DiagonalRelations := by
  constructor
  · intro a b ha hb
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a zero_lt_two
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact ha hr.symm
    rw [← hr, P.diagonal_sandwich_of_weylSwaps hP r b hr0,
      P.diagonal_pow_of_weylSwaps hP r hr0 2]
    calc
      _ = P.diagonal r * (P.diagonal b * P.diagonal r) := by group
      _ = P.diagonal r * (P.diagonal r * P.diagonal b) := by rw [(hc b r hb hr0).eq]
      _ = _ := by simp only [pow_two, mul_assoc]
  · intro a ha b
    exact (mul_inv_eq_iff_eq_mul).mp
      (P.diagonal_conjugation_of_weylSwaps hP a ha b).1

/-- Reduction of the multiplication law to an explicit characteristic-two
linear algebraic group bound. -/
public lemma diagonalRelations_of_weylSwaps_of_centralCommutatorBound (hP : P.WeylSwaps)
    (hbound : ∃ m : ℕ, 0 < m ∧ ∀ x y : Target (S := S) (i := i),
      Commute ⁅x, y⁆ x → Commute ⁅x, y⁆ y → ⁅x, y⁆^m = 1) : P.DiagonalRelations :=
  P.diagonalRelations_of_weylSwaps_of_commute hP
    (P.diagonal_commute_of_weylSwaps_of_centralCommutatorBound hP hbound)

/-- For the actual opposite-root pair, swapping implies multiplicativity and
square scaling of the right-normalized diagonal words. The uniform central
commutator bound is supplied by the generated algebraic subgroup itself. -/
public theorem diagonalRelations_of_weylSwaps (hP : P.WeylSwaps) :
    P.DiagonalRelations :=
  P.diagonalRelations_of_weylSwaps_of_centralCommutatorBound hP
    (exists_centralCommutatorExponent (oppositePairGeneratedSubgroup
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).carrierVariety)

end SimpleRootSL2Parameters
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
