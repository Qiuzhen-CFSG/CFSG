module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal

/-!
# Simple-operator equations for central E6 words in E7 and E8

All roots in the actual E7 and E8 coordinate systems have squared norm two.
Consequently no root differs from another by three times a root, and the
third divided power of every signed simple operator vanishes integrally.
For odd characteristic, subtracting the root-curve values at one and minus
one recovers twice the first operator. The divided-power convolution then
recovers twice the second coefficient from the square of the first.

Thus an evaluated six-node word is central in the word image exactly when
its matrix commutes with the twelve signed simple operators. The proof also
works in characteristic three, and needs no finiteness assumption or
semisimple decomposition. These are equations for the scalar-shape argument;
they do not themselves assert that a central word is diagonal.

Sources: the integral Chevalley construction in GLS3 §§1.12.5–6 and 2.6.2,
for the higher subsystem embeddings used in Aschbacher–Smith A.2.17,
printed p.39.
-/

@[expose] public section

noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup
open scoped BigOperators
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

private theorem norm_two_no_triple (i j k : Vec 8)
    (hi : dot i i = 2) (hj : dot j j = 2) (hk : dot k k = 2) :
    k ≠ j + (3 : ℕ) • i := by
  intro h
  have he : dot k k = dot j j + 6 * dot j i + 9 * dot i i := by
    rw [h]
    simp only [dot, Pi.add_apply, nsmul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    change (j a + 3 * i a) * (j a + 3 * i a) =
      j a * j a + 6 * (j a * i a) + 9 * (i a * i a)
    ring
  have hs : dot (j + i) (j + i) = dot j j + 2 * dot j i + dot i i := by
    simp only [dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hn : 0 ≤ dot (j + i) (j + i) :=
    Finset.sum_nonneg fun a _ => mul_self_nonneg _
  linarith

variable {n κ F : Type*} [Fintype n] [DecidableEq n] [Field F]

private theorem odd_two_ne_zero (hodd : Odd (ringChar F)) : (2 : F) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h) with h | h
  · exact CharP.ringChar_ne_one (R := F) h
  · exact hodd.not_two_dvd_nat (by rw [h])

/-- Values at one and minus one recover the first operator in odd characteristic. -/
theorem coefficient_one_of_commute (D : IntegralCubicFamily κ n) (i : κ)
    (h3 : D.dividedPower i 3 = 0) (A : Matrix n n F)
    (hodd : Odd (ringChar F))
    (hp : Commute A (D.curve i (1 : F)))
    (hm : Commute A (D.curve i (-1 : F))) :
    Commute A (D.coefficient i 1) := by
  have hz : D.coefficient (S := F) i 3 = 0 := by
    simp [IntegralCubicFamily.coefficient, h3]
  have he : D.curve i (1 : F) - D.curve i (-1 : F) =
      (2 : F) • D.coefficient i 1 := by
    simp only [IntegralCubicFamily.curve, hz, smul_zero, add_zero,
      one_smul, one_pow, neg_one_sq, neg_smul]
    module
  have hc := hp.sub_right hm
  rw [he] at hc
  change A * D.coefficient i 1 = D.coefficient i 1 * A
  exact (smul_right_injective _ (odd_two_ne_zero hodd)) (by
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hc.eq)


/-- The first operator also determines commutation with the second coefficient. -/
theorem coefficient_two_of_commute_one (D : IntegralCubicFamily κ n) (i : κ)
    (A : Matrix n n F) (hodd : Odd (ringChar F))
    (hc : Commute A (D.coefficient i 1)) : Commute A (D.coefficient i 2) := by
  have he : D.coefficient (S := F) i 1 * D.coefficient i 1 =
      (2 : F) • D.coefficient i 2 := by
    simpa using D.coefficient_mul (S := F) i 1 1
  have h := hc.mul_right hc
  rw [he] at h
  change A * D.coefficient i 2 = D.coefficient i 2 * A
  exact (smul_right_injective _ (odd_two_ne_zero hodd)) (by
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using h.eq)

/-- For a quadratic root curve, its centralizer is the centralizer of its first operator. -/
theorem commute_curve_iff_coefficient (D : IntegralCubicFamily κ n) (i : κ)
    (h3 : D.dividedPower i 3 = 0) (A : Matrix n n F)
    (hodd : Odd (ringChar F)) :
    (∀ t : F, Commute A (D.curve i t)) ↔ Commute A (D.coefficient i 1) := by
  constructor
  · intro h
    exact coefficient_one_of_commute D i h3 A hodd (h 1) (h (-1))
  · intro h t
    have h2 := coefficient_two_of_commute_one D i A hodd h
    have hz : D.coefficient (S := F) i 3 = 0 := by
      simp [IntegralCubicFamily.coefficient, h3]
    simp only [IntegralCubicFamily.curve, hz, smul_zero, add_zero]
    exact ((Commute.one_right A).add_right (h.smul_right t)).add_right
      (h2.smul_right (t ^ 2))

private theorem e7_no_triple (i j k : typeE7Roots) :
    typeE7RootPairing.root k ≠ typeE7RootPairing.root j + 3 • typeE7RootPairing.root i := by
  intro h
  exact norm_two_no_triple i.val j.val k.val (typeE7Root_dot_self i)
    (typeE7Root_dot_self j) (typeE7Root_dot_self k)
    (congrArg (fun x : typeE7Space => x.val) h)

/-- The signed E7 simple curves are quadratic over the integral lattice. -/
theorem e7_simple_third_zero (s : Bool) (i : typeE7RootPairing_base.support) :
    (simpleFamily (b := typeE7RootPairing_base)).dividedPower (s, i) 3 = 0 := by
  have he : eDividedPower (P := typeE7RootPairing) i 3 = 0 := by
    ext (r | r) (c | c) <;> simp only [eDividedPower, Matrix.of_apply, Matrix.zero_apply]
    split_ifs with h
    · exact (e7_no_triple i c r h).elim
    · rfl
  cases s <;> simp [simpleFamily, fDividedPower, he]

/-- The signed E8 simple curves are quadratic over the integral lattice. -/
theorem e8_simple_third_zero (s : Bool) (i : typeE8RootPairing_base.support) :
    (simpleFamily (b := typeE8RootPairing_base)).dividedPower (s, i) 3 = 0 := by
  have he : eDividedPower (P := typeE8RootPairing) i 3 = 0 := by
    ext (r | r) (c | c) <;> simp only [eDividedPower, Matrix.of_apply, Matrix.zero_apply]
    split_ifs with h
    · exact (norm_two_no_triple (i : typeE8Roots).val c.val r.val
        (typeE8Root_dot_self i) (typeE8Root_dot_self c) (typeE8Root_dot_self r) h).elim
    · rfl
  cases s <;> simp [simpleFamily, fDividedPower, he]

open TwistedE6.FoldedSubsystem.HigherRealizations
open TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters

/-- The twelve operator equations detect commutation with the literal word image. -/
theorem commute_eval_iff_operators (D : IntegralCubicFamily κ n)
    (j : Bool → Fin 6 → κ) (h3 : ∀ s i, D.dividedPower (j s i) 3 = 0)
    (v : SixNodeWord F →* (Matrix n n F)ˣ)
    (hv : ∀ s i t, v (FreeGroup.of (s, i, t)) = D.unit (j s i) t)
    (A : (Matrix n n F)ˣ) (hodd : Odd (ringChar F)) :
    (∀ w, Commute A (v w)) ↔ ∀ s i, Commute A.val (D.coefficient (j s i) 1) := by
  constructor
  · intro hc s i
    apply (commute_curve_iff_coefficient D (j s i) (h3 s i) A.val hodd).mp
    intro t
    have h := (hc (FreeGroup.of (s, i, t))).map (Units.coeHom _)
    simpa only [hv, Units.coeHom_apply, IntegralCubicFamily.unit_val] using h
  · intro hc w
    have hs (s : Bool) (i : Fin 6) (t : F) : Commute A (v (FreeGroup.of (s, i, t))) := by
      apply Units.ext
      simpa only [Units.val_mul, hv, IntegralCubicFamily.unit_val] using
        ((commute_curve_iff_coefficient D (j s i) (h3 s i) A.val hodd).mpr (hc s i) t).eq
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of x => obtain ⟨s, i, t⟩ := x; exact hs s i t
    | inv_of x hx => simpa using hx.inv_right
    | mul x y hx hy => simpa using hx.mul_right hy

/-- Centrality of an E7 six-node word is exactly the twelve simple-operator equations. -/
theorem e7Six_central_iff_operators (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) :
    (∀ z, Commute (e7Six F w) (e7Six F z)) ↔
      ∀ s i, Commute (e7Six F w).val.val
        ((simpleFamily (b := typeE7RootPairing_base)).coefficient (s, e7Node i) 1) := by
  let v := (ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F)
  have hv (s : Bool) (i : Fin 6) (t : F) :
      v (FreeGroup.of (s, i, t)) =
        (simpleFamily (b := typeE7RootPairing_base)).unit (s, e7Node i) t := by
    simp [v, e7Simple, e7Node]
  have h := commute_eval_iff_operators (simpleFamily (b := typeE7RootPairing_base))
    (fun s i => (s, e7Node i)) (fun s i => e7_simple_third_zero s (e7Node i))
    v hv (e7Six F w).val hodd
  constructor
  · intro hc
    apply h.mp
    intro z
    exact (hc z).map (Subgroup.subtype _)
  · intro hc z
    apply Subtype.ext
    exact (h.mpr hc z).eq

/-- Centrality of an E8 six-node word is exactly the twelve simple-operator equations. -/
theorem e8Six_central_iff_operators (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) :
    (∀ z, Commute (e8Six F w) (e8Six F z)) ↔
      ∀ s i, Commute (e8Six F w).val.val
        ((simpleFamily (b := typeE8RootPairing_base)).coefficient (s, e8Node i) 1) := by
  let v := (ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F)
  have hv (s : Bool) (i : Fin 6) (t : F) :
      v (FreeGroup.of (s, i, t)) =
        (simpleFamily (b := typeE8RootPairing_base)).unit (s, e8Node i) t := by
    simp [v, e8Simple, e8Node]
  have h := commute_eval_iff_operators (simpleFamily (b := typeE8RootPairing_base))
    (fun s i => (s, e8Node i)) (fun s i => e8_simple_third_zero s (e8Node i))
    v hv (e8Six F w).val hodd
  constructor
  · intro hc
    apply h.mp
    intro z
    exact (hc z).map (Subgroup.subtype _)
  · intro hc z
    apply Subtype.ext
    exact (h.mpr hc z).eq

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
