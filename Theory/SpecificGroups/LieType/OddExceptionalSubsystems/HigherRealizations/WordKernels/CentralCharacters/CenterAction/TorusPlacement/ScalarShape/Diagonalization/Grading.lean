module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Operators

/-!
# Integral complementary gradings for the six-node word images

A linear combination of integral coroot weights which annihilates the six
selected simple roots is preserved by every signed divided power, every curve,
and therefore every evaluated word. This argument takes place over the integers
before specialization and works in all characteristics.

For E7 the coefficients are `(2,4,6,3,5,4,3)`. For E8 use the same coefficients
with a final zero, together with the eighth coroot weight. Their zero values on
the six selected roots are checked on the actual numbered Cartan matrices.
The resulting zero-entry statements retain word membership and prevent mixing
between different integral grades, even when Cartan weights coincide in the
coefficient field. They do not assert diagonality within an individual grade.

Source: the common integral lattice construction for subsystem subgroups in
GLS3 §2.6.2, with the E6 central-torus calculation of §§1.12.5–6, used in
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
attribute [local instance] Classical.decEq

section Matrix
variable {n Γ F : Type*} [Fintype n] [DecidableEq n] [Field F]

omit [DecidableEq n] in
private theorem mul_preserves_grade (g : n → Γ) (A B : Matrix n n F)
    (hA : ∀ r c, g r ≠ g c → A r c = 0)
    (hB : ∀ r c, g r ≠ g c → B r c = 0)
    (r c : n) (h : g r ≠ g c) : (A * B) r c = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : g r = g k
  · rw [hB k c (fun hc => h (hk.trans hc)), mul_zero]
  · rw [hA r k hk, zero_mul]

/-- A grading preserved by all generating curves is preserved by their actual words. -/
theorem eval_preserves_grade {κ : Type*} (D : IntegralCubicFamily κ n)
    (j : Bool → Fin 6 → κ) (v : SixNodeWord F →* (Matrix n n F)ˣ)
    (hv : ∀ s i t, v (FreeGroup.of (s, i, t)) = D.unit (j s i) t)
    (g : n → Γ) (hg : ∀ s i (t : F) r c, g r ≠ g c → D.curve (j s i) t r c = 0)
    (w : SixNodeWord F) (r c : n) (h : g r ≠ g c) : (v w).val r c = 0 := by
  have hall : ∀ r c, g r ≠ g c → (v w).val r c = 0 := by
    induction w using FreeGroup.induction_on with
    | C1 =>
      intro r c h
      have hrc : r ≠ c := fun he => h (congrArg g he)
      simp [hrc]
    | of x =>
      obtain ⟨s,i,t⟩ := x
      simpa only [hv, IntegralCubicFamily.unit_val] using hg s i t
    | inv_of x _ =>
      obtain ⟨s,i,t⟩ := x
      simpa only [map_inv, hv, IntegralCubicFamily.unit_inv,
        IntegralCubicFamily.unit_val] using hg s i (-t)
    | mul x y hx hy =>
      intro r c h
      simpa only [map_mul, Units.val_mul] using
        mul_preserves_grade g _ _ hx hy r c h
  exact hall r c h
end Matrix

section Generic
variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι] [Field F]
  {m : ℕ}

/-- An integral grading on the Chevalley basis, before reduction in the coefficient field. -/
def integralWeightGrade (q : Fin m → ι) (a : Fin m → ℤ) (r : b.support ⊕ ι) : ℤ :=
  ∑ k, a k * chevalleyBasisWeight (P := P) r (q k)

omit [CharZero R] [P.IsReduced] [Fintype ι] [DecidableEq ι] in
private theorem homogeneous_preserves_grade (q : Fin m → ι) (a : Fin m → ℤ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (d : ι → ℤ)
    (hA : IsChevalleyHomogeneous (P := P) A d) (hd : ∑ k, a k * d (q k) = 0)
    (r c : b.support ⊕ ι)
    (h : integralWeightGrade q a r ≠ integralWeightGrade q a c) : A r c = 0 := by
  by_contra hn
  apply h
  apply sub_eq_zero.mp
  calc
    integralWeightGrade q a r - integralWeightGrade q a c =
        ∑ k, a k * (chevalleyBasisWeight (P := P) r (q k) -
          chevalleyBasisWeight (P := P) c (q k)) := by
      simp only [integralWeightGrade, ← Finset.sum_sub_distrib, mul_sub]
    _ = ∑ k, a k * d (q k) := by simp only [hA r c hn]
    _ = 0 := hd

/-- If an integral coroot functional kills a simple root, its whole signed curve
preserves the functional's grading in every characteristic. -/
theorem simpleCurve_preserves_integralWeightGrade (q : Fin m → ι) (a : Fin m → ℤ)
    (i : b.support) (hi : ∑ k, a k * P.pairingIn ℤ i (q k) = 0)
    (s : Bool) (t : F) (r c : b.support ⊕ ι)
    (h : integralWeightGrade q a r ≠ integralWeightGrade q a c) :
    (simpleFamily (b := b)).curve (s, i) t r c = 0 := by
  have hd (n : ℤ) : ∑ k, a k * (n * P.pairingIn ℤ i (q k)) = 0 := by
    calc
      _ = n * ∑ k, a k * P.pairingIn ℤ i (q k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [hi, mul_zero]
  have hc (n : ℕ) : (simpleFamily (b := b)).coefficient (S := F) (s, i) n r c = 0 := by
    have hz : (simpleFamily (b := b)).dividedPower (s, i) n r c = 0 := by
      cases s
      · exact homogeneous_preserves_grade q a _ _
          (fDividedPower_isChevalleyHomogeneous i n) (hd (-n)) r c h
      · exact homogeneous_preserves_grade q a _ _
          (eDividedPower_isChevalleyHomogeneous i n) (hd n) r c h
    simp only [IntegralCubicFamily.coefficient, Matrix.map_apply, hz, map_zero]
  have hrc : r ≠ c := fun he => h (congrArg (integralWeightGrade q a) he)
  simp [IntegralCubicFamily.curve, hc, hrc]

/-- Evaluated six-node words preserve every integral coroot functional annihilating
those six roots. This is a consequence of word membership, independent of centrality. -/
theorem eval_preserves_integralWeightGrade (q : Fin m → ι) (a : Fin m → ℤ)
    (j : Fin 6 → b.support)
    (hj : ∀ i, ∑ k, a k * P.pairingIn ℤ (j i) (q k) = 0)
    (v : SixNodeWord F →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
    (hv : ∀ s i t, v (FreeGroup.of (s, i, t)) = (simpleFamily (b := b)).unit (s, j i) t)
    (w : SixNodeWord F) (r c : b.support ⊕ ι)
    (h : integralWeightGrade q a r ≠ integralWeightGrade q a c) : (v w).val r c = 0 := by
  exact eval_preserves_grade (simpleFamily (b := b)) (fun s i => (s, j i)) v hv
    (integralWeightGrade q a)
    (fun s i t r c h => simpleCurve_preserves_integralWeightGrade q a (j i) (hj i) s t r c h)
    w r c h
end Generic

local instance gradingE7RootsFintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance gradingE8RootsFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- The integral grading transverse to the E6 subsystem in E7. -/
def e7ComplementGrade : typeE7RootPairing_base.support ⊕ typeE7Roots → ℤ :=
  integralWeightGrade (fun k => (typeE7RootPairing_baseEquiv k : typeE7Roots))
    ![2,4,6,3,5,4,3]

/-- Two independent integral gradings transverse to the E6 subsystem in E8. -/
def e8ComplementGrade (r : typeE8RootPairing_base.support ⊕ typeE8Roots) : ℤ × ℤ :=
  (integralWeightGrade (fun k => (typeE8RootPairing_baseEquiv k : typeE8Roots))
      ![2,4,6,3,5,4,3,0] r,
    chevalleyBasisWeight (P := typeE8RootPairing) r (typeE8RootPairing_baseEquiv 7))

/-- Literal E7 words have zero entries between distinct integral grades. -/
theorem e7Six_entry_zero_of_complementGrade (F : Type*) [Field F] (w : SixNodeWord F)
    (r c : typeE7RootPairing_base.support ⊕ typeE7Roots)
    (h : e7ComplementGrade r ≠ e7ComplementGrade c) : (e7Six F w).val.val r c = 0 := by
  apply eval_preserves_integralWeightGrade
    (fun k => (typeE7RootPairing_baseEquiv k : typeE7Roots)) ![2,4,6,3,5,4,3] e7Node _
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F)) _ w r c h
  · intro i
    have hp (k : Fin 7) : typeE7RootPairing.pairingIn ℤ (e7Node i)
        (typeE7RootPairing_baseEquiv k) = typeE7CartanMatrix (i.castLE (by decide)) k :=
      typeE7RootPairing_base_cartan_apply _ _
    simp only [hp]
    fin_cases i <;> decide
  · intro s i t
    simp [e7Simple, e7Node]

/-- Literal E8 words cannot mix equal E6 constituents lying in distinct integral grades. -/
theorem e8Six_entry_zero_of_complementGrade (F : Type*) [Field F] (w : SixNodeWord F)
    (r c : typeE8RootPairing_base.support ⊕ typeE8Roots)
    (h : e8ComplementGrade r ≠ e8ComplementGrade c) : (e8Six F w).val.val r c = 0 := by
  by_cases hfst : (e8ComplementGrade r).1 = (e8ComplementGrade c).1
  · have hsnd : (e8ComplementGrade r).2 ≠ (e8ComplementGrade c).2 := by
      intro he
      exact h (Prod.ext hfst he)
    have heq (a : typeE8RootPairing_base.support ⊕ typeE8Roots) :
        (e8ComplementGrade a).2 = integralWeightGrade
          (fun _ : Fin 1 => (typeE8RootPairing_baseEquiv 7 : typeE8Roots)) (fun _ => 1) a := by
      simp [e8ComplementGrade, integralWeightGrade]
    simp only [heq] at hsnd
    apply eval_preserves_integralWeightGrade _ _ e8Node _
      ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F)) _ w r c hsnd
    · intro i
      have hp (k : Fin 8) : typeE8RootPairing.pairingIn ℤ (e8Node i)
          (typeE8RootPairing_baseEquiv k) = typeE8CartanMatrix (i.castLE (by decide)) k :=
        typeE8RootPairing_base_cartan_apply _ _
      simp only [hp]
      fin_cases i <;> decide
    · intro s i t
      simp [e8Simple, e8Node]
  · apply eval_preserves_integralWeightGrade
      (fun k => (typeE8RootPairing_baseEquiv k : typeE8Roots)) ![2,4,6,3,5,4,3,0] e8Node _
      ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F)) _ w r c hfst
    · intro i
      have hp (k : Fin 8) : typeE8RootPairing.pairingIn ℤ (e8Node i)
          (typeE8RootPairing_baseEquiv k) = typeE8CartanMatrix (i.castLE (by decide)) k :=
        typeE8RootPairing_base_cartan_apply _ _
      simp only [hp]
      fin_cases i <;> decide
    · intro s i t
      simp [e8Simple, e8Node]
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
