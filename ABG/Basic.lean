module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.GaloisField
public import Stellmacher.MainDefs
public import Theory.Mathieu.M11.Basic

/-!
# Models and characteristic parameters for the ABG theorems

Chapter I, article pages 2–3 of Alperin–Brauer–Gorenstein,
`refs/latex/alperin-brauer-gorenstein.tex`, introduces quasi-dihedral Sylow
2-subgroups and the characteristic parameters of an involution centralizer.
This module gives the shared definitions for the three main theorems and their
prerequisites. Quasi-dihedral groups use the existing semidihedral presentation
of order at least 16, whose exponent parameter is one larger than the paper's.

The linear and unitary models use finite fields. The standard unitary form has
identity Gram matrix and conjugation by the q-power Frobenius; involutivity
follows from the finite-field cardinality and power identities. Centralizer
parameters retain the prime power q and the odd central kernel order d without
choosing a preferred involution or a preferred field presentation. Their
independence of the involution is a theorem to be established, not an assumption
of these definitions. Exposed definition bodies form the intentional shared
boundary for source-oriented proof modules.
-/

open BenderSuzuki.MatrixGroups

noncomputable section

namespace ABG

universe u v

/-- The standard Hermitian form over `GF(p^(2n))`, with Frobenius conjugation
`a ↦ a^(p^n)`. Its involutivity follows from the finite-field cardinality formula
and `a^|F| = a`; the Gram matrix is the identity. -/
@[expose] public def unitaryForm (m p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    HermitianForm m (GaloisField p (2 * n)) where
  conj := iterateFrobeniusEquiv (GaloisField p (2 * n)) p n
  conj_involutive := by
    intro x
    simp only [iterateFrobeniusEquiv_def, ← pow_mul, ← pow_add]
    have hcard := GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn)
    let := Fintype.ofFinite (GaloisField p (2 * n))
    have hpow := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hcard] at hpow
    simpa only [two_mul] using hpow
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]
  form_nondegenerate := by simp

/-- A Sylow `2`-subgroup is quasi-dihedral (semidihedral), of order at least 16.
Existence suffices because all Sylow `2`-subgroups are conjugate. -/
@[expose] public def HasQuasiDihedralSylowTwoSubgroups (G : Type u) [Group G] : Prop :=
  ∃ S : Sylow 2 G, Stellmacher.IsSemidihedralGroup S

/-- `GL(2, p^n)`. -/
public abbrev GL2 (p n : ℕ) [Fact p.Prime] := GL (Fin 2) (GaloisField p n)

/-- `GU(2, p^n)`, the full isometry group of the standard Hermitian form. -/
public abbrev GU2 (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :=
  (unitaryForm 2 p n hn).unitarySubgroup

/-- `L₃(p^n) = PSL(3, p^n)`. -/
public abbrev PSL3 (p n : ℕ) [Fact p.Prime] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p n)

/-- `U₃(p^n) = PSU(3, p^n)`, the image of the special unitary group in `PGL`. -/
public abbrev PSU3 (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :=
  ProjectiveSpecialUnitaryMatrixGroup (unitaryForm 3 p n hn)

/-- `H` is isomorphic to `K/Z`, where `Z` is central of odd order `d`.
Normality is recorded explicitly to form the quotient group in Lean. -/
@[expose] public def IsCentralOddQuotient
    (H : Type u) [Group H] (K : Type v) [Group K] (d : ℕ) : Prop :=
  ∃ Z : Subgroup K, ∃ _ : Z.Normal,
    Z ≤ Subgroup.center K ∧ Odd (Nat.card Z) ∧ Nat.card Z = d ∧
      Nonempty (H ≃* K ⧸ Z)

/-- The centralizer description in the First Main Theorem, with the prime
power `q` and central kernel order `d` retained. The involution hypothesis on
`x` is supplied by the theorem or by `HasCharacteristicParameters`. -/
@[expose] public def InvolutionCentralizerParameters
    {G : Type u} [Group G] (x : G) (q d : ℕ) : Prop :=
  ∃ (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0),
    letI : Fact p.Prime := ⟨hp⟩
    q = p ^ n ∧
      ((q % 4 = 3 ∧
          IsCentralOddQuotient (Subgroup.centralizer ({x} : Set G)) (GL2 p n) d) ∨
        (q % 4 = 1 ∧
          IsCentralOddQuotient (Subgroup.centralizer ({x} : Set G)) (GU2 p n hn) d))

/-- The characteristic power `q` and kernel order `d` obtained from an
involution centralizer. In the simple quasi-dihedral setting the paper observes
that these parameters are independent of the involution. -/
@[expose] public def HasCharacteristicParameters
    (G : Type u) [Group G] (q d : ℕ) : Prop :=
  ∃ x : G, orderOf x = 2 ∧ InvolutionCentralizerParameters x q d

/-- The characteristic power, with the central kernel order left unspecified. -/
@[expose] public def HasCharacteristicPower (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ d : ℕ, HasCharacteristicParameters G q d

/-- Isomorphism with `PSL(3,q)` for a prime power `q`. -/
@[expose] public def IsPSL3 (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (p n : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    n ≠ 0 ∧ q = p ^ n ∧ Nonempty (G ≃* PSL3 p n)

/-- Isomorphism with `PSU(3,q)` for a prime power `q`. -/
@[expose] public def IsPSU3 (G : Type u) [Group G] (q : ℕ) : Prop :=
  ∃ (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0),
    letI : Fact p.Prime := ⟨hp⟩
    q = p ^ n ∧ Nonempty (G ≃* PSU3 p n hn)

end ABG
