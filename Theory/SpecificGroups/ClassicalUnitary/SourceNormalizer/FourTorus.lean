module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourFixed

/-!
# A split torus detecting two-elements in the unitary-four group

The fixed-field diagonal torus has four distinct characters a,b,b⁻¹,a⁻¹
when the fixed field has more than two elements. Commuting with the torus
forces a unitary matrix to be diagonal. In characteristic two such a
matrix has no nonidentity element of two-power order. The torus lies in
the original flag Borel, including at fixed-field order four.

This is the native calculation used by the Hall/Frattini proof of the
splitting clause of Aschbacher–Smith F.4.29(2), printed p.289 of
`refs/quasithin.pdf`.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourTorus
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "U" => SU F (form F σ hσ)

def diagonalEntries (a b : Kˣ) : Fin 4 → F :=
  ![(a:K),(b:K),((b⁻¹:Kˣ):K),((a⁻¹:Kˣ):K)]

/-- The existing split torus, viewed in the same special unitary carrier. -/
abbrev torusElement (a b : Kˣ) : U :=
  (SmallCompletion.FourFixed.torus F σ hσ a b).val

omit [CharP F 2] in
theorem torusElement_matrix (a b : Kˣ) :
    (torusElement F σ hσ a b).val.val = Matrix.diagonal (diagonalEntries F σ a b) :=
  SmallCompletion.FourFixed.torus_val F σ hσ a b

def torusHom : (Kˣ × Kˣ) →* U where
  toFun x := torusElement F σ hσ x.1 x.2
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [torusElement_matrix,diagonalEntries]
    ext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

omit [CharP F 2] in
theorem torusElement_mem_borel (a b : Kˣ) :
    torusElement F σ hσ a b ∈ borelSU F (form F σ hσ) :=
  (SmallCompletion.FourFixed.torus F σ hσ a b).property

private theorem separating_unit (hq : 2 < Nat.card K) :
    ∃ a : Kˣ, ((a:K):F) ≠ 1 ∧ ((a:K):F) ≠ (((a:K):F)⁻¹) := by
  have hcard : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a,ha⟩ := exists_ne (1:Kˣ)
  have ha1 : ((a:K):F) ≠ 1 := fun h => ha (Units.ext (Subtype.ext h))
  refine ⟨a,ha1,?_⟩
  intro he
  apply ha1
  apply CharTwo.sq_injective
  calc
    ((a:K):F)^2 = ((a:K):F) * (((a:K):F)⁻¹) := by
      rw [pow_two]
      exact congrArg (fun x : F => ((a:K):F)*x) he
    _ = (1:F)^2 := by simp

theorem diagonal_of_commute_torus (hq : 2 < Nat.card K) (g : U)
    (hg : ∀ a b : Kˣ, Commute g (torusElement F σ hσ a b)) :
    g.val.val = Matrix.diagonal (fun i => g.val.val i i) := by
  let A := g.val.val
  have he (a b : Kˣ) : A * Matrix.diagonal (diagonalEntries F σ a b) =
      Matrix.diagonal (diagonalEntries F σ a b) * A :=
    congrArg (fun g : U => g.val.val) (hg a b).eq
  obtain ⟨a,ha1,hai⟩ := separating_unit F σ hq
  have hentry (x y : Kˣ) (i j : Fin 4) :
      ((diagonalEntries F σ x y i) - (diagonalEntries F σ x y j)) * A i j=0 := by
    have hh := congrArg (fun B : Matrix (Fin 4) (Fin 4) F => B i j) (he x y)
    simp only [diagonal_mul,mul_diagonal] at hh
    linear_combination -hh
  have h1 := hentry a 1
  have h2 := hentry 1 a
  ext i j
  by_cases hij : i=j
  · subst j; simp
  · rw [diagonal_apply_ne _ hij]
    change A i j=0
    have h1' := h1 i j
    have h2' := h2 i j
    clear hg he hentry h1 h2
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | simp [diagonalEntries,ha1,ha1.symm,hai,hai.symm,sub_eq_zero,mul_eq_zero] at h1' h2'
        assumption

omit [Finite F] in
private theorem eq_one_of_two_power (x : F) (k : ℕ) (hx : x^(2^k)=1) : x=1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    apply CharTwo.sq_injective
    rw [pow_succ,pow_mul] at hx
    simpa only [one_pow] using hx

theorem two_element_centralizer (hq : 2 < Nat.card K)
    (g : U) (k : ℕ) (hg : g^(2^k)=1)
    (ht : ∀ a b : Kˣ, Commute g (torusElement F σ hσ a b)) : g=1 := by
  have hd := diagonal_of_commute_torus F σ hσ hq g ht
  have hpow := congrArg (fun g : U => g.val.val) hg
  change g.val.val^(2^k)=1 at hpow
  rw [hd,Matrix.diagonal_pow] at hpow
  have hi (i : Fin 4) : g.val.val i i=1 := by
    apply eq_one_of_two_power F _ k
    have hh := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A i i) hpow
    simpa using hh
  apply Subtype.ext
  apply Units.ext
  change g.val.val=1
  rw [hd]
  ext i j
  by_cases hij : i=j
  · subst j; simpa using hi i
  · simp [hij]
end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourTorus
