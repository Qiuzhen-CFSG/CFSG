module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveFixed
public import Theory.GroupTheory.CentralCoprimeCardLift

/-!
# A split torus with no nontrivial centralizing two-elements in PSU₅(4)

The fixed-field torus has the five distinct characters a, b, 1, a⁻¹, b⁻¹
in the native flag basis. A matrix commuting with it is diagonal. Its
only two-power torsion element is the identity in characteristic two.
Unique coprime torsion lifting through the scalar kernel of order five
proves the same assertion in the actual projective carrier. The torus
preserves both native parabolics and has an odd parameter group of order nine.

This supplies the local trivial-intersection calculation for the Hall/Frattini
proof of F.4.29(2), Aschbacher–Smith, printed p.289 of refs/quasithin.pdf.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open Theory.SpecificGroups.UnitaryFive.SmallCompletion FivePaths FiveFixed

@[expose] public noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.SourceTorus
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
local notation "K" => FixedBy.subfield F J.conj

private theorem separating_unit [Finite F] (hq : 2 < Nat.card K) :
    ∃ a : Kˣ, ((a : K) : F) ≠ 1 ∧ ((a : K) : F) ≠ ((a⁻¹ : Kˣ) : K) := by
  have hcard : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a,ha⟩ := exists_ne (1 : Kˣ)
  have ha1 : ((a : K) : F) ≠ 1 := fun h => ha (Units.ext (Subtype.ext h))
  refine ⟨a,ha1,?_⟩
  intro h
  apply ha1
  apply CharTwo.sq_injective
  calc
    ((a : K) : F)^2 = ((a : K) : F)*((a⁻¹ : Kˣ) : K) := by rw [pow_two,h]
    _ = (1 : F)^2 := by simp

theorem coordinates_diagonal_of_commute_torus [Finite F] (hq : 2 < Nat.card K)
    (g : J.specialSubgroup)
    (hg : ∀ a b : Kˣ, Commute g (torus J c hc hJ a b)) :
    (coordinates J c g).val = diagonal (fun i => (coordinates J c g).val i i) := by
  let A := (coordinates J c g).val
  have he (a b : Kˣ) :
      A * (torusDiagonal J a b).val = (torusDiagonal J a b).val * A := by
    have hh := congrArg (fun g : J.specialSubgroup => (coordinates J c g).val) (hg a b).eq
    simpa only [map_mul, Units.val_mul, torus_coordinates] using hh
  obtain ⟨a,ha1,hai⟩ := separating_unit J hq
  have haiF : ((a : K) : F) ≠ (((a : K) : F)⁻¹) := by simpa using hai
  have hentry (x y : Kˣ) (i j : Fin 5) :
      (((torusDiagonal J x y).val i i) - ((torusDiagonal J x y).val j j)) * A i j = 0 := by
    have hh := congrArg (fun B : Matrix (Fin 5) (Fin 5) F => B i j) (he x y)
    simp only [torusDiagonal, diagonal_mul, mul_diagonal, diagonal_apply_eq] at hh ⊢
    linear_combination -hh
  have h1 := hentry a 1
  have h2 := hentry 1 a
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · rw [diagonal_apply_ne _ hij]
    change A i j = 0
    have h1' := h1 i j
    have h2' := h2 i j
    clear hg he hentry h1 h2
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | simp [torusDiagonal,ha1,ha1.symm,haiF,haiF.symm,
          sub_eq_zero,mul_eq_zero] at h1' h2'
        assumption

/-- The split torus uses the fixed field and the native flag basis. -/
def torusHom : (Kˣ × Kˣ) →* J.specialSubgroup where
  toFun x := torus J c hc hJ x.1 x.2
  map_one' := by
    apply coordinates_injective J c
    rw [torus_coordinates,map_one]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusDiagonal]
  map_mul' x y := by
    apply coordinates_injective J c
    rw [map_mul,torus_coordinates,torus_coordinates,torus_coordinates]
    apply Units.ext
    simp only [torusDiagonal,Units.val_mul,diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [_root_.mul_inv_rev,mul_comm]

private theorem eq_one_of_two_power (x : F) (k : ℕ) (hx : x^(2^k)=1) : x=1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    apply CharTwo.sq_injective
    rw [pow_succ, pow_mul] at hx
    simpa only [one_pow] using hx

/-- No nonidentity two-element centralizes the entire split torus. -/
theorem projective_two_element_centralizer [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) (k : ℕ) (hg : g^(2^k)=1)
    (ht : ∀ a b : Kˣ, Commute g (project J (torus J c hc hJ a b))) : g=1 := by
  have hcop : (Nat.card (project J).ker).Coprime (2^k) := by
    rw [card_project_kernel J hconj hcard]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  obtain ⟨u,hu,hup⟩ := (project J).exists_pow_eq_one_lift_of_central_coprime_ker
    (project_surjective J) (project_kernel_le_center J) hcop g hg
  have hut (a b : Kˣ) : Commute u (torus J c hc hJ a b) :=
    (project J).commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
      (project_kernel_le_center J) hcop hup (hu.symm ▸ ht a b)
  have hq : 2 < Nat.card K := by
    change 2 < Nat.card {x : F // J.conj x=x}
    rw [fixed_card_four J hcard hconj]
    decide
  have hd := coordinates_diagonal_of_commute_torus J c hc hJ hq u hut
  have hpow := congrArg (fun g : J.specialSubgroup => (coordinates J c g).val) hup
  simp only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] at hpow
  rw [hd,diagonal_pow] at hpow
  have hi (i : Fin 5) : (coordinates J c u).val i i=1 := by
    apply eq_one_of_two_power _ k
    have hh := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A i i) hpow
    simpa using hh
  have hu1 : u=1 := by
    apply coordinates_injective J c
    rw [map_one]
    apply Units.ext
    rw [hd]
    ext i j
    by_cases hij : i=j
    · subst j; simpa using hi i
    · simp [hij]
  rw [←hu,hu1,map_one]

/-- The split torus in the literal projective flag overlap. -/
def flagTorus [Finite F] : (Kˣ × Kˣ) →*
    (lineParabolic J ⊓ planeParabolic J : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  ((project J).comp (torusHom J c hc hJ)).codRestrict _ (by
    intro x
    have hx := torus_mem J c hc hJ x.1 x.2
    exact ⟨⟨_,hx.1,rfl⟩,⟨_,hx.2,rfl⟩⟩)

omit [CharP F 2] in
/-- Its parameter group has odd order nine. -/
theorem torus_parameter_card [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16) :
    Nat.card (Kˣ × Kˣ)=9 := by
  rw [Nat.card_prod,Nat.card_units]
  have hk : Nat.card K=4 := fixed_card_four J hcard hconj
  rw [hk]

end Theory.SpecificGroups.UnitaryFive.SourceTorus
