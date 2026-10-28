module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ThreeAxes
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.Permutations

/-!
# Diagonal unitary reflections in rank-two sections

A norm-one reflection and the literal special unitary group generate all three
independent prime-order diagonal axes. A coordinate swap is special unitary in
characteristic two. Applying the section-centralizer obstruction to the actual
surjective cover excludes the reflection, including the cubic-center case.

Source: Aschbacher--Smith H.2, printed p.378, applying A.1.31(1).
-/
public section
open Subgroup
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open UnitaryThree.OddTorusNormalizer
namespace UnitaryThree
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

/-- A diagonal unitary reflection cannot occur in a rank-two section
containing the literal special unitary group. -/
theorem no_diagonal_reflection_in_rank_two_section
    (J : HermitianForm 3 F) (H : Subgroup (GL (Fin 3) F))
    (hSU : (identityGram J).specialSubgroup ≤ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (lam : Fˣ) (hlam : orderOf lam = p) (hn : lam ∈ normOne J)
    (hR : diagonalHom ![lam,1,1] ∈ H) : False := by
  let C := zpowers lam
  have hc : Nat.card C = p := by rw [Nat.card_zpowers,hlam]
  have hCn : C ≤ normOne J := zpowers_le.mpr hn
  let first : Fˣ →* (Fin 3 → Fˣ) :=
    { toFun := fun x => ![x,1,1]
      map_one' := by ext i; fin_cases i <;> rfl
      map_mul' := fun x y => by ext i; fin_cases i <;> simp }
  have hfirst (x : C) : diagonalHom (first x.val) ∈ H := by
    have hh : (diagonalHom.comp first) lam ∈ H := hR
    have hle := map_le_iff_le_comap.mpr (zpowers_le.mpr hh)
    exact hle ⟨x.val,x.property,rfl⟩
  have hall (a : Fin 3 → C) : diagonalHom (fun i => (a i).val) ∈ H := by
    let u : C := ∏ i, a i
    let b : Fin 3 → Fˣ := ![((a 1).val * (a 2).val)⁻¹, (a 1).val, (a 2).val]
    have hb : diagonalHom b ∈ (identityGram J).specialSubgroup := by
      apply (diagonal_mem_identity_special_iff J b).mpr
      constructor
      · intro i
        fin_cases i
        · exact (normOne J).inv_mem ((normOne J).mul_mem (hCn (a 1).property) (hCn (a 2).property))
        · exact hCn (a 1).property
        · exact hCn (a 2).property
      · simp [b,Fin.prod_univ_three,mul_assoc]
    have he : (fun i => (a i).val) = first u.val * b := by
      ext i
      fin_cases i <;> simp [first,b,u,Fin.prod_univ_three,mul_assoc,mul_comm,mul_left_comm]
    rw [he,map_mul]
    exact H.mul_mem (hfirst u) (hSU hb)
  let inc : (Fin 3 → C) →* (Fin 3 → Fˣ) :=
    { toFun := fun a i => (a i).val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j : (Fin 3 → C) →* H :=
    (diagonalHom.comp inc).codRestrict H hall
  have hj : Function.Injective j := by
    intro a b h
    have hh := diagonalHom_injective (congrArg Subtype.val h)
    funext i
    exact Subtype.ext (congrFun hh i)
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let t : H := ⟨permutationGL τ, hSU (permutationGL_special J τ)⟩
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      change permutationGL τ ^ 2 = 1
      rw [←map_pow]
      have he : τ ^ 2 = 1 := by simp [τ,pow_two]
      rw [he,map_one]
    · intro he
      have hh := congrArg (fun x : H => x.val.val 0 0) he
      simp [t,permutationGL_apply,τ] at hh
  have hswap (a : Fin 3 → C) :
      t * j a * t⁻¹ = j (a ∘ Equiv.swap (0 : Fin 3) 1) := by
    apply Subtype.ext
    apply Units.ext
    change (permutationGL τ).val * (diagonalHom (fun i => (a i).val)).val *
      ((permutationGL τ)⁻¹).val = (diagonalHom (fun i => (a (τ i)).val)).val
    rw [←map_inv]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [permutationGL_apply,τ,diagonalHom,Matrix.mul_apply,Fin.sum_univ_three,
        Equiv.swap_apply_def]
  exact Theory.GroupTheory.no_three_axes_swapped_in_rank_two_section
    hp f hf hrank hc j hj t ht hswap
end UnitaryThree
