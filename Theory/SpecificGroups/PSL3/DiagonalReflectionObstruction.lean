module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ThreeAxes
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.Permutations

/-!
# Linear reflections excluded by the original covering rank

The full special linear group and one diagonal odd-prime reflection generate
three independent prime axes. A coordinate swap is special linear in
characteristic two. The genuine section-centralizer theorem contradicts the
rank-two bound on the source of the surjection. The rank is retained on the
cover and is never transferred to an arbitrary quotient.

Source: Aschbacher--Smith H.4.1 and A.1.31(1), printed pp.379 and27--28.
-/
public section
open Subgroup
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open UnitaryThree.OddTorusNormalizer
namespace Matrix.SL3Reflection
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

/-- A diagonal odd-prime reflection cannot lie in a covered SL₃ overgroup
whose original covering group has p-rank at most two. -/
theorem no_diagonal_reflection_in_rank_two_section
    (H : Subgroup (GL (Fin 3) F))
    (hSL : ∀ S : SpecialLinearGroup (Fin 3) F, S.toGL ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (lam : Fˣ) (hlam : orderOf lam = p)
    (hR : diagonalHom ![lam,1,1] ∈ H) : False := by
  let C := zpowers lam
  have hc : Nat.card C = p := by rw [Nat.card_zpowers,hlam]
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
    have hbdet : (diagonalHom b).val.det = 1 := by
      simp [diagonalHom,Matrix.det_diagonal,b,Fin.prod_univ_three]
    have hb : diagonalHom b ∈ H := by
      let S : SpecialLinearGroup (Fin 3) F := ⟨(diagonalHom b).val,hbdet⟩
      have he : S.toGL = diagonalHom b := Units.ext rfl
      exact he ▸ hSL S
    have he : (fun i => (a i).val) = first u.val * b := by
      ext i
      fin_cases i <;> simp [first,b,u,Fin.prod_univ_three,mul_assoc,mul_comm,mul_left_comm]
    rw [he,map_mul]
    exact H.mul_mem (hfirst u) hb
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
  have htH : permutationGL (E := F) τ ∈ H := by
    have hd : (permutationGL (E := F) τ).val.det = 1 := by
      change ((τ⁻¹).permMatrix F).det = 1
      rw [Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;>
        simp [h,CharTwo.neg_eq]
    let S : SpecialLinearGroup (Fin 3) F := ⟨(permutationGL (E := F) τ).val,hd⟩
    have he : S.toGL = permutationGL (E := F) τ := Units.ext rfl
    exact he ▸ hSL S
  let t : H := ⟨permutationGL τ,htH⟩
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
end Matrix.SL3Reflection
