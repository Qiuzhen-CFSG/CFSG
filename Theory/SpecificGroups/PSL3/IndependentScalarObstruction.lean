module
public import Theory.SpecificGroups.PSL3.DiagonalReflectionObstruction

/-!
# An independent scalar on a second SL₃ summand

The diagonal torus on the faithful first three-space and an independent
scalar on a second three-space form three prime axes. A coordinate swap
interchanges the torus axes and fixes the scalar. The section-centralizer
obstruction applies to the actual cover, including when the prime divides
the center of SL₃. No prime-rank estimate on a quotient is used.

This supplies the zero-displacement-on-one-summand case of the doubled
natural H.4.1 argument. The second representation may be the contragredient.
-/
public section
open Subgroup Matrix
open UnitaryThree.OddTorusNormalizer
namespace Matrix.SL3Reflection
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

/-- A covered paired SL₃ overgroup cannot contain a nontrivial odd-prime
scalar acting only on its second summand. -/
theorem no_independent_scalar_in_rank_two_section
    (ρ : SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F)
    (H : Subgroup (GL (Fin 3) F × GL (Fin 3) F))
    (hSL : ∀ S : SpecialLinearGroup (Fin 3) F, (S.toGL,ρ S) ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (lam : Fˣ) (hlam : orderOf lam = p)
    (hR : (1,GeneralLinearGroup.scalar (Fin 3) lam) ∈ H) : False := by
  let C := zpowers lam
  have hc : Nat.card C = p := by rw [Nat.card_zpowers,hlam]
  let d : (Fin 3 → C) →* (Fin 3 → Fˣ) :=
    { toFun := fun a => ![(a 0).val,(a 1).val,((a 0).val*(a 1).val)⁻¹]
      map_one' := by ext i; fin_cases i <;> simp
      map_mul' := fun a b => by
        ext i
        fin_cases i <;> simp [mul_assoc,mul_comm,mul_left_comm] }
  let D : (Fin 3 → C) →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun a => ⟨(diagonalHom (d a)).val,by
        simp [diagonalHom,d,Matrix.det_diagonal,Fin.prod_univ_three,mul_assoc]⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change (diagonalHom (d (a*b))).val =
          (diagonalHom (d a)).val*(diagonalHom (d b)).val
        simp }
  have hDtoGL (a : Fin 3 → C) : (D a).toGL = diagonalHom (d a) := Units.ext rfl
  let scalar : Fˣ →* GL (Fin 3) F × GL (Fin 3) F :=
    (1 : Fˣ →* GL (Fin 3) F).prod (GeneralLinearGroup.scalar (Fin 3))
  have hscalar (c : C) : scalar c.val ∈ H := by
    have hle := map_le_iff_le_comap.mpr (zpowers_le.mpr (show scalar lam ∈ H from hR))
    exact hle ⟨c.val,c.property,rfl⟩
  let j₀ : (Fin 3 → C) →* GL (Fin 3) F × GL (Fin 3) F :=
    { toFun := fun a => ((D a).toGL,ρ (D a)*GeneralLinearGroup.scalar (Fin 3) (a 2).val)
      map_one' := by simp
      map_mul' := fun a b => by
        apply Prod.ext
        · simp
        · change ρ (D (a*b))*GeneralLinearGroup.scalar (Fin 3) ((a 2).val*(b 2).val) = _
          simp only [map_mul,Prod.mk_mul_mk]
          calc
            _ = ρ (D a)*(ρ (D b)*GeneralLinearGroup.scalar (Fin 3) (a 2).val)*
                GeneralLinearGroup.scalar (Fin 3) (b 2).val := by simp only [mul_assoc]
            _ = ρ (D a)*(GeneralLinearGroup.scalar (Fin 3) (a 2).val*ρ (D b))*
                GeneralLinearGroup.scalar (Fin 3) (b 2).val := by
              rw [GeneralLinearGroup.scalar_commute]
            _ = _ := by simp only [mul_assoc] }
  have hjH (a : Fin 3 → C) : j₀ a ∈ H := by
    change ((D a).toGL,ρ (D a)*GeneralLinearGroup.scalar (Fin 3) (a 2).val) ∈ H
    simpa only [scalar,MonoidHom.prod_apply,MonoidHom.one_apply,Prod.mk_mul_mk,mul_one]
      using H.mul_mem (hSL (D a)) (hscalar (a 2))
  let j := j₀.codRestrict H hjH
  have hj : Function.Injective j := by
    intro a b he
    have hfirst := congrArg (fun x : H => x.val.1) he
    change (D a).toGL = (D b).toGL at hfirst
    rw [hDtoGL,hDtoGL] at hfirst
    have hdiag := diagonalHom_injective hfirst
    have h0 : a 0=b 0 := Subtype.ext (congrFun hdiag 0)
    have h1 : a 1=b 1 := Subtype.ext (congrFun hdiag 1)
    have hD : D a=D b := by
      apply Subtype.ext
      exact congrArg Units.val hfirst
    have hsecond := congrArg (fun x : H => x.val.2) he
    change ρ (D a)*GeneralLinearGroup.scalar (Fin 3) (a 2).val =
      ρ (D b)*GeneralLinearGroup.scalar (Fin 3) (b 2).val at hsecond
    rw [hD] at hsecond
    have hscalarEq := mul_left_cancel hsecond
    have h2 : a 2=b 2 := by
      apply Subtype.ext
      apply Units.ext
      exact congrArg (fun x : GL (Fin 3) F => x.val 0 0) hscalarEq
    funext i
    fin_cases i <;> assumption
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have htDet : (permutationGL (E := F) τ).val.det = 1 := by
    change ((τ⁻¹).permMatrix F).det = 1
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;>
      simp [h,CharTwo.neg_eq]
  let T : SpecialLinearGroup (Fin 3) F := ⟨(permutationGL τ).val,htDet⟩
  have hT : T.toGL=permutationGL τ := Units.ext rfl
  have hTsq : T^2=1 := by
    apply Subtype.ext
    change (permutationGL τ).val^2=1
    have hh : permutationGL (E := F) τ^2=1 := by
      rw [←map_pow]
      have he : τ^2=1 := by simp [τ,pow_two]
      rw [he,map_one]
    exact congrArg Units.val hh
  let t : H := ⟨(T.toGL,ρ T),hSL T⟩
  have ht : orderOf t=2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      apply Prod.ext
      · change T.toGL^2=1
        rw [←map_pow,hTsq,map_one]
      · change ρ T^2=1
        rw [←map_pow,hTsq,map_one]
    · intro he
      have hh := congrArg (fun x : H => x.val.1.val 0 0) he
      simp [t,hT,permutationGL_apply,τ] at hh
  have hswapD (a : Fin 3 → C) : T*D a*T⁻¹=D (a ∘ τ) := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul,map_mul,map_inv,hT,hDtoGL,hDtoGL]
    apply Units.ext
    change (permutationGL τ).val * (diagonalHom (d a)).val *
      ((permutationGL τ)⁻¹).val = (diagonalHom (d (a ∘ τ))).val
    rw [←map_inv]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [permutationGL_apply,τ,diagonalHom,d,Matrix.mul_apply,Fin.sum_univ_three,
        Equiv.swap_apply_def]
    ring
  have hswap (a : Fin 3 → C) : t*j a*t⁻¹=j (a ∘ Equiv.swap (0 : Fin 3) 1) := by
    apply Subtype.ext
    apply Prod.ext
    · change T.toGL*(D a).toGL*T.toGL⁻¹=(D (a ∘ τ)).toGL
      rw [←map_inv,←map_mul,←map_mul,hswapD]
    · change ρ T*(ρ (D a)*GeneralLinearGroup.scalar (Fin 3) (a 2).val)*(ρ T)⁻¹ =
        ρ (D (a ∘ τ))*GeneralLinearGroup.scalar (Fin 3) (a (τ 2)).val
      have htwo : τ 2=2 := by decide
      rw [htwo,←hswapD,map_mul,map_mul,map_inv]
      calc
        _ = ρ T*ρ (D a)*(GeneralLinearGroup.scalar (Fin 3) (a 2).val*(ρ T)⁻¹) :=
          by simp only [mul_assoc]
        _ = _ := by rw [GeneralLinearGroup.scalar_commute]; simp only [mul_assoc]
  exact Theory.GroupTheory.no_three_axes_swapped_in_rank_two_section
    hp f hf hrank hc j hj t ht hswap

end Matrix.SL3Reflection
