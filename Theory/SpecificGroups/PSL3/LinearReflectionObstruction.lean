module
public import Theory.SpecificGroups.PSL3.DiagonalReflectionObstruction
public import Theory.LinearAlgebra.RankOneEigenbasis

/-!
# Odd-prime reflections in covered special-linear overgroups

A rank-one displacement with nontrivial determinant has an actual eigenbasis.
Conjugation by this basis preserves the full SL₃ subgroup and carries the actor
to a diagonal reflection. The three-axis section obstruction then excludes it,
retaining the prime rank on the original covering group. The image version
restricts that same cover to the field-linear image before applying the bound.

Source: Aschbacher--Smith H.4.1, printed p.379, and A.1.31(1), pp.27--28.
-/
public section
open Subgroup Matrix Module
open UnitaryThree.OddTorusNormalizer
namespace Matrix.SL3Reflection
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

/-- The full SL₃ image cannot contain an odd-prime linear reflection when
its original finite cover has p-rank at most two. -/
theorem no_linear_reflection_in_rank_two_section
    (H : Subgroup (GL (Fin 3) F))
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, X.toGL ∈ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (S : H) (ho : orderOf S = p)
    (hr : finrank F (LinearMap.range (Matrix.toLin' S.val.val - LinearMap.id)) = 1)
    (hd : GeneralLinearGroup.det S.val ≠ 1) : False := by
  classical
  let e := (GeneralLinearGroup.toLin S.val).toLinearEquiv
  have he : e.toLinearMap = Matrix.toLin' S.val.val := rfl
  have hde : e.det = GeneralLinearGroup.det S.val := by
    apply Units.ext
    rw [LinearEquiv.coe_det,he,LinearMap.det_toLin']
    rfl
  obtain ⟨b,hb⟩ := e.exists_rank_one_eigenbasis (he ▸ hr) (hde ▸ hd)
  let std := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F :=
    ⟨std.toMatrix b,b.toMatrix std,std.toMatrix_mul_toMatrix_flip b,b.toMatrix_mul_toMatrix_flip std⟩
  let d := diagonalHom ![1,1,GeneralLinearGroup.det S.val]
  have hP : P * d * P⁻¹ = S.val := by
    apply Units.ext
    change std.toMatrix b * d.val * b.toMatrix std = S.val.val
    have hdval : d.val = Matrix.diagonal ![1,1,(e.det : F)] := by
      rw [hde]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [d,diagonalHom]
    rw [hdval,←hb,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,he]
    simp [std,LinearMap.toMatrix_eq_toMatrix']
  let c := (MulAut.conj P⁻¹).toMonoidHom
  let H' := H.map c
  let E := H.equivMapOfInjective c (MulAut.conj P⁻¹).injective
  have hSL' (X : SpecialLinearGroup (Fin 3) F) : X.toGL ∈ H' := by
    let Y := P*X.toGL*P⁻¹
    have hdet : Y.val.det = 1 := by
      have hh : GeneralLinearGroup.det Y = 1 := by simp [Y]
      exact congrArg Units.val hh
    let Y' : SpecialLinearGroup (Fin 3) F := ⟨Y.val,hdet⟩
    have hy : Y'.toGL=Y := Units.ext rfl
    refine ⟨Y,hy ▸ hSL Y',?_⟩
    change P⁻¹*(P*X.toGL*P⁻¹)*(P⁻¹)⁻¹=X.toGL
    simp [mul_assoc]
  have hdH : d ∈ H' := by
    refine ⟨S.val,S.property,?_⟩
    change P⁻¹*S.val*(P⁻¹)⁻¹=d
    rw [←hP]
    simp [mul_assoc]
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let t := permutationGL (E := F) τ
  have htH : t ∈ H' := by
    have ht : t.val.det=1 := by
      change ((τ⁻¹).permMatrix F).det=1
      rw [Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;>
        simp [h,CharTwo.neg_eq]
    let t' : SpecialLinearGroup (Fin 3) F := ⟨t.val,ht⟩
    have he : t'.toGL=t := Units.ext rfl
    exact he ▸ hSL' t'
  have hswap : t*d*t⁻¹=diagonalHom ![GeneralLinearGroup.det S.val,1,1] := by
    apply Units.ext
    change (permutationGL τ).val *
      (diagonalHom ![1,1,GeneralLinearGroup.det S.val]).val *
      ((permutationGL τ)⁻¹).val = _
    rw [←map_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [permutationGL_apply,diagonalHom,Matrix.mul_apply,Fin.sum_univ_three,τ,Equiv.swap_apply_def]
  have hlam : orderOf (GeneralLinearGroup.det S.val)=p := by
    have hdiv : orderOf (GeneralLinearGroup.det S.val) ∣ p := by
      rw [←ho]
      exact orderOf_map_dvd (GeneralLinearGroup.det.comp H.subtype) S
    exact ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv).resolve_left
      (fun h => hd (orderOf_eq_one_iff.mp h))
  exact no_diagonal_reflection_in_rank_two_section H' hSL' hp
    (E.toMonoidHom.comp f) (E.surjective.comp hf) hrank
    (GeneralLinearGroup.det S.val) hlam
    (hswap ▸ H'.mul_mem (H'.mul_mem htH hdH) (H'.inv_mem htH))

/-- Restrict the original cover to its field-linear image; quotient prime rank
is not assumed to be monotone. -/
theorem no_linear_reflection_in_injective_image
    {B : Type*} [Group B]
    (r : GL (Fin 3) F →* B) (hinj : Function.Injective r)
    (f : K →* B) (hrank : primeRank p K ≤ 2) (hp : Odd p)
    (hSL : ∀ X : SpecialLinearGroup (Fin 3) F, r X.toGL ∈ f.range)
    (S : GL (Fin 3) F) (hS : r S ∈ f.range) (ho : orderOf S = p)
    (hr : finrank F (LinearMap.range (Matrix.toLin' S.val - LinearMap.id)) = 1)
    (hd : GeneralLinearGroup.det S ≠ 1) : False := by
  let P := r.range.comap f
  let e := MonoidHom.ofInjective hinj
  let g : P →* GL (Fin 3) F := e.symm.toMonoidHom.comp (f.subgroupComap r.range)
  have hpre (A : GL (Fin 3) F) (hA : r A ∈ f.range) : A ∈ g.range := by
    obtain ⟨k,hk⟩ := hA
    have hkP : k ∈ P := ⟨A,hk.symm⟩
    refine ⟨⟨k,hkP⟩,?_⟩
    apply hinj
    change (e (e.symm ⟨f k,hkP⟩)).val = r A
    rw [e.apply_symm_apply]
    exact hk
  let S' : g.range := ⟨S,hpre S hS⟩
  have horder : orderOf S'=p :=
    (orderOf_injective g.range.subtype g.range.subtype_injective S').symm.trans ho
  exact no_linear_reflection_in_rank_two_section g.range
    (fun X => hpre X.toGL (hSL X)) hp g.rangeRestrict g.rangeRestrict_surjective
    ((primeRank_subgroup_le p P).trans hrank) S' horder hr hd
end Matrix.SL3Reflection
