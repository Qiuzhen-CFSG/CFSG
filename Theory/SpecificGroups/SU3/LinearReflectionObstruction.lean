module
public import Theory.SpecificGroups.SU3.LinearNormalizerReflections
public import Theory.SpecificGroups.SU3.DiagonalReflectionObstruction

/-!
# Linear reflections are excluded by the rank of an actual cover

Orthogonal reflection coordinates carry the entire special unitary subgroup
to its identity-Gram realization. Conjugate the given overgroup and its
surjective covering map by the same matrix, then use the three-axis
involution-centralizer obstruction. Rank is never moved to a quotient.

Source: Aschbacher--Smith H.2, printed p.378, applying A.1.31(1).
-/
public section
open Subgroup Matrix Module BenderSuzuki.MatrixGroups
open UnitaryThree.OddTorusNormalizer

namespace UnitaryThree
open HermitianForm HermitianForm.IdentityGram HermitianForm.LinearNormalizerReflections
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  {p : ℕ} [Fact p.Prime]

/-- A rank-one odd-prime actor in an actual linear SU₃ overgroup contradicts
the odd-rank bound on its covering group. -/
theorem no_linear_reflection_in_rank_two_section
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) (q : ℕ)
    (hcard : Nat.card F = q^2) (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (H : Subgroup (GL (Fin 3) F)) (hSU : J.specialSubgroup ≤ H)
    (hp : Odd p) (f : K →* H) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (S : H) (ho : orderOf S = p)
    (hN : ∀ X : J.specialSubgroup, S.val * X.val * S.val⁻¹ ∈ J.specialSubgroup)
    (hr : finrank F (LinearMap.range (Matrix.toLin' S.val.val - LinearMap.id)) = 1)
    (hd : GeneralLinearGroup.det S.val ≠ 1) : False := by
  obtain ⟨P,hP,hn⟩ := exists_reflection_frame J hJ hconj q hcard hfixed S.val hN hr hd
  let c := (MulAut.conj P.val⁻¹).toMonoidHom
  let H' := H.map c
  let e := H.equivMapOfInjective c (MulAut.conj P.val⁻¹).injective
  have hSU' : (identityGram J).specialSubgroup ≤ H' := by
    intro X hX
    refine ⟨P.val * X * P.val⁻¹,hSU ((special_conjugate_iff J P.val X P.property).mpr hX),?_⟩
    change P.val⁻¹ * (P.val*X*P.val⁻¹) * (P.val⁻¹)⁻¹ = X
    simp [mul_assoc]
  have hthird : diagonalHom ![1,1,GeneralLinearGroup.det S.val] ∈ H' := by
    refine ⟨S.val,S.property,?_⟩
    change P.val⁻¹*S.val*(P.val⁻¹)⁻¹ = _
    simpa only [inv_inv] using hP
  let t := permutationGL (E := F) (Equiv.swap (0 : Fin 3) 2)
  have ht : t ∈ H' := hSU' (permutationGL_special J _)
  have heq : t * diagonalHom ![1,1,GeneralLinearGroup.det S.val] * t⁻¹ =
      diagonalHom ![GeneralLinearGroup.det S.val,1,1] := by
    apply Units.ext
    change (permutationGL (Equiv.swap (0 : Fin 3) 2)).val *
      (diagonalHom ![1,1,GeneralLinearGroup.det S.val]).val *
      ((permutationGL (Equiv.swap (0 : Fin 3) 2))⁻¹).val = _
    rw [←map_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [permutationGL_apply,diagonalHom,Matrix.mul_apply,Fin.sum_univ_three,Equiv.swap_apply_def]
  have hlam : orderOf (GeneralLinearGroup.det S.val) = p := by
    have hdiv : orderOf (GeneralLinearGroup.det S.val) ∣ p := by
      rw [←ho]
      exact orderOf_map_dvd (GeneralLinearGroup.det.comp H.subtype) S
    exact ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv).resolve_left
      (fun he => hd (orderOf_eq_one_iff.mp he))
  exact no_diagonal_reflection_in_rank_two_section J H' hSU' hp
    (e.toMonoidHom.comp f) (e.surjective.comp hf) hrank
    (GeneralLinearGroup.det S.val) hlam hn (heq ▸ H'.mul_mem (H'.mul_mem ht hthird) (H'.inv_mem ht))
end UnitaryThree


namespace UnitaryThree
variable {F K B : Type*} [Field F] [Finite F] [CharP F 2] [Group K] [Finite K]
  [Group B] {p : ℕ} [Fact p.Prime]

/-- Restrict the original covering group to its field-linear image before
applying the reflection obstruction. -/
theorem no_linear_reflection_in_injective_image
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∃ z : F, J.conj z ≠ z) (q : ℕ)
    (hcard : Nat.card F = q^2) (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (r : GL (Fin 3) F →* B) (hinj : Function.Injective r)
    (f : K →* B) (hrank : primeRank p K ≤ 2) (hp : Odd p)
    (hSU : ∀ X : J.specialSubgroup, r X.val ∈ f.range)
    (S : GL (Fin 3) F) (hS : r S ∈ f.range) (ho : orderOf S = p)
    (hN : ∀ X : J.specialSubgroup, S * X.val * S⁻¹ ∈ J.specialSubgroup)
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
  have horder : orderOf S' = p :=
    (orderOf_injective g.range.subtype g.range.subtype_injective S').symm.trans ho
  exact no_linear_reflection_in_rank_two_section J hJ hconj q hcard hfixed
    g.range (fun x hx => hpre x (hSU ⟨x,hx⟩)) hp g.rangeRestrict
    g.rangeRestrict_surjective ((primeRank_subgroup_le p P).trans hrank)
    S' horder hN hr hd
end UnitaryThree
