module

public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Defining-characteristic Sylow subgroups of SL₂

Every Sylow subgroup in the defining characteristic of a finite field is
isomorphic to the additive field. The upper-unipotent Sylow construction and
Sylow conjugacy give this equivalence. Conjugation by the standard Weyl matrix
carries a nontrivial upper transvection outside the upper-unipotent subgroup,
so no defining-characteristic Sylow subgroup is normal. This includes SL₂(2).

These are elementary matrix consequences of the Sylow construction; they
supply the non-2-closed fixed-group calculation in GLS, Volume 4, Chapter 4,
Lemma 3.4(c).
-/

namespace Matrix.SpecialLinearGroup
variable (K : Type*) [Field K] [Finite K]

@[expose] public noncomputable def sylowEquivAdditive (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Sylow p (SpecialLinearGroup (Fin 2) K)) : Multiplicative K ≃* P :=
  (MonoidHom.ofInjective (upperUnipotentHom_injective K)).trans
    ((upperUnipotentSylow K p).equiv P)

omit [Finite K] in
public theorem upperUnipotent_not_normal : ¬ (upperUnipotent K).Normal := by
  intro h
  let w : SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let u := upperUnipotentHom K (Multiplicative.ofAdd (1 : K))
  have hu : u ∈ upperUnipotent K := ⟨_, rfl⟩
  have hw := h.conj_mem u hu w
  obtain ⟨t, ht⟩ := (mem_upperUnipotent K _).mp hw
  have he := congrArg (fun g : SpecialLinearGroup (Fin 2) K => g.1 1 0) ht
  have hw_inv : (w⁻¹).1 = !![0, 1; -1, 0] := by
    change (Matrix.adjugate w.1) = _
    simp [w, Matrix.adjugate_fin_two]
  change (transvection zero_ne_one t).1 1 0 =
    ((w.1 * u.1) * (w⁻¹).1) 1 0 at he
  simp [u, upperUnipotentHom, transvection_coe, hw_inv,
    w, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at he

public theorem no_normal_sylow (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Sylow p (SpecialLinearGroup (Fin 2) K)) : ¬ (P : Subgroup (SpecialLinearGroup (Fin 2) K)).Normal := by
  intro hP
  let := Sylow.unique_of_normal P hP
  have hUP : upperUnipotentSylow K p = P := Subsingleton.elim _ _
  have hU : (upperUnipotent K).Normal := by
    change (upperUnipotentSylow K p : Subgroup (SpecialLinearGroup (Fin 2) K)).Normal
    rw [hUP]
    exact hP
  exact upperUnipotent_not_normal K hU
end Matrix.SpecialLinearGroup
