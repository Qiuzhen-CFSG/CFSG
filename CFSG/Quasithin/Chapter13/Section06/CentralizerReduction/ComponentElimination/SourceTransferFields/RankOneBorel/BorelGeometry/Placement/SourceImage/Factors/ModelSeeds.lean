module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.Decomposition
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Nontrivial residuals in the E.2.3 factors

A concrete order-three matrix works over every field of characteristic two,
including the prime field. A three-cycle does the same in S₅. Transport through
the actual factor isomorphisms supplies a nontrivial two-residual in every
factor. The abstract selection argument then proves that the decomposition
has exactly one factor whenever the ambient residual is simple.

Source application: Aschbacher–Smith E.2.3(1) and 13.6.18,
printed pp.216 and 931. No simplicity or order computation for a new model
is required for the factor seeds.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors

/-- A uniform cubic element of the actual binary special-linear model. -/
theorem exists_cubic_linear (F : Type*) [Field F] [CharP F 2] :
    ∃ a : SL(2,F), orderOf a = 3 := by
  let a : SL(2,F) := ⟨!![0, 1; 1, 1], by simp [det_fin_two, CharTwo.neg_eq]⟩
  have ha : a ^ 3 = 1 := by
    apply Subtype.ext
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hne : a ≠ 1 := by
    intro h
    have he := congrArg (fun x : SL(2,F) => x.val 0 0) h
    exact zero_ne_one he
  exact ⟨a, orderOf_eq_prime ha hne⟩

/-- A cubic element of the actual five-letter symmetric group. -/
theorem exists_cubic_symmetric : ∃ a : Equiv.Perm (Fin 5), orderOf a = 3 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]

/-- Model recognition supplies an odd-order nonidentity element in the
literal internal factor, not merely in an unrelated model carrier. -/
theorem FactorModule.exists_cubic {ρ : Representation (ZMod 2) A W}
    {N B : Subgroup A} (m : FactorModule ρ N B) :
    ∃ b : B, orderOf b = 3 := by
  cases m with
  | linear m =>
    obtain ⟨a, ha⟩ := exists_cubic_linear m.field.Carrier
    exact ⟨m.actor.symm a, (orderOf_injective m.actor.symm.toMonoidHom
      m.actor.symm.injective a).trans ha⟩
  | symmetric m =>
    obtain ⟨a, ha⟩ := exists_cubic_symmetric
    exact ⟨m.actor.symm a, (orderOf_injective m.actor.symm.toMonoidHom
      m.actor.symm.injective a).trans ha⟩

variable {H : Type*} [Group H] [Finite H]
variable {q : H →* A} {T : Subgroup H} {ρ : Representation (ZMod 2) A W}

/-- E.2.3(1)'s original residual containment passes through the specified
surjective quotient, identifying no Thompson subgroup in the quotient. -/
theorem Decomposition.residual_le_image (d : Decomposition q T ρ)
    (hq : Function.Surjective q) : pResidual 2 A ≤ globalImage q := by
  rw [← map_pResidual_of_surjective 2 q hq]
  exact map_mono d.residual_le_global

omit [Finite H] in
/-- The two-residual of the Thompson image lies in the restriction of the
ambient residual, by functoriality. -/
theorem residual_image_le_internal (q : H →* A) :
    pResidual 2 (globalImage q) ≤ (pResidual 2 A).subgroupOf (globalImage q) := by
  intro x hx
  exact map_pResidual_le 2 (globalImage q).subtype (mem_map_of_mem _ hx)

/-- The one-or-two alternative is reduced to exactly one using the actual
simple residual and the actual factor models. -/
theorem Decomposition.size_eq_one (d : Decomposition q T ρ)
    (hq : Function.Surjective q) [IsSimpleGroup (pResidual 2 A)] :
    d.factors.size = 1 := by
  let : IsSimpleGroup ((pResidual 2 A).subgroupOf (globalImage q)) :=
    (subgroupOfEquivOfLe (d.residual_le_image hq)).isSimpleGroup
  apply SourceFactors.size_eq_one d.factors _ (residual_image_le_internal q)
  intro i
  obtain ⟨b, hb⟩ := (d.modules i).exists_cubic
  refine ⟨b, ?_, by rw [hb]; decide⟩
  intro h
  rw [h, orderOf_one] at hb
  contradiction

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
end
