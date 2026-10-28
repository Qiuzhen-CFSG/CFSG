module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Basic

/-!
# A nine-subgroup in the higher minus residual image

In ambient minus rank at least five the complement contains the published
marked four-space. Its left SL₂ commutes with the original right SL₂.
Transvection generation puts both factors in the literal centralizer residual,
including over F₃. The involutory projective kernel preserves the product of
the two displayed cubic subgroups.

Source: the three-rank obstruction in Aschbacher–Smith A.2.17, printed p.39.
The subgroup lies below `centralizerResidualImage` through the actual subtype
inclusion. No full centralizer equality, complementary generation, scalar
membership criterion, or perfectness is needed for this higher-rank consequence.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- The right SL₂ and a marked SL₂ inside the complement, followed by the literal projective map. -/
def higherPairHom [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →*
      ClassicalGroup.POmegaMinus (r + 5) F :=
  (projectiveBlockHom (r + 2) hq).comp
    ((MonoidHom.id _).prodMap ((splitOmegaHom r (Minus.parameter F) hq).comp fourLeft))

/-- Both SL₂ factors lie in the actual prime-to-p residual, without complementary generation. -/
theorem higherPairHom_mem_residual [Finite F] (p : ℕ) [CharP F p]
    (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    higherPairHom r hq g ∈ centralizerResidualImage p (r + 2) hq := by
  let f := (blockToCentralizer (r + 2) hq).comp
    ((MonoidHom.id _).prodMap ((splitOmegaHom r (Minus.parameter F) hq).comp fourLeft))
  have h1 := Matrix.SL2.map_mem_primeToResidual p (f.comp (MonoidHom.inl _ _)) g.1
  have h2 := Matrix.SL2.map_mem_primeToResidual p (f.comp (MonoidHom.inr _ _)) g.2
  have hg : f g ∈ centralizerResidual p (r + 2) hq := by
    have he : g = (g.1, 1) * (1, g.2) := by simp
    rw [he, map_mul]
    exact Subgroup.mul_mem _ h1 h2
  exact ⟨f g, hg, rfl⟩

/-- The published scalar bound applies to the two explicit SL₂ factors. -/
theorem higherPairHom_kernel_square [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)
    (hg : higherPairHom r hq g = 1) : g ^ 2 = 1 := by
  let f : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 2) F ×
        Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) :=
    (MonoidHom.id _).prodMap ((splitOmegaHom r (Minus.parameter F) hq).comp fourLeft)
  have hf : Function.Injective f := by
    intro a b hab
    change (a.1, splitOmegaHom r (Minus.parameter F) hq (fourLeft a.2)) =
      (b.1, splitOmegaHom r (Minus.parameter F) hq (fourLeft b.2)) at hab
    have hab1 := congrArg Prod.fst hab
    have hab2 := congrArg Prod.snd hab
    exact Prod.ext hab1
      (fourLeft_injective (splitOmegaHom_injective r (Minus.parameter F) hq
        hab2))
  apply hf
  rw [map_pow, map_one]
  exact projectiveBlockHom_kernel_square (r + 2) hq (f g) hg

/-- An actual nine-subgroup in the literal residual image for ambient minus rank at least five. -/
theorem higher_residualImage_contains_nine [Finite F] (p : ℕ) [CharP F p]
    (r : ℕ) (hq : 2 < Nat.card F) :
    ∃ E : Subgroup (ClassicalGroup.POmegaMinus (r + 5) F),
      E ≤ centralizerResidualImage p (r + 2) hq ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, he, hc⟩ := CubicProductQuotient.exists_nine (higherPairHom (F := F) r hq)
    (higherPairHom_kernel_square (F := F) r hq)
    (cubicSL (F := F)) (cubicSL (F := F)) (cubicSL_order (F := F)) (cubicSL_order (F := F))
  refine ⟨E, ?_, he, hc⟩
  intro x hx
  obtain ⟨g, rfl⟩ := hE hx
  exact higherPairHom_mem_residual p r hq g


end ClassicalOrthogonal.Fundamental.MinusCentralizer
