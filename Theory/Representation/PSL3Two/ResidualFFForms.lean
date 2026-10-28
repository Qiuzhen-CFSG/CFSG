module

public import Theory.Representation.PSL3Two.ResidualFFForms.Descent
public import Theory.Representation.PSL3Two.ResidualFFForms.Reduction
public import Theory.Representation.PSL3Two.ResidualFFForms.Induction
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget

/-!
# Constituent and restriction reductions for binary invariant forms

Simple binary actions descend through a normal two-group kernel without
changing the costs of a prescribed actor or its image. Separately, the modular
fixed-vector theorem reduces vanishing of two-residual invariant bilinear
forms to vanishing of whole-group invariant forms.

These reductions retain arbitrary nonsplit modules. The numerical
`SimpleBudget` criterion records the concrete constituent facts needed by an
induction on such modules; the reductions do not assume that the original
module is semisimple or that its two-group kernel acts trivially.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.4) and (3.8), printed pp.842 and 878.
-/

public section

open Representation Representation.BinaryOffender

namespace BinaryLinearThree.ResidualFFForms

universe u v

variable {G : Type v} [_root_.Group G] [Finite G]
  {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A projected binary `SL₃(2)` offender excludes every form fixed by the
two-residual, even when the two-group kernel acts nontrivially on nonsplit
extensions. -/
theorem form_zero_of_projected_SL3_residual_invariance
    (π : G →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) G V)
    (hfull : subspaceCommutator ρ ⊤ (pResidual 2 G) = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hmap : A.map π ≠ ⊥)
    (hcost : fixedCodim ρ A ≤ rank (A.map π))
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g ∈ pResidual 2 G, ∀ v w,
      B (ρ g v) (ρ g w) = B v w) : B = 0 := by
  let hAm : IsElementaryAbelian 2 (A.map π) := IsElementaryAbelian.map π
  have hbudgetQ : SimpleBudget.{u} (A.map π) (rank (A.map π)) :=
    simpleBudget (A.map π) hmap hAm
  have hbudget : SimpleBudget.{u} A (rank (A.map π)) :=
    simpleBudget_of_surjective π hπ hp A (rank (A.map π)) hbudgetQ
  have htop : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    apply top_unique
    calc
      (⊤ : Submodule (ZMod 2) V) = subspaceCommutator ρ ⊤ (pResidual 2 G) := hfull.symm
      _ ≤ subspaceCommutator ρ ⊤ ⊤ := by
        apply Submodule.span_mono
        rintro _ ⟨g, hg, v, hv, rfl⟩
        exact ⟨g, Subgroup.mem_top _, v, hv, rfl⟩
  exact form_zero_of_residual_invariance ρ
    (fun C hC => form_zero_of_simpleBudget ρ A (rank (A.map π))
      hbudget hcost htop C hC)
    B hB

end BinaryLinearThree.ResidualFFForms
