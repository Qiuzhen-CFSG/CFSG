module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Setup
public import Theory.GroupTheory.PResidual.FiniteLocalPair

/-!
# The actual two-perfect residual of the universal cubic action

Only the two finite local groups and their common Sylow are needed for the
residual calculation. The acting group itself may be infinite. In particular,
the calculation applies to Goldschmidt's universal completion, and identifies
its two-perfect normal subgroup and the literal common-Sylow supplement.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (3.2),
printed pp.386--387. Restriction to its faithful action remains a separate step.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Both local residuals generate the true ambient residual; it is two-perfect
and the original edge stabilizer supplements it. -/
theorem CubicTreeAction.residual_source (h : CubicTreeAction F) :
    pResidual 2 G = (pResidual 2 (F false)).map (F false).subtype ⊔
      (pResidual 2 (F true)).map (F true).subtype ∧
    IsPPerfect 2 (pResidual 2 G) ∧
    pResidual 2 G ⊔ (F false ⊓ F true) = ⊤ := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  obtain ⟨P, hP⟩ := h.primitive.sylow.left_sylow
  obtain ⟨Q, hQ⟩ := h.primitive.sylow.right_sylow
  have hp : (P : Subgroup (F false)).map (F false).subtype = F false ⊓ F true := by
    rw [hP, ← MonoidHom.range_comp]
    exact (F false ⊓ F true).range_subtype
  have hq : (Q : Subgroup (F true)).map (F true).subtype = F false ⊓ F true := by
    rw [hQ, ← MonoidHom.range_comp]
    exact (F false ⊓ F true).range_subtype
  exact ⟨pResidual_eq_sup_of_finite_sylow_pair _ _ _ P Q hp hq h.generated,
    isPPerfect_pResidual_of_finite_sylow_pair _ _ _ P Q hp hq h.generated,
    pResidual_sup_of_finite_sylow_pair _ _ _ P Q hp hq h.generated⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
