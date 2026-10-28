module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallAlternatingBaseBound
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualCrossing

/-!
# Two alternating-four residuals exclude a large original overlap

Goldschmidt's crossing argument supplies an involution from one residual
four-group outside the opposite two-core. The two faithful residual actions
then bound the original common overlap by 32. This applies directly to the
original cubic tree action, without passing to its two-perfect normal base.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.2),
printed pp.392–393; the compatible normal-base action is (2.8), p.381.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Both actual local residuals being A4 forces a small original overlap. -/
theorem CubicTreeAction.overlap_card_le_thirtyTwo_of_alternating_residuals
    (h : CubicTreeAction F)
    (e₀ : pResidual 2 (F false) ≃* alternatingGroup (Fin 4))
    (e₁ : pResidual 2 (F true) ≃* alternatingGroup (Fin 4)) :
    Nat.card (F false ⊓ F true : Subgroup G) ≤ 32 :=
  h.overlap_card_le_thirtyTwo_of_alternating_crossing e₀ e₁
    (h.alternating_residual_core_not_le_opposite e₀)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
