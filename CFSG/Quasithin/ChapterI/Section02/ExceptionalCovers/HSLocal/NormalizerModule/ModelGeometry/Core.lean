module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Setup
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.InvolutionLifting

/-!
# The marked core in the HS normalizer geometry

We fix the literal subgroups A, X₀, R₀ and V₀ used in the final HS paragraph
of I.2.2(5). The concrete C₄³ coordinates identify the involutions of A with
the marked elementary eight, so the established HS class calculation makes
every involution of A two-central. A centralizes the marked elementary eight,
hence lies in C(e₀). Its inclusion in O²(C(e₀)) and the normal generation by
V₀ require the separate centralizer incidences.

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open Theory.GroupTheory.DoubleCoverCentralizer

/-- The actual normalizer core embedded in the exact HS carrier. -/
def A : Subgroup Carrier := (pCore 2 baseNormalizer).map baseNormalizer.subtype

/-- The two-residual of the marked involution centralizer, embedded in HS. -/
def X₀ : Subgroup Carrier := centralizerTwoResidual e0

/-- The two-core of that residual, embedded in HS. -/
def R₀ : Subgroup Carrier := ExceptionalCovers.centralizerCore e0

/-- The center of the residual two-core, embedded in HS. -/
def V₀ : Subgroup Carrier := HSLocal.coreCenter e0

/-- The concrete equivalence supplies the source's C₄³ model premise. -/
noncomputable def coreEquiv :
    pCore 2 baseNormalizer ≃* Multiplicative (Fin 3 → ZMod 4) :=
  CoreGeometry.coreEquiv

theorem elementary_le_A : baseElementary ≤ A := CoreGeometry.elementary_le_core_image

theorem A_le_normalizer : A ≤ baseNormalizer := map_subtype_le _

theorem A_le_elementary_centralizer : A ≤ centralizer (baseElementary : Set Carrier) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [model_core_eq_action_ker, normalizerMonoidHom_ker] at hx
  exact hx


theorem A_le_marked_centralizer : A ≤ centralizer ({e0} : Set Carrier) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact (A_le_elementary_centralizer hx e0
    (show e0 ∈ baseElementary from subset_closure ⟨0, Fin.le_last 0, rfl⟩)).symm

/-- This is the model involution-purity premise consumed by the cover argument. -/
theorem A_order_two_mem_elementary (a : Carrier) (ha : a ∈ A)
    (ha2 : orderOf a = 2) : a ∈ baseElementary := by
  obtain ⟨x, hx, rfl⟩ := ha
  change orderOf (x : Carrier) = 2 at ha2
  apply (CoreGeometry.core_involution_iff (⟨x, hx⟩ : pCore 2 baseNormalizer)).mp
  apply Subtype.ext
  apply Subtype.ext
  change (x : Carrier) ^ 2 = 1
  simpa only [ha2] using pow_orderOf_eq_one (x : Carrier)

theorem A_involutions_twoCentral (a : Carrier) (ha : a ∈ A)
    (ha2 : orderOf a = 2) : TwoCentral a :=
  baseElementary_twoCentral a (A_order_two_mem_elementary a ha ha2) ha2

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
