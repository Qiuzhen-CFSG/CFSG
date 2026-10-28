module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Irreducibility

/-!
# Source module branches with the literal quotient maps

A natural marking of the central quotient through L/O₂(L) is transported
to the source's L/C_L(V) marking when that actor is simple. In degree five,
projectivity reconstructs the whole original module from this central
quotient, providing both 12.2.2(3d) and the full conjugation model used in 13.3.2.
The four-dimensional linear-three case obtains indecomposability from Irr⁺.

Source: Aschbacher--Smith 12.2.2(3b,d), p.795, and 13.3.2(3), p.885;
the reconstruction uses I.1.6(1), p.408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Transport an actual central-quotient marking along the canonical
isomorphism L/O₂(L) → L/C_L(V). -/
def faithfulCentralMarking
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) A W}
    (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (e : (L ⧸ pCore 2 L) ≃* A)
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] W)
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      σ (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    letI := D.actionCentralizer_normal
    ActionEquiv D.faithfulCentralAction σ := by
  letI := D.actionCentralizer_normal
  refine ⟨(D.coreToFaithfulEquiv hs).symm.trans e,a,?_⟩
  intro q v
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) q
  have he : (D.coreToFaithfulEquiv hs).symm
      (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) =
      QuotientGroup.mk' (pCore 2 L) l := by
    apply (D.coreToFaithfulEquiv hs).injective
    rw [MulEquiv.apply_symm_apply,D.coreToFaithfulEquiv_mk]
  change a (D.chosenCentralAction l v) =
    σ (e ((D.coreToFaithfulEquiv hs).symm
      (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l))) (a v)
  rw [he]
  exact ha l v

/-- The original central-quotient A₅ marking supplies both the printed
alternating alternative and the full original conjugation model for 13.3.2. -/
theorem alternatives_and_a5_model_of_central_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    ModuleAlternatives1222 D ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨.alternating 5 (by decide) (by decide)
    (D.faithfulCentralMarking e.isSimpleGroup e a ha),
    D.a5_model_of_central_quotient e a ha⟩

/-- Dimension four and the actual linear-three quotient suffice for the
printed extension row: indecomposability is already forced by the choice. -/
theorem alternatives_of_linearThree_four
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4) : ModuleAlternatives1222 D :=
  .linearThreeExtension e hd D.quotientAction_indecomposable

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
