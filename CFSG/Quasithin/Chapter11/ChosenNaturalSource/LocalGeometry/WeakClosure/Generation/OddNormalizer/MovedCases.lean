module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ImageModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FinalOrdinary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SelectedNormal

/-!
# The surviving moved C-components have J₄ or Ru quotient and a full SL₃(4) actor

The proved inner placement puts the original residual in the component of
N_G(A). Its literal central image then meets all hypotheses of the completed
C-model inspection. The surviving model orders force the same field-four
special-linear quotient as in the ordinary pushing-up branch. All conclusions
refer to the original V, residual and covering quotient.

Source applies this to the actual Hall kernel. The two remaining local model
exclusions and B-only component cases remain with this task; this is not yet
odd-kernel normalizer control. Source: Aschbacher--Smith 4.4.10--12, pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The original moved C-component reaches only the two actual remaining rows,
with normal placement and the full cubic covering quotient proved. -/
theorem moved_component_last_models {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hmodel : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
        Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
      S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
        Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  obtain ⟨hn,hv,hf,hz⟩ := moved_component_normal_of_theoremC D S hA hodd hu hout K hK houtK hmodel
  have hi := placed_residual_natural_cover_image D S hA hodd K hf
  have hm := hi.theoremC_models D S hmodel
  refine ⟨hn,hv,hf,hz,hm,?_⟩
  have hd := hi.product_card_dvd D
  rcases hm with hJ | hR
  · obtain ⟨e⟩ := hJ
    rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hd
    exact field_four_of_product_order_dvd D S _ (Or.inr rfl) hd
  · obtain ⟨e⟩ := hR
    rw [Nat.card_congr e.toEquiv,Rudvalis.model_card] at hd
    exact field_four_of_product_order_dvd D S _ (Or.inl rfl) hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
