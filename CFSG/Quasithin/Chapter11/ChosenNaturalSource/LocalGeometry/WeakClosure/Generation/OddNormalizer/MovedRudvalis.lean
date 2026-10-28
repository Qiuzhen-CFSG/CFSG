module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.Rudvalis
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedOuter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OddFour

/-!
# The moved component cannot have Rudvalis central quotient

The actual residual image retains the full quotient L/O₂(L). If its ambient
central quotient were Ru, the product-order obstruction would force this
full quotient to be SL₃(4). Its central cubic lifts through the two-core of
the residual image. The centralizer of a lifted cubic still covers SL₃(4),
contradicting the native Rudvalis cubic-centralizer bound.

This reuses the model calculation from the ordinary branch, but uses no
C.2.8 hypothesis: the moved ambient has trivial two-core. In the outer-action
alternative Ru is already excluded by its solvable outer group. Thus the
same selected component cannot have Ru quotient in either action, and every
placed component in the full B-catalogue now has J₄ quotient. Source applies
the exclusion to the original odd actor and the literal Hall kernel.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, and the native
Rudvalis cubic-centralizer calculation used for the local inspection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The full residual quotient, including its central cubic, excludes Ru. -/
theorem NaturalCoverImage.not_rudvalis {Q : Type*} [Group Q] [Finite Q]
    (h : NaturalCoverImage D Q) (e : Q ≃* Rudvalis.Model) : False := by
  have hd := h.product_card_dvd D
  rw [Nat.card_congr e.toEquiv,Rudvalis.model_card] at hd
  obtain ⟨hf,⟨a⟩,_⟩ := field_four_of_product_order_dvd D S _ (Or.inl rfl) hd
  obtain ⟨X,U,hX,hU,hUX,hN,hcard,⟨b⟩⟩ := h.of_equiv D e
  let t := b.trans a
  apply Normalizers.FixedSummand.Centralizer.rudvalis_no_cubic_center_quotient
    X (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  · rw [Nat.card_congr (centerCongr t).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num [S.field.card_eq,hf]
  · rw [Nat.card_congr t.toEquiv,linear_three_order]
    norm_num [S.field.card_eq,hf]

/-- The full B-catalogue sieve for a placed residual now retains only J₄. -/
theorem NaturalCoverImage.theoremB_models_jankoFour {Q : Type*} [Group Q] [Finite Q]
    (h : NaturalCoverImage D Q) (hm : ChapterA.Section02.IsTheoremBModel Q) :
    Nonempty (Q ≃* Janko4.Model) := by
  rcases h.theoremB_models_sporadic D S hm with hj | hr
  · exact hj
  · exact (h.not_rudvalis D S hr.some).elim

open Chapter4 Chapter4.Section04
/-- Ru is excluded on the actual moved component, in either action. -/
theorem moved_component_not_rudvalis {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (e : (K ⧸ center K) ≃* Rudvalis.Model) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,himage,_⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    exact himage.not_rudvalis D S e
  · exact (moved_outer_section_exclusions D S K hK ho).1
      (.sporadic (Or.inl ⟨.ru,(by intro h; cases h),⟨e⟩⟩))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
