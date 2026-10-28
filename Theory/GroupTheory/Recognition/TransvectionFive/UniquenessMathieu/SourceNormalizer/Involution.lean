module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.FourNormalizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.ResidualFour

/-!
# Source 40.4(2) for the exceptional involution class

The literal centralizer quotient is S₅. Its solvable residual fixes exactly
the marked four-subgroup, whose normalizer is the product XI for an actual
order-three lift X with XA₂ normal in N_G(A₂). This assembles all clauses of
the existing source contract without replacing its quotient or subgroup maps.
Only nonidentity and exclusion from the distinguished conjugacy class are
required; the source second-class fusion exclusion is a separate theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private def CubicFourData (A B I : Subgroup G) : Prop :=
  ∃ X : Subgroup (normalizer (A : Set G)), Nat.card X = 3 ∧
    (X ⊔ A.subgroupOf (normalizer (A : Set G))).Normal ∧
    (normalizer (B : Set G)).subgroupOf (normalizer (A : Set G)) =
      X ⊔ I.subgroupOf (normalizer (A : Set G)) ∧
    ((normalizer (B : Set G)).subgroupOf (normalizer (A : Set G)) :
      Set (normalizer (A : Set G))) =
      (X : Set (normalizer (A : Set G))) *
        (I.subgroupOf (normalizer (A : Set G)) : Set (normalizer (A : Set G)))

private theorem plane_cubic_four_data (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (ht : t ∈ F.plane) (ht1 : t ≠ 1) (hzt : ¬ IsConj z t) :
    CubicFourData F.plane (planeResidualFour F t) (planeCentralizer F t) := by
  obtain ⟨i,hi,_⟩ := exists_unique_planeFour F hc t ht ht1 hzt
  obtain ⟨X,hXcard,hXmap,hXjoin⟩ := exists_plane_cubic_lift F hc
  have hnormal : (X ⊔ F.plane.subgroupOf (planeNormalizer F)).Normal := by
    rw [hXjoin]
    infer_instance
  refine ⟨X,hXcard,hnormal,?_,?_⟩
  · rw [planeResidualFour_eq_of_mem_four F hc t ht1 i hi]
    exact plane_four_normalizer_join F hc X hXmap i t hi ht1
  · rw [planeResidualFour_eq_of_mem_four F hc t ht1 i hi]
    exact plane_four_normalizer_product F hc X hXmap i t hi ht1

/-- All source 40.4(2) centralizer and four-subgroup conclusions, on the
literal original A₂, for an element outside the distinguished conjugacy class.
The source fusion exclusion for `SecondInvolutionClass` remains separate. -/
theorem involutionCentralizerData_of_not_fused (hcounts : MathieuFusionOrientation F)
    (t : G) (ht : t ∈ F.threeSpace) (ht1 : t ≠ 1) (hzt : ¬ IsConj z t) :
    Nonempty (InvolutionCentralizerData F t) := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  have h := plane_cubic_four_data (oppositeMarking F) hc t
    (by simpa only [oppositeMarking_plane] using ht) ht1 hzt
  have heq : planeCentralizer (oppositeMarking F) t = involutionCentralizer F t :=
    congrArg (fun A : Subgroup G => normalizer (A : Set G) ⊓ centralizer ({t} : Set G))
      (oppositeMarking_plane F)
  rw [heq, opposite_planeResidualFour_eq F t, oppositeMarking_plane] at h
  obtain ⟨X,hcard,hnormal,hjoin,hprod⟩ := h
  exact ⟨{
    quotient_equiv := involutionCentralizer_quotient_of_not_fused F hcounts t ht ht1 hzt
    four_card := involutionFour_card_of_not_fused F hcounts t ht ht1 hzt
    cubic := X
    cubic_card := hcard
    cubic_extension_normal := hnormal
    four_normalizer := hjoin
    product := hprod }⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
