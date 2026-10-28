module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Centralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Residual

/-!
# The literal solvable-residual fixed four-subgroup

The centralizer quotient maps onto the exceptional-vector stabilizer with
its original conjugation action. Surjective transport of solvable residuals
therefore identifies its fixed subgroup with the actual four-subgroup in the
marked six-line geometry. Marking interchange gives C_{A₂}(I^∞) and its
order four. The distinguished-class exclusion remains explicit until the
source fusion argument supplies it.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The literal residual-fixed subgroup for an arbitrary 45-point plane marking. -/
def planeResidualFour (t : G) : Subgroup G :=
  F.plane ⊓ centralizer
    (((solvableResidual (planeCentralizer F t)).map (planeCentralizer F t).subtype) : Set G)

private def residualProjection (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    planeCentralizer F t →* Sextet.pointFixer x :=
  (planeCentralizerPointEquiv F hc t x hxt).toMonoidHom.comp
    (QuotientGroup.mk' (F.plane.subgroupOf (planeCentralizer F t)))

private theorem residualProjection_surjective (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    Function.Surjective (residualProjection F hc t x hxt) :=
  (planeCentralizerPointEquiv F hc t x hxt).surjective.comp (QuotientGroup.mk'_surjective _)

private theorem residualProjection_action (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) (n : planeCentralizer F t) (y : Code) :
    element F ((residualProjection F hc t x hxt n).val.val y) =
      (n : G) * element F y * (n : G)⁻¹ :=
  planeCentralizerPointEquiv_action F hc t x hxt n y

/-- The actual residual-fixed subgroup is the original embedded four-subgroup,
not merely a group of order four. -/
theorem planeResidualFour_eq (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) (hx : Sextet.exceptional x = true)
    (i : Fin 6) (hi : x ∈ Sextet.line i) :
    planeResidualFour F t = planeFour F i := by
  let p := residualProjection F hc t x hxt
  have hp : (solvableResidual (planeCentralizer F t)).map p =
      solvableResidual (Sextet.pointFixer x) :=
    map_solvableResidual_eq p (residualProjection_surjective F hc t x hxt)
  have hcard : Nat.card Sextet.symmetryGroup = 2160 := by
    let e := MulEquiv.ofBijective (planeSextetRepresentation F hc)
      ⟨planeSextetRepresentation_injective F hc, planeSextetRepresentation_surjective F hc⟩
    exact (Nat.card_congr e.toEquiv).symm.trans (planeSextet_quotient_card F hc)
  ext a
  rw [mem_planeFour]
  constructor
  · rintro ⟨ha, hz⟩
    obtain ⟨y, hy⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
    have hya : element F y = a := congrArg Subtype.val hy
    refine ⟨y, ?_, hya⟩
    apply (Sextet.residual_fixed_iff hcard x hx i hi y).mp
    intro f hf
    rw [← hp] at hf
    obtain ⟨n, hn, rfl⟩ := hf
    apply element_injective F
    rw [residualProjection_action, hya]
    rw [hz (n : G) (mem_map_of_mem _ hn), mul_inv_cancel_right]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨element_mem F y, ?_⟩
    rintro b ⟨n, hn, rfl⟩
    have hf : p n ∈ solvableResidual (Sextet.pointFixer x) := hp ▸ mem_map_of_mem p hn
    have he := (Sextet.residual_fixed_iff hcard x hx i hi y).mpr hy (p n) hf
    have hg := congrArg (element F) he
    rw [residualProjection_action] at hg
    exact mul_inv_eq_iff_eq_mul.mp hg

/-- Every nonzero element outside the distinguished class has the literal
residual-fixed four-subgroup specified by the six-point geometry. -/
theorem planeResidualFour_eq_of_mem_four (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (ht1 : t ≠ 1)
    (i : Fin 6) (hi : t ∈ planeFour F i) : planeResidualFour F t = planeFour F i := by
  obtain ⟨x, hx, hxt⟩ := (mem_planeFour F i t).mp hi
  apply planeResidualFour_eq F hc t x hxt _ i hx
  apply Sextet.line_exceptional i x hx
  exact fun h => ht1 (hxt.symm.trans (h ▸ element_zero F))

omit [Finite G] in
/-- Marking interchange preserves the actual residual-fixed subgroup,
including its centralizer and subgroup inclusion. -/
theorem opposite_planeResidualFour_eq (t : G) :
    planeResidualFour (oppositeMarking F) t = involutionFour F t := by
  have heq : planeCentralizer (oppositeMarking F) t = involutionCentralizer F t :=
    congrArg (fun A : Subgroup G => normalizer (A : Set G) ⊓ centralizer ({t} : Set G))
      (oppositeMarking_plane F)
  unfold planeResidualFour
  rw [heq, oppositeMarking_plane]
  rfl

/-- In the original oriented A₂, the solvable-residual fixed subgroup is
exactly the unique exceptional four-subgroup containing t. -/
theorem involutionFour_eq_of_mem_four (hcounts : MathieuFusionOrientation F)
    (t : G) (ht1 : t ≠ 1)
    (i : Fin 6) (hi : t ∈ planeFour (oppositeMarking F) i) :
    involutionFour F t = planeFour (oppositeMarking F) i := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  have he := planeResidualFour_eq_of_mem_four (oppositeMarking F) hc t ht1 i hi
  exact (opposite_planeResidualFour_eq F t).symm.trans he

/-- The original source fixed subgroup has order four, from its explicit
identification in the marked coordinate geometry. -/
theorem involutionFour_card_of_not_fused (hcounts : MathieuFusionOrientation F)
    (t : G) (ht : t ∈ F.threeSpace) (ht1 : t ≠ 1) (hzt : ¬ IsConj z t) :
    Nat.card (involutionFour F t) = 4 := by
  obtain ⟨i, hi, _⟩ := (oriented_threeSpace_fours F hcounts).2.2 t ht ht1 hzt
  rw [involutionFour_eq_of_mem_four F hcounts t ht1 i hi]
  exact planeFour_card _ i

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
