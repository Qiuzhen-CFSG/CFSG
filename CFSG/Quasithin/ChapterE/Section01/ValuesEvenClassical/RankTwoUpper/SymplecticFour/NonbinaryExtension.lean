module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.GlobalDescent
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerQuotient
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry
public import CFSG.Quasithin.ClassicalModels

/-!
# Generation for the full nonbinary symplectic extension

The diagram kernel is generated at the field exponent by the proved
parabolic argument. Large elementary actors inside the kernel have ambient
tau inside it by the fixed-center rank calculation. An elementary actor
outside the kernel contains a swapping involution. Global graph descent and
the actual Suzuki centralizer quotient construct its external E-member.
Thus E-generation holds in the entire almost-simple two-extension, including
diagram actors, with no action or fixed-point premise remaining.

Source: Aschbacher–Smith E.1.14(1), printed p.214 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
open DiagramAutomorphisms Swapping Swapping.ExternalMembers
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The full source upper bound, including the genuine swapping extension. -/
theorem isEGenerated_nonbinary_extension {κ : GroupClass} (hG : IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ}
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (e : Sp F ≃* generalizedFitting G)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated f G := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  apply isEGenerated_of_diagramKernel_calculations hF hf e T hgen hq
  · exact diagramKernel_generation_of_preserving_bound hG e hq T hgen
      (fun J _ _ _ hJ S hS eJ hd => DiagramPreserving.isEGenerated hJ S hS hF hf eJ hd)
  · exact FixedRank.rank_le_of_swapping_centralizer hF hf e hq T
  · intro hodd A hA hAT hAH hr
    let := hA
    exact exists_external_member_of_normalized_calculations e T hgen hF hf hodd hq
      A hAT hAH hr (graph_power_cocycle_coboundary hF hodd)
      (normalized_quotient_calculations e T hgen hF hf hodd hq A)
      (CentralizerGeometry.normalized_hgeometry e T hF hf hodd hq A hAT)

/-- The marked projective model supplies the full symplectic source bound. -/
theorem isEGenerated_of_isPSp {κ : GroupClass} (hG : IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 1 < f)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hm : ClassicalGroup.IsPSp (generalizedFitting G) 2 (2^f)) :
    IsEGenerated f G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact isEGenerated_nonbinary_extension hG hF hf (EvenProjective.equiv.trans e.symm) T hgen

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
