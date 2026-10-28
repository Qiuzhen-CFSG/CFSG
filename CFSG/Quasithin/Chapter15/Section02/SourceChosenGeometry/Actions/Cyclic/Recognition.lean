module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Recognition.Exclusions
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralResidual
public import Theory.GroupTheory.FittingFiveModels

/-!
# Recognition of the surviving cyclic chosen actions

The cubic-plane obstruction excludes the S₃ × C₃ and cyclic-fifteen Fitting
rows. In the remaining five row, the original DihedralMarking supplies the
normal five inside J-hat. The actual Fitting subgroup equals that five;
solvability and self-centralization recognize the whole image as D₁₀ or
Sz(2). The S₃ row and the original J-hat marking are retained.

Source: Aschbacher--Smith 15.2.13(1)(i), printed pp.1111--1112,
refs/quasithin.pdf. The only assumptions are the preceding source inputs.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The preceding source conclusions recognize all surviving non-Omega models. -/
theorem Preceding.restricted_models {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) : RestrictedModels h := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let ρ := imageRepresentation M V h.prepared.normalized
  let K := Jhat ρ
  let : K.Normal := Jhat_normal ρ
  rcases d.alternatives with h3 | ⟨_,h18⟩ | hω | ⟨hK,_,_⟩
  · exact Or.inl h3
  · exact (d.not_symmetric_three_cubic h18).elim
  · exact (d.non_omega hω).elim
  · refine Or.inr ⟨hK,?_⟩
    have hcK : Nat.card K = 10 :=
      (Nat.card_congr hK.some.toEquiv).trans DihedralGroup.nat_card
    have hF : Nat.card (fittingSubgroup D) = 5 := by
      rcases h.small with ⟨l,p,m,hpm,hd⟩ | hω
      · have hm : m = 2 := by
          have hh := hd.dimension
          rw [h.finrank_eq_four] at hh
          omega
        subst m
        rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
        · have hc : Nat.card K = 6 :=
            (Nat.card_congr hd.dihedral.some.toEquiv).trans DihedralGroup.nat_card
          omega
        · let P := l.kernel.map K.subtype
          have hp : PrimeDimensionOptions 5 2 :=
            (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
          have hmks := hd.ambient_marks K hp
          let : P.Normal := hmks.2.2.2.1
          rcases SmallBinaryFiveOvergroup.fitting_alternatives ρ
            (imageRepresentation_injective _ _ _) h.finrank_eq_four P hmks.2.2.1 with he | he
          · exact he ▸ hmks.2.2.1
          · exact (d.not_fitting_fifteen he).elim
      · exact (d.non_omega hω).elim
    have htwo : 2 ∣ Nat.card D := by
      have hd := K.card_subgroup_dvd_card
      rw [hcK] at hd
      exact (by decide : 2 ∣ 10).trans hd
    exact small_models_of_fitting_card_five
      (source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
        h.prepared.normalized h.prepared.le_local) hF htwo
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
