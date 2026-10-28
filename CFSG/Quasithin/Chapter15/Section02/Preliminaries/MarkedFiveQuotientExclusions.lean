module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveFinalExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveRecognition
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SourceSmallParabolic

/-!
# Applying the mixed-pair exclusion to the original H-star catalogue

The single S₅ quotient supplies the same small-solvable / A₅ pair as the
wreath-five quotient, using its actual two-residual as the second factor.
The proved mixed-pair exclusion therefore removes both five-letter entries
from marked-five 15.2.8. The remaining single S₃ entry retains its literal
rank-two pair; excluding that separate branch gives the required S₃ wreath
quotient. The general small-source assembly also no longer needs a
marked-five wreath callback.

Source: Aschbacher--Smith, original 15.2.4 and 15.2.8,
printed pp.1106--1110; DGS (1985), (11.4)--(11.8), pp.171--176.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The single S₅ H-star quotient is impossible in the original marked-five
configuration; its actual two-residual gives the excluded A₅ factor. -/
theorem ChosenSmallSource.marked_five_HStar_not_symmetricFive
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  intro he
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨hF,_,_,_,_,ha⟩ := source_dihedral_five_symmetricFive_pair
    h.ambient T h.empty h.maximal h.centralizing h.partner h.many h.prepared l hp hd hH he
  exact Assembly.small_solvable_a5_exclusion hF
    (source_dihedral_five_join_quotient h.ambient T h.empty h.maximal h.centralizing
      h.partner h.many h.prepared l hp hd) ha

/-- After excluding both five-letter entries, the marked-five source has
the required wreath quotient or the literal remaining S₃ rank-two pair. -/
theorem ChosenSmallSource.marked_five_HStar_quotient_alternatives
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
    (Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      HypothesisF11 ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)) := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  rcases source_dihedral_five_HStar_recognition_alternatives h.ambient T h.empty
    h.maximal h.centralizing h.partner h.many h.prepared l hp hd hH with hwr | h3 | hmix
  · exact Or.inl hwr
  · exact Or.inr h3
  · obtain ⟨A,hA,hfin,L,S,_,hF,_,hq,ha⟩ := hmix
    let := hA
    let := hfin
    exact (Assembly.small_solvable_a5_exclusion hF hq ha).elim

/-- Marked-five 15.2.8 now requires only its separate single-S₃ exclusion;
both five-letter recognition branches are discharged internally. -/
theorem ChosenSmallSource.HStar_wreath_of_marked_five_of_not_symmetricThree
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hthree : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  rcases h.marked_five_HStar_quotient_alternatives hd hH with hwr | h3
  · exact hwr
  · exact (hthree h3.1).elim

/-- The general small-source quotient assembly needs only its actual residual
uniqueness and the two single symmetric-group exclusions. -/
theorem ChosenSmallSource.HStar_wreath_of_single_exclusions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hthree : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hfive : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  apply h.HStar_wreath_of_exclusions hunique ?_ hH hthree hfive
  let := h.prepared.elementary
  intro l hd H hH
  exact h.HStar_not_wreath_five hH

end CFSG.Quasithin.Chapter15.Section02
