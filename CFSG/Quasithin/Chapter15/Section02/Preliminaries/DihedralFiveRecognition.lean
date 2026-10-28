module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveParabolic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveMixedPair

/-!
# The two remaining recognition branches in marked-five 15.2.8

The faithful chief action identifies H/O₂(H) with one of four small actors.
The S₃ case supplies its literal (5,3) rank-one pair. The S₅ case uses the
actual two-residual to obtain an A₅ factor with original parabolic H; hence
it joins the S₅-wreath case in the same faithful D₁₀/Sz(2)--A₅ branch.
The remaining recognition theorems must exclude these two concrete pairs.

Source: Aschbacher--Smith, original 15.2.4 and 15.2.8, printed pp.1106--1110.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Complete reduction of the marked-five quotient alternatives to the two
actual outstanding rank-two recognition inputs. -/
theorem source_dihedral_five_HStar_recognition_alternatives
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
    (Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      ChapterF.Source.HypothesisF11
        ![caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
          (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)) ∨
    (∃ (A : Type u) (_ : Group A) (_ : Finite A)
      (L : Fin 2 → Subgroup A) (S : Subgroup A),
      IsQuasithin A ∧ ChapterF.Source.HypothesisF11 L S ∧
      S ⊔ ChapterF.Source.borel (L 0) S = S ∧
      (Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
        Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5))) := by
  have hsmall := source_dihedral_five_HStar_small_quotient
    hG T hempty hM hJ hu hmany hV l hp hd hH
  rcases hsmall with h3 | h3wr | h5 | h5wr
  · exact Or.inr (Or.inl ⟨h3,(source_dihedral_five_symmetricThree_pair
      hG T hempty hM hJ hu hmany hV l hp hd hH h3).1⟩)
  · exact Or.inl h3wr
  · right; right
    obtain ⟨hF,_,_,_,hB,heK⟩ := source_dihedral_five_symmetricFive_pair
      hG T hempty hM hJ hu hmany hV l hp hd hH h5
    exact ⟨G,inferInstance,inferInstance,_,T,hG.quasithin,hF,hB,
      source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd,heK⟩
  · exact Or.inr (Or.inr (source_HStar_wreath_five_faithful_mixed_pair
      hG T hempty hM hJ hu hmany hV (Or.inl ⟨l,5,m,hp,hd⟩) hH h5wr))
end CFSG.Quasithin.Chapter15.Section02
