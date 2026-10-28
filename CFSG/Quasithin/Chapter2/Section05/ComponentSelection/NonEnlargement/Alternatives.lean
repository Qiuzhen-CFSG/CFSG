module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.SmallModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SpecialLinear
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
/-!
# The ordinary component alternative in the original source normalizer

Retain the local C-component condition for the original full Sylow.
The genuine 2.5.2 catalogue of the ordinary containing component reduces
all strict inclusions to the M₁₁ row: Bender and even rank-two models
have no proper nonsolvable Sylow overgroups, PSL₃(3) is minimally simple,
and the prime-linear proper row would make the original component A₅.
This is the component-or-M₁₁ part of 2.5.6; the additional A₆/M₁₀
identifications belong to its exceptional-branch refinement.
Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]

theorem component_or_mathieu_containing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {M H K S T E : Subgroup G} {z : G}
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀:Subgroup G)≤M)
    (hunique : ∀ N:Subgroup G, IsMaximalTwoLocal N → (T₀:Subgroup G)≤N → N=M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H=K⊔S)
    (hb : ¬ClassificationModels.IsBenderModel K)
    (hE:E≠⊥) (hEC:E≤S⊓centralizer (K:Set G)) (hSE:S≤normalizer (E:Set G)) :
    IsComponentIn K (normalizer (E:Set G)) ∨
      ∃ C : Subgroup G, IsComponentIn C (normalizer (E:Set G)) ∧ K ≤ C ∧
        Nonempty (C ≃* Sporadic.Mathieu.M11) := by
  let J := normalizer (E:Set G)
  have hHJ : H ≤ J := normalizes_centralizer_subgroup hgen hEC hSE
  have hKJ := hK.1.trans hHJ
  obtain ⟨C,hC,hKC⟩ := exists_containing_component hG T₀ hM hT₀M hunique d hK hgen hE hEC hSE
  obtain ⟨hJ,⟨P,hP⟩,_⟩ := centralizer_subgroup_normalizer d hgen hE hEC hSE
  obtain ⟨cC⟩ := exists_setup_of_same_sylow T₀ hM hT₀M hunique d hJ P hP hC
  let B := K.subgroupOf J
  let L := C.subgroupOf J
  let eB : B ≃* K := subgroupOfEquivOfLe hKJ
  let eL : L ≃* C := subgroupOfEquivOfLe hC.1
  let : IsQuasisimple K := hK.quasisimple
  let : IsQuasisimple C := hC.quasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB.symm
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  have hlocal : K ∈ localCComponents S := by
    change (K.subgroupOf (K⊔S)).IsCComponent
    rw [←hgen]
    exact hK.2.isCComponent
  have hB : B ∈ localCComponents P := by
    have hh := local_restrict (L:=J) hlocal hKJ
    have hSP : S.subgroupOf J=(P:Subgroup J) := by
      apply map_injective J.subtype_injective
      rw [map_subgroupOf_eq_of_le hSE]
      exact hP.symm
    rwa [hSP] at hh
  have hL : L.IsCComponent := hC.2.isCComponent
  have hBL : B ≤ L := subgroupOf_mono J hKC
  have finish (he : B=L) : IsComponentIn K J := by
    have hh := congrArg (Subgroup.map J.subtype) he
    change (K.subgroupOf J).map J.subtype=(C.subgroupOf J).map J.subtype at hh
    rw [map_subgroupOf_eq_of_le hKJ, map_subgroupOf_eq_of_le (show C≤J from hC.1)] at hh
    exact hh.symm ▸ hC
  by_cases hbc : ClassificationModels.IsBenderModel C
  · apply Or.inl; apply finish
    apply eq_of_solvable_sylow_overgroups P hB hL hBL
    exact isSolvable_proper_sylow_overgroup_of_equiv eL
      (bender_solvable_proper_sylow_overgroup hbc)
  have models := MathieuSourceSetup.nonBender_model cC hG localC129Input_knownSimple hempty hbc
  rcases models with hs | hl | (hsmall | hsmall) | hp
  · left; apply finish
    apply eq_of_proper_sylow_fitting_bound P hB hL hBL
    apply properSylowFittingBound_of_equiv eL
    obtain ⟨F,_,_,m,hm,hF,⟨e⟩⟩ := hs
    by_cases hm1 : m=1
    · let a := Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      let b := Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F:=F) (by simpa [hm1] using hF)
      apply properSylowFittingBound_of_equiv (e.trans (b.trans a.symm))
      exact properSylowFittingBound_binary_symplectic_derived
    · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hcard : 2<Nat.card F := by
        rw [hF]
        calc 2=2^1 := by norm_num
             _<2^m := Nat.pow_lt_pow_right (by decide) (by omega)
      apply properSylowFittingBound_of_equiv (e.trans
        (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hcard))
      exact properSylowFittingBound_sp_four F m (by omega) hF
  · left; apply finish
    apply eq_of_proper_sylow_fitting_bound P hB hL hBL
    apply properSylowFittingBound_of_equiv eL
    obtain ⟨F,_,_,m,hm,hF,⟨e⟩⟩ := hl
    exact properSylowFittingBound_of_centralQuotient e
      (ChapterC.RankOne.ChiProduct.ComponentSource.linearThree_properSylowFittingBound F hm hF)
  · left; apply finish
    apply eq_of_solvable_sylow_overgroups P hB hL hBL
    obtain ⟨e⟩ := hsmall
    exact isSolvable_proper_sylow_overgroup_of_equiv (eL.trans e)
      (fun _ U _ hU => Matrix.PSL3Three.isSolvable_of_ne_top U hU)
  · exact Or.inr ⟨C,hC,hKC,hsmall⟩
  · left; apply finish
    by_contra he
    obtain ⟨r,hr,hrlarge,⟨e⟩⟩ := hp
    let : Fact r.Prime := ⟨hr.1⟩
    obtain ⟨_,⟨a⟩⟩ := proper_primePSL2_models P hB hL hBL he hr.1 (hr.1.odd_of_ne_two (by omega))
      ⟨ZMod r,inferInstance,inferInstance,Nat.card_zmod r,⟨eL.trans e⟩⟩
    exact hb (.linear 2 (by decide)
      ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
       ⟨eB.symm.trans (a.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm)⟩⟩)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
