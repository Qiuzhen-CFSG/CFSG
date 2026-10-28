module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldKernelImage
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenCubicReduction

/-!
# The actual opposite normalizer has a cubic A6 fitting component

Apply the proved six-space and fixed-line exclusions to the literal B.5
source attached to N_G(W). The original dihedral epimorphism, extraspecial
kernel P, opposite plane W, center z and normalizer Y all remain unchanged.
The ordinary A6, A7 and outer A6--C3 rows are eliminated; the surviving
actual fitting component has cubic center and A6 central quotient. This
does not yet identify the full z-centralizer with a marked S4 normalizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_cubic_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤Y ∧ Nat.card P=128 ∧ IsExtraspecial 2 P ∧
      Nonempty (P≃*DihedralCentralProductThree.Model) ∧
      Nat.card (U⊓P : Subgroup G)=16 ∧ Nat.card ((U.subgroupOf T).map π)=4 ∧
      ∃ z : G, orderOf z=2 ∧ z∈U ∧
        centerIn P=zpowers z ∧ centerIn (T : Subgroup G)=zpowers z ∧
        centralizer (P : Set G)=zpowers z ∧ Y≤centralizer ({z} : Set G) ∧
        normalizer (K : Set G)⊓centralizer ({z} : Set G)≤Y ∧
        let H := centralizer ({(t:G)} : Set G)
        let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
        let B := conjugateSpanBy Lt H
        ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
          ∃ hWe : IsElementaryAbelian 2 W, letI := hWe
          let Bk := B.map (MulAut.conj k).toMonoidHom
          let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
          let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
          let I := normalizer (W : Set G)
          let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
          let τ := imageRepresentation ρ
          let A := actionSubgroup ρ (P.subgroupOf I)
          let C := actionSubgroup ρ (L.subgroupOf I)
          let J := offenderSubgroup τ
          let F := generalizedFitting J
          U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ U⊔W=R ∧
          Nat.card W=64 ∧ (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
          centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
          (actionHom ρ).ker=W.subgroupOf I ∧
          Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
          (U⊓P : Subgroup G)≠W⊓P ∧
          Module.finrank (ZMod 2) (Additive W)=6 ∧
          (∀ Q : Sylow 2 (actionImage ρ), Nat.card Q=16) ∧
          Function.Injective τ ∧ τ.IsIrreducible ∧
          Nonempty (C≃*alternatingGroup (Fin 5)) ∧ C≤J ∧ fixedSpace τ C≠⊥ ∧
          IsElementaryAbelian 2 A ∧ Nat.card A=8 ∧
          Module.finrank (ZMod 2) (fixedSpace τ A)=1 ∧
          (∀ v : Additive W, v∈fixedSpace τ A ↔ (v.toMul:G)∈zpowers z) ∧
          IsQuasisimple F ∧
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (τ.comp J.subtype) F) ∧
          Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
          Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,rows⟩ :=
    original_tripleSix_escaping_kernel_image h structural D a t ht heven hout
  let := hWe
  let P := π.ker.map (T : Subgroup G).subtype
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let A := actionSubgroup ρ (P.subgroupOf I)
  let J := offenderSubgroup τ
  let F := generalizedFitting J
  have cubic : IsQuasisimple F ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (τ.comp J.subtype) F) ∧
      Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
      Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)) := by
    rcases rows with ⟨hq,⟨c⟩,⟨e⟩ | ⟨e⟩ | hcubic⟩ | ⟨c⟩
    · obtain ⟨e⟩ := e
      exact (ChapterB.SourceInduction.SylowSixteenSixSpace.not_ordinary_six_source
        τ hf hi hdim hq c e).elim
    · obtain ⟨e⟩ := e
      let : IsElementaryAbelian 2 A := hAe
      exact (ChapterB.SourceInduction.SylowSixteenSixSpace.not_seven_source
        τ hf hi hdim hq c e A (IsElementaryAbelian.isPGroup 2 A) hAd).elim
    · exact ⟨hq,⟨c⟩,hcubic⟩
    · obtain ⟨c⟩ := c
      exact (ChapterB.SourceInduction.SylowSixteenSixSpace.not_outer_six_three_source
        τ hf hi hdim c).elim
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,cubic⟩

end CFSG.Quasithin.Chapter12.Section07
