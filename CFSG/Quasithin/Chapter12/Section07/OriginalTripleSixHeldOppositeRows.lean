module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeCatalogue
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenReduction

/-!
# The surviving actual opposite-normalizer rows

Apply the complete Sylow-sixteen six-space sieve to the faithful action of
N_G(W) on the same original W. The original dihedral map, kernel P,
opposite parabolic, U-offender and A5 fixed space are retained. The literal
offender subgroup has an A6, A7 or cubic A6 fitting component, or the actual
outer A6-C3 shape. This is source exhaustion, not ambient Held recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (π : T→*DihedralGroup 4) [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128) :
    let P := π.ker.map (T : Subgroup G).subtype
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
      let A := actionSubgroup ρ (U.subgroupOf I)
      let C := actionSubgroup ρ (L.subgroupOf I)
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ Nat.card R=256 ∧ Nat.card W=64 ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (U⊓W : Subgroup G)=16 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧ L≤I ∧ L.pCoreIn 2=W ∧
      centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
      (actionHom ρ).ker=W.subgroupOf I ∧
      Module.finrank (ZMod 2) (Additive W)=6 ∧
      (∀ Q : Sylow 2 (actionImage ρ), Nat.card Q=16) ∧
      Function.Injective τ ∧ τ.IsIrreducible ∧ pCore 2 (actionImage ρ)=⊥ ∧
      Nonempty (ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ)) ∧
      ChapterB.SourceInduction.AdequateAlternative (τ.comp (offenderSubgroup τ).subtype) ∧
      Nonempty (C≃*alternatingGroup (Fin 5)) ∧ Nat.card A=4 ∧ IsOffender τ A ∧
      A≤C ∧ C≤offenderSubgroup τ ∧ fixedSpace τ C≠⊥ ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P ∧
      let J := offenderSubgroup τ
      let F := generalizedFitting J
      (IsQuasisimple F ∧
        Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          (τ.comp J.subtype) F) ∧
        (Nonempty (F≃*alternatingGroup (Fin 6)) ∨
          Nonempty (F≃*alternatingGroup (Fin 7)) ∨
          Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
            Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)))) ∨
        Nonempty (ChapterB.OuterSixThreeShape J) := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨k,hk,S,W,hWe,hUR,hWR,hRT,hRc,hWc,hgen,hint,hIc,hTN,hLI,hLcore,
    hC,hcoreG,hker,hdim,hsyl,hf,hi,hcore,⟨cover⟩,hc,⟨ec⟩,hAc,hA,hAC,hCJ,hfix,hWP,hZW,hneq⟩ :=
    original_tripleSix_escaping_opposite_catalogue h structural D a t ht heven hout π hP
  let := hWe
  let Bk := B.map (MulAut.conj k).toMonoidHom
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let C := actionSubgroup ρ (L.subgroupOf I)
  have rows := ChapterB.SourceInduction.SylowSixteenSixSpace.rows_from_source
    τ hf hi hdim.le cover (fun Q => (hsyl Q).le) C hCJ ec hfix
  exact ⟨k,hk,S,W,hWe,hUR,hWR,hRT,hRc,hWc,hgen,hint,hIc,hTN,hLI,hLcore,
    hC,hcoreG,hker,hdim,hsyl,hf,hi,hcore,⟨cover⟩,hc,⟨ec⟩,hAc,hA,hAC,hCJ,hfix,hWP,hZW,hneq,rows⟩

end CFSG.Quasithin.Chapter12.Section07
