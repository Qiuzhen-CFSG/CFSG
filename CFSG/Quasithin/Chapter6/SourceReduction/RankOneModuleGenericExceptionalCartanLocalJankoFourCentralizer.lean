module
public import Theory.GroupTheory.SylowCentralizerLine
public import Theory.GroupTheory.SolvableResidual.NormalizerLifting
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveFaithfulSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourMax4Residual

/-!
# Common involution-centralizer placement of the original J₄ residual

Even characteristic rules out a trivial two-core: a local A₅ would force
the full Sylow order to divide eight. The nontrivial core places the
original residual in an involution centralizer. The Sylow center has
order two, so this is the same centralizer as every line fixed by the
whole actor. The second involution class is excluded by the existing
local A₅ placement theorem, retaining simultaneous transport of R,S,K.

Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4
attribute [local irreducible] modelGroup matrixA matrixB

/-- The same local A₅ residual has nontrivial two-core. -/
theorem jankoFour_residual_core_ne_bot (S : Sylow 2 Model) (R : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : pCore 2 R ≠ ⊥ := by
  intro hc
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let e : R ≃* alternatingGroup (Fin 5) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans eR)
  have hd := ChapterA.Section03.SourceEmbeddings.AlternatingFive.sylow_card_dvd_of_evenCharacteristic
    S (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic S) hl hn e
  rw [Janko4.OuterReduction.OddIndex.ambient_sylow_card S] at hd
  norm_num at hd

private theorem line_centralizer_eq (S : Sylow 2 Model)
    (A : Subgroup Model) (ha : Nat.card A = 2)
    (hSA : (S : Subgroup Model) ≤ centralizer (A : Set Model))
    (z : Model) (hz : orderOf z = 2)
    (hSz : (S : Subgroup Model) ≤ centralizer ({z} : Set Model)) :
    centralizer (A : Set Model) = centralizer ({z} : Set Model) := by
  have hSz' : (S : Subgroup Model) ≤ centralizer (zpowers z : Set Model) := by
    rwa [zpowers_eq_closure, centralizer_closure]
  have he := (S.eq_center_image_of_card_two (sylow_center_card_two S) A ha hSA).trans
    (S.eq_center_image_of_card_two (sylow_center_card_two S) (zpowers z)
      (by rw [Nat.card_zpowers,hz]) hSz').symm
  rw [he,zpowers_eq_closure,centralizer_closure]

/-- Every Sylow-centralized line has a centralizer containing the same residual. -/
theorem jankoFour_common_line_centralizer (S : Sylow 2 Model) (R A : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (ha : Nat.card A = 2) (hSA : (S : Subgroup Model) ≤ centralizer (A : Set Model)) :
    R ≤ centralizer (A : Set Model) := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  obtain ⟨z,hz,hpair⟩ :=
    ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.involution_centralizer_placement_of_core
      S R hl hn eR (jankoFour_residual_core_ne_bot S R hl hn ⟨F,inferInstance,inferInstance,hF,⟨eF⟩⟩)
  rw [line_centralizer_eq S A ha hSA z hz (le_sup_right.trans hpair)]
  exact le_sup_left.trans hpair

/-- The actor, residual and full Sylow share one actual first-centralizer marking. -/
theorem jankoFour_common_first_centralizer (S : Sylow 2 Model) (R K A : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (ha : Nat.card A = 2) (hSK : (S : Subgroup Model) ≤ K)
    (hKA : K ≤ centralizer (A : Set Model)) :
    ∃ g : Model,
      R.map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer ∧
      (S : Subgroup Model).map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer ∧
      K.map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer := by
  have hc := jankoFour_residual_core_ne_bot S R hl hn he
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  obtain ⟨g,hR,hS⟩ :=
    ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.first_centralizer_placement
      S R hl hn eR hc
  let f := MulAut.conj g
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  have hPA : (P : Subgroup Model) ≤ centralizer (A.map f.toMonoidHom : Set Model) := by
    have hh := map_mono (f := f.toMonoidHom) (hSK.trans hKA)
    rwa [map_centralizer_equiv] at hh
  have hC := line_centralizer_eq P (A.map f.toMonoidHom)
    ((card_map_of_injective f.injective).trans ha) hPA a orderOf_a hS
  refine ⟨g,hR,hS,?_⟩
  have hh := map_mono (f := f.toMonoidHom) hKA
  rw [map_centralizer_equiv] at hh
  exact hh.trans hC.le
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
