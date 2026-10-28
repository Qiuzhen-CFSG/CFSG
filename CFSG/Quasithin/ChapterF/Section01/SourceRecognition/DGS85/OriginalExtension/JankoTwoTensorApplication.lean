module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoParabolics
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TensorApplication

/-!
# Hall–Janko restoration in the original tensor consumer

The reduced J₂ row yields the bound on the same ambient Sylow T, in either
orientation. For a marked orientation it also identifies the original
H-core, the original AT-core and the entire BT order. The actual tensor
model has |T| > 256, so the restored bound excludes this reduced row from
its zero-core branch. No original Aut(J₂) recognition is assumed.

Reduced parabolic recognition and construction of the cubic factor remain
explicit source inputs. This removes the original-versus-reduced premise
of the mixed size consumer, not the remaining source classification.

Source: Aschbacher–Smith, original 9.3.1, printed pp.732–733, using
F.1.11–12, pp.262–264, and DGS (1985), (15.3), pp.229–231.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- A genuine reduced Hall–Janko comparison supplies the original tensor
Sylow bound, in either orientation and without a restored Aut(J₂) premise. -/
theorem mixed_cubic_factor_size_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (he : ExceptionalModels.ParabolicModel .j2
        (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∨
      ExceptionalModels.ParabolicModel .j2
        (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)).reverse) :
    Nat.card T ≤ 256 := by
  obtain ⟨hf,_,_,_,_,_,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hs := (JankoTwo.original_profile_of_parabolicModels hf he).1
  rcases hs with hs | hs <;> omega

/-- The marked first reduced endpoint controls both the original residual
core and the literal original H-core, as required by the mixed consumer. -/
theorem mixed_cubic_factor_core_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam) :
    twoCore H = twoCore ((pResidual 2 H).map H.subtype) ∧
    Nat.card (pCore 2 H) = 32 ∧
    Nat.card (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)) = 64 ∧
    (Nat.card T = 128 ∨ Nat.card T = 256) ∧
    (Nat.card (B ⊔ (T : Subgroup G) : Subgroup G) = 384 ∨
      Nat.card (B ⊔ (T : Subgroup G) : Subgroup G) = 768) := by
  obtain ⟨hf,_,_,_,hb,hp,hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hk := JankoTwo.original_core_eq_local hf 0 e.left
  have hc := JankoTwo.original_core_card hf 0 e.left
  have hd := JankoTwo.original_second_core_card hf 1 e.right
  have hs := JankoTwo.original_sylow_card_cases hf 0 e.left
  have hbcard := JankoTwo.original_borel_card_cases hf 0 e.left e.middle
  rw [hp] at hk hc
  rw [hq] at hd
  rw [hb] at hbcard
  exact ⟨hk,hc,hd,hs,hbcard⟩

/-- The actual tensor group has Sylow order greater than 256, so this
restoration excludes the reduced Hall–Janko branch of the zero-core argument. -/
theorem not_reduced_j2_of_mixed_cubic_factor
    {eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    (m : SourceA5TensorModel D eL)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    ¬ (ExceptionalModels.ParabolicModel .j2
        (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∨
      ExceptionalModels.ParabolicModel .j2
        (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)).reverse) := by
  intro he
  exact (not_lt_of_ge
    (mixed_cubic_factor_size_of_reduced_j2 hH eK A B U hAB hBA hBK hB3 hU hzero he))
      (m.sylow_card_gt_256 m.sylow_not_normalizes_component)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
