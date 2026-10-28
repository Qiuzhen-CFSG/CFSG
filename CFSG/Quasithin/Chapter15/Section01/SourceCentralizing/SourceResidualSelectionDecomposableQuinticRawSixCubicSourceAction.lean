module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Full
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction
public import Theory.Representation.HexacodeAction.NaturalConjugation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction

/-!
# Natural action on the retained central-six quotient

For the actual B.5 moved-section conclusion, a component whose center has
order dividing three and whose central quotient is A₆ has natural ambient
conjugation action. In the simple case this is the binary natural module
normalizer; in the cubic case the full moved hexacode coordinates give
the full ambient embedding. Neither proof reconstructs the original core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

private theorem simple_source_natural
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) [C.Normal]
    (hCJ : C ≤ offenderSubgroup ρ)
    (c : ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp (offenderSubgroup ρ).subtype)
      (C.subgroupOf (offenderSubgroup ρ)))
    (hz : center C = ⊥) (e : (C ⧸ center C) ≃* alternatingGroup (Fin 6)) (g : D) :
    Hexacode.centralSixAction C e g ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  let b : (C ⧸ center C) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let a : C ≃* alternatingGroup (Fin 6) := b.symm.trans e
  let s := MovedSection.ofNormal ρ C
  have hn := (AlternatingSixReconstruction.Exceptional.Exhaustion.natural_of_layer_source
    ρ C hCJ c a s).2
  have hh := AlternatingSixReconstruction.Exceptional.Exhaustion.normal_action_natural
    s.action C hn a g
  have he : Hexacode.centralSixAction C e g = MulAut.congr a (MulAut.conjNormal g) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y,rfl⟩ := a.surjective x
    have ha (y : C) : a y = e (QuotientGroup.mk' (center C) y) := rfl
    rw [ha,Hexacode.centralSixAction_mk]
    change e (QuotientGroup.mk' (center C) (MulAut.conjNormal g y)) =
      a (MulAut.conjNormal g (a.symm (a y)))
    rw [a.symm_apply_apply]
    rfl
  exact he ▸ hh

/-- A concrete B.5 conclusion forces natural action on the full central-six
quotient, including the case where the cubic center acts faithfully. -/
theorem raw_six_source_action_natural
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) [C.Normal] [IsQuasisimple C]
    (hquot : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥)
    (hCJ : C ≤ offenderSubgroup ρ)
    (c : ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp (offenderSubgroup ρ).subtype)
      (C.subgroupOf (offenderSubgroup ρ)))
    (hc : Nat.card (center C) ∣ 3)
    (e : (C ⧸ center C) ≃* alternatingGroup (Fin 6)) (g : D) :
    Hexacode.centralSixAction C e g ∈ _root_.AlternatingSix.ShadowLocal.natural := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hc with hz | hz
  · exact simple_source_natural ρ C hCJ c ((center C).eq_bot_iff_card.mpr hz) e g
  · let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = center C := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨a,_⟩ := Hexacode.triple_cover_equiv q hq hk.le (hk ▸ hz)
    let b := (subgroupOfEquivOfLe hCJ).trans a
    obtain ⟨hi,hfaith,hirr,_,⟨htriple⟩,_⟩ := CoveredSixModels.source_tripleSix _ c b
    let m : CoveredSixModels.ActionData ρ C :=
      ⟨hCJ,c,hi,hfaith,hirr,htriple,CoveredSixModels.source_invariant_split _ c b,
        CoveredSixModels.source_central_eq_bot _ c b,CoveredSixModels.source_moved_finrank _ c b⟩
    obtain ⟨φ,d,_,hφ,_,hφd,_⟩ := m.exists_full_model a hquot hcore
    have himage : C.map φ = Atlas.Codes.hexSign.ker := by
      apply le_antisymm
      · rintro y ⟨x,hx,rfl⟩
        rw [hφd ⟨x,hx⟩]
        exact (d ⟨x,hx⟩).property
      · intro y hy
        obtain ⟨x,hxy⟩ := d.surjective ⟨y,hy⟩
        exact ⟨x,x.property,(hφd x).trans (congrArg Subtype.val hxy)⟩
    exact Hexacode.centralSixAction_mem_natural C e φ hφ himage g

end CFSG.Quasithin.Chapter15.Section01
