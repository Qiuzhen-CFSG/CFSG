module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles
/-!
# The original C.1.19 reduction of the selected universal pair

One intrinsic pair is selected in the characteristic Baumann base before
all finite local overgroups. Intersecting its first image with the original
ambient center preserves characteristicity and nontriviality, and the
literal subgroup-of/image maps transfer all three C.1.18 alternatives.
The inputs are exactly Campbell Theorem A and the residual-layer block
recognition used by Selection, with their final source producers independent.

Source: Aschbacher–Smith C.1.18–19, printed pp.126–127.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v
variable {S : Type u} [Group S] [Finite S]

theorem exists_reducedPair_of_campbell_inputs
    (hp : IsPGroup 2 S) (B : Subgroup S) [B.Characteristic] [Nontrivial B]
    (hB : IsBaumannFixed B)
    (hA : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      (∀ a : MulAut B, ((Campbell.V H).comap e |>.map a.toMonoidHom).map e ≤ pCore 2 H) →
      ∀ a : MulAut B,
        ⁅Campbell.J (⊤ : Subgroup H),((Campbell.F H).comap e |>.map a.toMonoidHom).map e⁆ ≤ Campbell.F H)
    (hblock : ∀ (H : Type v) [Group H] [Finite H] (e : B →* H), InLocalClass e →
      ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H → BlockAlternative H) :
    ∃ C : RankOneCharacteristicPair B,
      ∀ (H : Type v) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives (C.first.subgroupOf B) C.second e := by
  obtain ⟨D,hD⟩ := exists_universal_pair_of_campbell_inputs (hp.to_subgroup B) hB hA hblock
  let : D.first.Characteristic := D.first_characteristic
  let : D.second.Characteristic := D.second_characteristic
  let C := glaubermanNiles_reducePair hp B D.first D.second D.first_ne_bot
    D.second_ne_bot D.first_le_omegaCenter
  refine ⟨C,?_⟩
  intro H _ _ e he
  have h := glaubermanNiles_reduction_alternatives B D.first D.second e
    (BlockAlternative H) (hD H e he)
  change Alternatives ((centerRestriction B D.first).subgroupOf B) D.second e
  simpa only [Alternatives,image_subgroupOf_subtype] using h
end CFSG.Quasithin.ChapterC.GlaubermanNiles
