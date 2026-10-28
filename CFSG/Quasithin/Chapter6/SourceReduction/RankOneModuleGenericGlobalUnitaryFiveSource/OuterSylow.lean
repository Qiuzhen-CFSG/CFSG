module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.TorusSplitting
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.OuterSylow

/-!
# Saturated outer representatives on the original U₅(4) marking

Start with the splitting theorem's outer involution and the transported
original Sylow. Reselect it inside the same full extension with saturated
centralizers, then pull back by the very same middle equivalence. Its exact
inner-preimage equation proves that the new original element remains outside
S. Every endpoint, whole-middle and carrier/range equation is retained.

This discharges the local saturation requirement preceding F.4.37, printed
p.293 of refs/quasithin.pdf. Graph classification, root geometry and ambient
centralizer Sylow placement remain necessary for F.4.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))

-- The dependent marking statement checks in 19 seconds with this local budget;
-- the subgroup pullback is checked separately in five_outer_saturated_preimage.
set_option maxHeartbeats 400000 in
include d h hH hp hc in
/-- An original outer involution with full and inner native Sylow centralizers,
retaining the original full-normalizer marking and every endpoint equation. -/
theorem Preparation.unitaryFive_marked_outer_saturated
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (hST : sourceS L H < (T : Subgroup G)) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
      ∃ P : Sylow 2 r.extension.middle,
        (P : Subgroup r.extension.middle) =
          ((T : Subgroup G).subgroupOf D).map F.middle.toMonoidHom ∧
        (P : Subgroup r.extension.middle) ⊓ (ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier).comap r.extension.middle.subtype =
          ((sourceS L H).subgroupOf D).map F.middle.toMonoidHom ∧
        ∃ t : D, t.val ∈ (T : Subgroup G) ∧ orderOf t=2 ∧
          t.val ∉ sourceS L H ∧ F.middle t ∈ (P : Subgroup r.extension.middle) ∧
          (F.middle t).val ∉ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ∧
          let j := inclusion (inf_le_left.trans r.extension.left_le :
            r.extension.middle ≤ r.extension.carrier)
          (∃ Q : Sylow 2 (centralizer ({j (F.middle t)} : Set r.extension.carrier)),
            (Q : Subgroup _).map (centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                centralizer ({j (F.middle t)} : Set r.extension.carrier)) ∧
          (∃ R : Sylow 2 (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            (R : Subgroup _).map (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) := by
  have hdata := Preparation.unitaryFive_marked_sylow_split
    (G := G) (T := T) (L := L) (W := W) (H := H) (A := A) (C := C) (n := n)
    d h hH hp U hc r
  obtain ⟨a,ell,F,heq⟩ := hdata
  obtain ⟨h0,h1,hD,hE,hleft,hright,hmiddle,hrest⟩ := heq
  obtain ⟨P,hP,hinner,houter⟩ := hrest
  obtain ⟨x,_,hxo,_,hxi⟩ := houter hST
  refine ⟨a,ell,F,h0,h1,hD,hE,hleft,hright,hmiddle,P,hP,hinner,?_⟩
  exact five_outer_saturated_preimage U r.extension F.middle
    ((T : Subgroup G).subgroupOf _) ((sourceS L H).subgroupOf _) P hP hinner x hxo hxi

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
