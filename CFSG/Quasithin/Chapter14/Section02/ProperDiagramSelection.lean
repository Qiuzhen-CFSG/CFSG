module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelGeometry
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramHallFixer
/-!
# Selecting the original diagram residual

The actual source DiagramModel supplies a selected perfect parabolic
residual with its PSL₂ quotient, index-two Sylow normalizer, Sylow
intersection, and original two-core containment. The derived symplectic
mark is transported by its canonical equivalence with the full group
only after the field order is greater than two.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

theorem source_diagram_residual_selection
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : DiagramModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) f) :
    ∃ L : Subgroup H, L ≤ K ∧ Group.IsPerfect L ∧
      ¬L ≤ ChapterB.minimalParabolicMax T hP ∧ L ⊔ (T : Subgroup H) = ⊤ ∧
      let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
      S.relIndex (T : Subgroup H) = 2 ∧ Chapter1.IsSylowIn 2 (S ⊓ L) L ∧
      pCore 2 H ≤ S ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^f ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let M := ChapterB.minimalParabolicMax T hP
  rcases hm with ⟨F,hfield,hfin,hchar,_,hcard,e,he,hmove⟩ |
      ⟨F,hfield,hfin,hchar,_,hcard,e,he,hmove⟩
  · let L := markedParabolicResidual M K e (Matrix.PSL3.LinearThree.pointParabolic F)
    obtain ⟨hperf,hout,hgenL,hi,hsyl,hcore,hq⟩ :=
      source_linear_diagram_residual_geometry T hP hs K hK hqK hgen hcard hf e he hmove
    exact ⟨L,markedParabolicResidual_le M K e _,hperf,hout,hgenL,hi,hsyl,hcore,
      F,hfield,hfin,hchar,hcard,hq⟩
  · have hq : 2 < Nat.card F := by
      rw [hcard]
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hf
    let d := Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq
    have hd : d.toMonoidHom = (Sp4Derived F).subtype := by
      apply MonoidHom.ext
      intro g
      exact Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two_apply hq g
    have hmap (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) :
        (P.subgroupOf (Sp4Derived F)).map d.toMonoidHom = P := by
      rw [hd,map_subgroupOf_eq_of_le]
      let := Theory.SpecificGroups.SymplecticFour.perfect_of_card_gt_two hq
      rw [show Sp4Derived F = ⊤ from Group.IsPerfect.commutator_eq_top]
      exact le_top
    let eF := e.trans d
    have heF : (componentOverlap M K).map eF.toMonoidHom =
        Theory.SpecificGroups.SymplecticFour.borel := by
      change (componentOverlap M K).map (d.toMonoidHom.comp e.toMonoidHom) = _
      rw [← map_map,he,hmap]
    have hmF : MovesDiagram M K (T : Subgroup H) eF
        Theory.SpecificGroups.SymplecticFour.pointParabolic
        Theory.SpecificGroups.SymplecticFour.planeParabolic := by
      obtain ⟨a,ha,hm⟩ := hmove
      refine ⟨a,ha,?_⟩
      have ha' : MulAut.congr d (MulAut.congr e a) = MulAut.congr eF a := by
        ext g
        simp only [MulAut.congr_apply,MulEquiv.trans_apply]
        rfl
      intro hp
      apply hm
      constructor
      · apply (ProperDiagramHallFixer.preservesParabolicClass_congr_iff d _ _).mp
        rw [hmap,ha']
        exact hp.1
      · apply (ProperDiagramHallFixer.preservesParabolicClass_congr_iff d _ _).mp
        rw [hmap,ha']
        exact hp.2
    let L := markedParabolicResidual M K eF
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
    obtain ⟨hperf,hout,hgenL,hi,hsyl,hcore,hqL⟩ :=
      source_symplectic_diagram_residual_geometry T hP hs K hK hqK hgen hcard hf eF heF hmF
    exact ⟨L,markedParabolicResidual_le M K eF _,hperf,hout,hgenL,hi,hsyl,hcore,
      F,hfield,hfin,hchar,hcard,hqL⟩
end CFSG.Quasithin.Chapter14.Section02
