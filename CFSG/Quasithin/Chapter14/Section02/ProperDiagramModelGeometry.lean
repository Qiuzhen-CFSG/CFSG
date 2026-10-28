module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramPairIndex
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramGeometry
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelResidual
/-!
# Source geometry of the selected diagram parabolic residual

Both concrete diagram families supply the same actual residual geometry:
perfectness, noncontainment in the original maximal subgroup, generation
with the prescribed Sylow, an index-two normalizer, the Sylow intersection,
and containment of the original two-core. Its intrinsic two-core quotient
is the genuine PSL₂ group over the same field.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

theorem source_linear_diagram_residual_geometry
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2^f) (hf : 1 < f)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (ChapterB.minimalParabolicMax T hP) K).map
      e.toMonoidHom = Matrix.PSL3.LinearThree.borel F)
    (hmove : MovesDiagram (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H)
      e (Matrix.PSL3.LinearThree.pointParabolic F)
      (Matrix.PSL3.LinearThree.lineParabolic F)) :
    let L := markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
      (Matrix.PSL3.LinearThree.pointParabolic F)
    let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
    Group.IsPerfect L ∧ ¬L ≤ ChapterB.minimalParabolicMax T hP ∧
      L ⊔ (T : Subgroup H) = ⊤ ∧ S.relIndex (T : Subgroup H) = 2 ∧
      Chapter1.IsSylowIn 2 (S ⊓ L) L ∧
      pCore 2 H ≤ S ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let M := ChapterB.minimalParabolicMax T hP
  let P := Matrix.PSL3.LinearThree.pointParabolic F
  let Q := Matrix.PSL3.LinearThree.lineParabolic F
  let B := Matrix.PSL3.LinearThree.borel F
  let L := markedParabolicResidual M K e P
  let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ f)
  have hnot : ¬L ≤ M := originalLinearParabolicResidual_not_le M K hcard hf e he
  have hpair (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
      (ha : B.map a.toMonoidHom = B) :
      (P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∨
      (P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P) :=
    invariant_pair_of_both_images P Q (Matrix.PSL3.LinearThree.projective_parabolics_ne F)
      a (Matrix.PSL3.LinearThree.point_parabolic_map_pair_of_borel F a ha)
      (Matrix.PSL3.LinearThree.line_parabolic_map_pair_of_borel F a ha)
  refine ⟨markedParabolicResidual_perfect M K e P,hnot,
    markedParabolicResidual_sup_sylow T hP K e P hnot,?_,?_,?_,?_⟩
  · exact markedParabolicResidual_index_two_of_movesDiagram M K _
      (ChapterB.minimalParabolicMax_spec T hP).2 e P Q B he
      (Matrix.PSL3.LinearThree.projective_parabolics_inf F) hnot hpair hmove
  · exact markedParabolicResidual_sylow_intersection T M K
      (ChapterB.minimalParabolicMax_spec T hP).2 e he
      ((Matrix.PSL3.LinearThree.projective_parabolics_inf F) ▸ inf_le_left)
  · exact original_twoCore_le_markedResidual_normalizer T hP K e P
  · exact ⟨originalLinearParabolicResidualCoreEquiv T hP hs K hK hqK hgen h4 e⟩

theorem source_symplectic_diagram_residual_geometry
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hcard : Nat.card F = 2^f) (hf : 1 < f)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (componentOverlap (ChapterB.minimalParabolicMax T hP) K).map
      e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel (F := F))
    (hmove : MovesDiagram (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H)
      e (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
      (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F))) :
    let L := markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e
      (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
    let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
    Group.IsPerfect L ∧ ¬L ≤ ChapterB.minimalParabolicMax T hP ∧
      L ⊔ (T : Subgroup H) = ⊤ ∧ S.relIndex (T : Subgroup H) = 2 ∧
      Chapter1.IsSylowIn 2 (S ⊓ L) L ∧
      pCore 2 H ≤ S ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let M := ChapterB.minimalParabolicMax T hP
  let P := Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)
  let Q := Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)
  let B := Theory.SpecificGroups.SymplecticFour.borel (F := F)
  let L := markedParabolicResidual M K e P
  let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
  have hPQ : P ≠ Q := by
    intro heq
    have hh := Theory.SpecificGroups.SymplecticFour.parabolics_sup_eq_top (F := F)
    change P ⊔ Q = ⊤ at hh
    rw [heq,sup_idem] at hh
    exact Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.planeParabolic_isCoatom.ne_top hh
  have hnot : ¬L ≤ M := originalSymplecticParabolicResidual_not_le M K hcard hf e he
  have hpair (a : MulAut (Theory.SpecificGroups.SymplecticFour.Sp F))
      (ha : B.map a.toMonoidHom = B) :
      (P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∨
      (P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P) :=
    invariant_pair_of_both_images P Q (hPQ)
      a (Theory.SpecificGroups.SymplecticFour.point_parabolic_map_pair_of_borel hcard hf a ha)
      (Theory.SpecificGroups.SymplecticFour.plane_parabolic_map_pair_of_borel hcard hf a ha)
  refine ⟨markedParabolicResidual_perfect M K e P,hnot,
    markedParabolicResidual_sup_sylow T hP K e P hnot,?_,?_,?_,?_⟩
  · exact markedParabolicResidual_index_two_of_movesDiagram M K _
      (ChapterB.minimalParabolicMax_spec T hP).2 e P Q B he
      (show P ⊓ Q = B from rfl) hnot hpair hmove
  · exact markedParabolicResidual_sylow_intersection T M K
      (ChapterB.minimalParabolicMax_spec T hP).2 e he
      (show Theory.SpecificGroups.SymplecticFour.borel (F := F) ≤
        Theory.SpecificGroups.SymplecticFour.pointParabolic from inf_le_left)
  · exact original_twoCore_le_markedResidual_normalizer T hP K e P
  · exact ⟨originalSymplecticParabolicResidualCoreEquiv T hP hs K hK hqK hgen hcard hf e⟩
end CFSG.Quasithin.Chapter14.Section02
