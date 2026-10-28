module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrame
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSylow

/-!
# One frame for the original radical and Sylow image

Conjugacy inside the already identified local aligns the image of S∩K₂
with the full unipotent Sylow. The image of S intersected with Inn is a
two-group containing this Sylow, so it is exactly that same subgroup.
Every subgroup here comes from the original quotient action.
Source: Aschbacher–Smith, original 4.3.14–16, printed pp.617–618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData

/-- A common frame retains the actual radical and the whole inner part of S. -/
theorem root_sylow_frame (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) (hg : ActionGeneration s)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1<f) (hF : Nat.card F = 2^f)
    (e : componentImage s ≃* PSL(3,F)) :
    ∃ (a : MulAut PSL(3,F)) (b : Bool),
      ((radicalImage s).subgroupOf (componentImage s)).map
        (e.trans a).toMonoidHom = Matrix.PSL3.RootPlaneGeometry.rootPlane F b ∧
      ((image s (S c) ⊓ componentImage s).subgroupOf (componentImage s)).map
        (e.trans a).toMonoidHom = Matrix.PSL3.LinearThree.unipotent F := by
  obtain ⟨a,b,hR,hX⟩ := root_local_frame s D hg hf hF e
  let I := componentImage s
  let P := image s (S c ⊓ secondary c)
  let X := secondaryImage s
  have hXI : X ≤ I := secondaryImage_le_componentImage s
  have hPX : P ≤ X := map_mono (comap_mono inf_le_right)
  have hPI : P ≤ I := hPX.trans hXI
  have hSyl : Chapter1.IsSylowIn 2 (P.subgroupOf I) (X.subgroupOf I) := by
    apply (Chapter1.IsSylowIn.map_iff I.subtype I.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hPI,map_subgroupOf_eq_of_le hXI]
    exact original_sylow_image s D
  have hmodel := Chapter1.Section02.IndexTwo.isSylowIn_map hSyl (e.trans a).toMonoidHom
  rw [hX] at hmodel
  obtain ⟨P₁,hP₁⟩ := hmodel
  obtain ⟨g,hgP,hgR⟩ := Matrix.PSL3.LinearThree.RadicalNormalizer.local_sylow_frame
    (by omega : 0<f) hF b P₁
  have he : (e.trans (a.trans (MulAut.conj g.val))).toMonoidHom =
      (MulAut.conj g.val).toMonoidHom.comp (e.trans a).toMonoidHom := by
    ext x
    rfl
  have hP : (P.subgroupOf I).map
      (e.trans (a.trans (MulAut.conj g.val))).toMonoidHom =
        Matrix.PSL3.LinearThree.unipotent F := by
    rw [he,←Subgroup.map_map,←hP₁]
    exact hgP
  refine ⟨a.trans (MulAut.conj g.val),b,?_,?_⟩
  · rw [he,←Subgroup.map_map,hR]
    exact hgR
  · let J := (image s (S c) ⊓ I).subgroupOf I
    have hpS : IsPGroup 2 (image s (S c)) :=
      (T.isPGroup'.to_le inf_le_left).comap_subtype.map s.action
    have hpJ : IsPGroup 2 J := (hpS.to_le inf_le_left).comap_subtype
    have hPJ : P.subgroupOf I ≤ J := by
      apply comap_mono
      exact le_inf (map_mono (comap_mono inf_le_left)) hPI
    exact (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF).is_maximal'
      (hpJ.map (e.trans (a.trans (MulAut.conj g.val))).toMonoidHom)
      (hP ▸ map_mono hPJ)

end SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
