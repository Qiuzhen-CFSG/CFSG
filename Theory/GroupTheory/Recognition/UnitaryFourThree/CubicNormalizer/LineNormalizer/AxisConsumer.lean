module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.MovedSource
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.SourceOddKernel
/-!
# The original45.8 axis and its moved cubic line

Choose the reflected marking before the source quaternion axis. The exact
intersection V∩D=[V,z]W gives [V,z]≤D for that same canonical odd kernel.
The completed U-line source then supplies F≤V∩D with F=[F,z], order3, and
full normalizer index24 over V. No moved-line or normalizer premise remains.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p.246.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem exists_cubic_axis_and_moved_line (h:IsType z) (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    ∃W:Subgroup G,Nat.card W=3 ∧ W≤X ∧
      Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) ∧
      (∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4)) ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) ∧
      ∃F:Subgroup G,F≤V⊓CubicLine.oddKernel W ∧ Nat.card F=3 ∧ ⁅F,zpowers z⁆=F ∧
        normalizer (F:Set G)≤normalizer (V:Set G) ∧ V.relIndex (normalizer (F:Set G))=24 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  obtain ⟨m,hmove⟩:=h.exists_reflected_moved_line_source P
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_of_source_binary_normalizers P m
  obtain ⟨W,hW,hWX,hQ,hS,hN,_,_,_⟩:=h.source_cubic_line_oddKernel P m
  have hVD:V⊓CubicLine.oddKernel W=⁅V,zpowers z⁆⊔W:=
    (h.cubic_line_kernel_intersection X W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hQ hN hV hVc).1
  have hD:⁅V,zpowers z⁆≤CubicLine.oddKernel W:=
    (le_sup_left.trans_eq hVD.symm).trans inf_le_right
  exact ⟨W,hW,hWX,hQ,hS,hN,hmove (CubicLine.oddKernel W) hD⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
