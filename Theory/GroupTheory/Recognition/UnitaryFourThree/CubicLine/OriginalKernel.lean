module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.SourceOddKernel
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Source
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CubicKernelConsumer

/-!
# Original-source cubic kernels with all binary-local inputs discharged

The source reflected actors and the actual A6 plane normalizer remove the
last earlier witnesses from the order81 kernel. The same IsType hypothesis
then constructs the cubic line, quaternion Sylow normalizer and exact common
order27 layer, retaining the original Sylow-three inclusion throughout.
Source: Aschbacher, Sporadic Groups (1994),45.7–45.8,pp245–246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem original_cubic_kernel_eighty_one (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    IsElementaryAbelian 3 V ∧ Nat.card V=81 := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  obtain ⟨M,f,hf⟩:=h.exists_A6_section
  exact h.reflected_kernel_from_A6_section P m M f hf

include h in
theorem original_cubic_line_structure (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    ∃W:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) ∧
      (∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4)) ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) ∧
      CubicLine.oddKernel W⊓centralizer z=W ∧
      (∀d∈CubicLine.oddKernel W,z*d*z⁻¹*d∈W) ∧
      ⁅CubicLine.oddKernel W,CubicLine.oddKernel W⁆≤W ∧
      V⊓CubicLine.oddKernel W=⁅V,zpowers z⁆⊔W ∧
      Nat.card (V⊓CubicLine.oddKernel W:Subgroup G)=27 := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  obtain ⟨W,hW,hWX,hfixed,hS,hN,hD,hi,hcom⟩:=h.source_cubic_line_oddKernel P m
  exact ⟨W,hW,hWX,hfixed,hS,hN,hD,hi,hcom,
    h.cubic_line_kernel_intersection _ W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hfixed hN hV hVc⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
