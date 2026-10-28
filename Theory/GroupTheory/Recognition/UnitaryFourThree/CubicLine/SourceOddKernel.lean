module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Intersection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.SourceKernel
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneSource

/-!
# The original cubic-line odd-core structure

The source elementary sixteen and its actual core eight discharge the final
binary-local witness in the quaternion normalizer argument. The same original
W has a quaternion Sylow normalizer, canonical odd-core decomposition, exact
fixed line and inverted abelian quotient. The reflected actors remain the
independently owned earlier45.3 input; no further local model is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.8,pp245–246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem source_cubic_line_oddKernel (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) :
    ∃W:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2) ∧
      (∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4)) ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) ∧
      CubicLine.oddKernel W⊓centralizer z=W ∧
      (∀d∈CubicLine.oddKernel W,z*d*z⁻¹*d∈W) ∧
      ⁅CubicLine.oddKernel W,CubicLine.oddKernel W⁆≤W := by
  obtain ⟨E,hEE,hE,hEH,hEQ,_⟩:=h.exists_plane_with_core_eight
  let : IsElementaryAbelian 2 E:=hEE
  obtain ⟨W,hW,hWX,hfixed,hS,hN⟩:=h.exists_cubic_line_quaternion_normalizer P m E hEH hE hEQ
  have hWH:W≤centralizer z:=hWX.trans (map_subtype_le _)
  exact ⟨W,hW,hWX,hfixed,hS,hN,h.cubic_line_oddKernel_fixed W hW hWH hfixed,
    h.cubic_line_oddKernel_inversion W hW hWH hfixed⟩
include h in
theorem source_cubic_line_kernel_intersection (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (M:Subgroup G) (f:M→*alternatingGroup (Fin 6)) (hf:Function.Surjective f) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    IsElementaryAbelian 3 V ∧ Nat.card V=81 ∧
    ∃W:Subgroup G,Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      (∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4)) ∧
      normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z) ∧
      CubicLine.oddKernel W⊓centralizer z=W ∧
      (∀d∈CubicLine.oddKernel W,z*d*z⁻¹*d∈W) ∧
      ⁅CubicLine.oddKernel W,CubicLine.oddKernel W⁆≤W ∧
      V⊓CubicLine.oddKernel W=⁅V,zpowers z⁆⊔W ∧
      Nat.card (V⊓CubicLine.oddKernel W:Subgroup G)=27 := by
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_from_A6_section P m M f hf
  obtain ⟨W,hW,hWX,hfixed,hS,hN,hD,hInv,hcomm⟩:=h.source_cubic_line_oddKernel P m
  exact ⟨hV,hVc,W,hW,hWX,hS,hN,hD,hInv,hcomm,
    h.cubic_line_kernel_intersection _ W (h.cubic_sylow_image_card P) (map_subtype_le _)
      hW hWX hfixed hN hV hVc⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
