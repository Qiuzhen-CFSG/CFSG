module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Intersection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CubicKernelConsumer
public import Theory.GroupTheory.CentralCubicNormalizerCount

/-!
# Counting the original cubic-line odd core

The earlier U-line normalizer supplies an actual cubic F in V∩D whose
normalizer preserves V with quotient order24. The source intersection theorem
and central commutator row then bound the original D by243. The separate
U-line family owns this F and its normalizer; neither is inferred from a
mere line/model label.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_card_dvd_of_moved_line (X W F:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (hW:Nat.card W=3) (hWX:W≤X)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hV:IsElementaryAbelian 3 (CubicNormalizer.oddKernel X))
    (hVcard:Nat.card (CubicNormalizer.oddKernel X)=81)
    (hF:Nat.card F=3) (hFV:F≤CubicNormalizer.oddKernel X) (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer (CubicNormalizer.oddKernel X:Set G))
    (hindex:(CubicNormalizer.oddKernel X).relIndex (normalizer (F:Set G))=24) :
    Nat.card (CubicLine.oddKernel W)∣243 := by
  let : IsElementaryAbelian 3 (CubicNormalizer.oddKernel X):=hV
  apply odd_central_cubic_card_dvd_243 (CubicLine.oddKernel W) W (CubicNormalizer.oddKernel X) F
    (CubicLine.oddKernel_odd W) hW hF hFD
    (h.cubic_line_oddKernel_inversion W hW (hWX.trans hXH) hfixed).2
    (le_centralizer_iff.mp (CubicLine.oddKernel_centralizes W hW))
    ?_ hVN hindex ?_
  · intro v hv f hf
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=CubicNormalizer.oddKernel X)).comm
      (⟨f,hFV hf⟩:CubicNormalizer.oddKernel X) ⟨v,hv⟩)
  · rw [inf_comm]
    exact (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVcard).2

include h in
theorem source_cubic_line_card_dvd_of_moved_line (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (M:Subgroup G) (f:M→*alternatingGroup (Fin 6)) (hf:Function.Surjective f)
    (W F:Subgroup G) (hW:Nat.card W=3)
    (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24) : Nat.card (CubicLine.oddKernel W)∣243 := by
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_from_A6_section P m M f hf
  exact h.cubic_line_card_dvd_of_moved_line _ W F (h.cubic_sylow_image_card P) (map_subtype_le _)
    hW hWX hfixed hsplit hV hVc hF hFV hFD hVN hindex
include h in
theorem source_cubic_line_card_dvd_of_binary_normalizers (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (W F:Subgroup G) (hW:Nat.card W=3)
    (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24) : Nat.card (CubicLine.oddKernel W)∣243 := by
  obtain ⟨hV,hVc⟩:=h.reflected_kernel_of_source_binary_normalizers P m
  exact h.cubic_line_card_dvd_of_moved_line _ W F (h.cubic_sylow_image_card P) (map_subtype_le _)
    hW hWX hfixed hsplit hV hVc hF hFV hFD hVN hindex
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
