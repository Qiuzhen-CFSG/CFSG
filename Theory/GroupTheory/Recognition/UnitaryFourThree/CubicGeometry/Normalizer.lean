module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Fusion

/-!
# The common normalizer of the source point and line

The center of the actual Sylow product is W and its unique maximum-order
abelian subgroup is V. Hence its normalizer preserves both. Conversely,
an actor normalizing V and W preserves D=O₂′(N_G(W)) and thus VD. This
identifies the actual common normalizer, without an incidence-geometry or
normalizer-order hypothesis.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_common_normalizer (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243)
    (he:IsExtraspecial 3 (CubicLine.oddKernel (zpowers (actors.x:G))))
    (T:Sylow 3 G)
    (hT:(T:Subgroup G)=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊔
      CubicLine.oddKernel (zpowers (actors.x:G)))
    (hcenter:(center T).map (T:Subgroup G).subtype=zpowers (actors.x:G)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    normalizer (T:Set G)=normalizer (V:Set G)⊓normalizer (zpowers (actors.x:G):Set G) := by
  apply le_antisymm
  · refine le_inf (h.cubic_kernel_source_fusion P actors ha hsplit hD he T hT).2.1 ?_
    rw [←hcenter]
    exact normalizer_le_normalizer_characteristic_image (T:Subgroup G) (center T)
  · change _≤normalizer ((T:Subgroup G):Set G)
    rw [hT]
    exact (le_inf inf_le_left (inf_le_right.trans
      (CubicLine.normalizer_normalizes_oddKernel _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
