module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.NineExclusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ResidualNormalizer

/-!
# The original root-pair action supplies the order-eighty-one kernel

The root-pair residual normalizer theorem discharges the local square-action
input. The remaining reflected actors and actual A₆ section are precisely
the earlier binary-local source families, not cubic-kernel assumptions.
Source: Aschbacher, *Sporadic Groups* (1994),45.7,printed p245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem reflected_kernel_from_A6_section (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (M:Subgroup G) (f:M→*alternatingGroup (Fin 6)) (hf:Function.Surjective f) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    IsElementaryAbelian 3 V ∧ Nat.card V=81 :=
  h.reflected_kernel_card_eighty_one P m
    (h.cubic_normalizer_square_centralizes _ (h.cubic_sylow_image_card P) (map_subtype_le _)) M f hf
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
