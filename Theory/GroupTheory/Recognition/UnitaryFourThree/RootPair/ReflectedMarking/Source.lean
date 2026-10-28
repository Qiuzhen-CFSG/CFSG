module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Action
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.MarkedKernel
/-!
# Original-source reflected markings and the canonical odd kernel

The original IsType hypothesis constructs both dihedral reflections in
Tx=T∩N_G(X), their actual action on the cubic Sylow subgroup, and involution
fusion. This fills the unchanged ReflectedMarking record with no added
hypothesis. The positioned form also retains an original elementary-sixteen
plane containing the first reflection, normalized by Tx, and both literal
quaternion-factor interchange maps. The final consumer applies the existing
odd-kernel theorem to the original Sylow-three inclusion.

Source: Aschbacher, Sporadic Groups,45.3(5),45.5 and45.7, pp.243–245.
-/
@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)
theorem exists_reflected_marking (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    ∃m:CubicNormalizer.ReflectedMarking z X,
      m.t∈P.cubicSylow X ∧ m.s∈P.cubicSylow X ∧ m.t∉core z ∧ m.s∉core z := by
  obtain ⟨t,ht,s,hs,hto,hso,htQ,hsQ,hst⟩:=P.exists_cubic_reflection_relations h X hX hXH
  have ht2:t^2=1 := hto ▸ pow_orderOf_eq_one t
  have hs2:s^2=1 := hso ▸ pow_orderOf_eq_one s
  refine ⟨{
    t:=t
    s:=s
    t_order:=hto
    s_order:=hso
    t_normalizes:=ht.2
    s_normalizes:=hs.2
    zt_commute:=(mem_centralizer_singleton_iff.mp (P.T_le_centralizer ht.1)).symm
    t_fused:=h.involution_fused t hto
    reflection_conjugation:=hst
    common_fixed_card:=P.cubic_involution_fixed_card h X hX hXH t ht ht2 htQ
    rotation_inverts:=P.cubic_reflection_rotation_inverts h X hX hXH t s ht hs ht2 hs2 htQ hsQ hst
  },ht,hs,htQ,hsQ⟩

theorem exists_positioned_reflected_marking (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    ∃m:CubicNormalizer.ReflectedMarking z X,∃V:Subgroup G,
      (V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) ∧ m.t∈V ∧
      m.t∈P.cubicSylow X ∧ m.s∈P.cubicSylow X ∧
      P.cubicSylow X≤normalizer (V:Set G) ∧
      h.toCentralizerHypothesis.factorData.leftCore.map (MulAut.conj m.t).toMonoidHom=
        h.toCentralizerHypothesis.factorData.rightCore ∧
      h.toCentralizerHypothesis.factorData.rightCore.map (MulAut.conj m.t).toMonoidHom=
        h.toCentralizerHypothesis.factorData.leftCore := by
  obtain ⟨m,ht,hs,htQ,hsQ⟩:=P.exists_reflected_marking h X hX hXH
  have ht2:m.t^2=1 := m.t_order ▸ pow_orderOf_eq_one m.t
  have htR:m.t∈P.R := (P.involution_mem_R_or_core h m.t ht.1 m.t_order).resolve_right htQ
  let : IsElementaryAbelian 2 (zpowers m.t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  obtain ⟨V,hUV,hVT,hVE,hVc⟩:=P.elementary_in_R_le_plane h (zpowers m.t) (zpowers_le.mpr htR)
  have hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16 := ⟨hVT,hVE,hVc⟩
  exact ⟨m,V,hV,hUV (mem_zpowers m.t),ht,hs,P.cubicSylow_normalizes_plane h X V hV,
    P.T_involution_swaps_core_factors h m.t ht.1 ht2 htQ⟩
end RootPair
namespace IsType
variable (h:IsType z)
include h in
theorem original_reflected_marking (P:Sylow 3 (centralizer z)) :
    Nonempty (CubicNormalizer.ReflectedMarking z
      ((P:Subgroup (centralizer z)).map (centralizer z).subtype)) := by
  obtain ⟨R⟩:=h.exists_rootPair
  obtain ⟨m,_⟩:=R.exists_reflected_marking h _ (h.cubic_sylow_image_card P) (map_subtype_le _)
  exact ⟨m⟩
include h in
theorem original_reflected_kernel (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    IsElementaryAbelian 3 V ∧ (V=X ∨ Nat.card V=81) := by
  obtain ⟨m⟩:=h.original_reflected_marking P
  exact h.reflected_kernel P m
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
