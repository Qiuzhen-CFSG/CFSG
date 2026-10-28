module

public import Theory.GroupTheory.ElementaryNineCyclicFourNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SymmetricFour

/-!
# The original faithful cyclic-four Sylow normalizer quotient

The marked rotation st normalizes V and the actual Sylow product VD. Its
square is z, which inverts VD/V because it inverts D modulo W≤V. The
normalizer quotient has order36, so the elementary-nine conjugation kernel
is exactly the nine and the rotation gives the faithful cyclic-four quotient.
Every actor and quotient here is the original one from IsType.
Source: Aschbacher, Sporadic Groups (1994),45.9 and Exercise2,p247–249.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)
omit [Finite G] in
theorem rotation_normalizes_kernel : c.marking.s*c.marking.t∈normalizer (c.toSourceData.V:Set G) := by
  apply CubicNormalizer.normalizer_normalizes_oddKernel
  exact mul_mem c.marking.s_normalizes c.marking.t_normalizes

omit [Finite G] in
theorem rotation_normalizes_sylow : c.marking.s*c.marking.t∈normalizer (c.toSourceData.Q:Set G) := by
  have hh:c.marking.s*c.marking.t∈normalizer (c.sylow:Set G):=by
    rw[c.common_normalizer]
    exact ⟨c.rotation_normalizes_kernel,(c.complement_le (mem_sup_right (mem_zpowers _))).2⟩
  change c.marking.s*c.marking.t∈normalizer ((c.sylow:Subgroup G):Set G) at hh
  rwa[c.sylow_eq] at hh

theorem quotient_rotation :
    ∃r:NormalizerAction.Star c.toSourceData.V,
      r∈normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V)) ∧
      r^4=1 ∧ ∀x∈(c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V)),
        r^2*x*(r^2)⁻¹=x⁻¹ := by
  let V:=c.toSourceData.V
  let D:=c.toSourceData.D
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  let rn:M:=⟨c.marking.s*c.marking.t,c.rotation_normalizes_kernel⟩
  let zn:M:=⟨z,c.involution_normalizes_kernel⟩
  have hr2:rn^2=zn:=Subtype.ext c.marking.rotation_square
  have hr4:rn^4=1:=by
    rw[show 4=2*2 from rfl,pow_mul,hr2]
    apply Subtype.ext
    change z^2=1
    simpa only [h.involution] using pow_orderOf_eq_one z
  have hQM:c.toSourceData.Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDM:D≤M:=le_sup_right.trans hQM
  refine ⟨f rn,?_,by rw[←map_pow,hr4,map_one],?_⟩
  · have hh:rn∈(normalizer (c.quotientSylow:Set (NormalizerAction.Star V))).comap f:=by
      rw[c.quotientSylow_normalizer_preimage]
      exact c.rotation_normalizes_sylow
    exact hh
  intro x hx
  have hx':x∈(c.toSourceData.Q.subgroupOf M).map f:=c.quotientSylow_coe.le hx
  obtain ⟨q,hq,hqx⟩:=hx'
  have hh:(q:G)∈(V:Set G)*(D:Set G):=by
    rw [←coe_mul_of_right_le_normalizer_left V D hDM]
    exact hq
  obtain ⟨v,hv,d,hd,he⟩:=hh
  let vn:M:=⟨v,V.le_normalizer hv⟩
  let dn:M:=⟨d,hDM hd⟩
  have hqeq:q=vn*dn:=Subtype.ext he.symm
  have hfv:f vn=1:=c.quotient_kernel_eq.ge hv
  have hxd:x=f dn:=by rw[←hqx,hqeq,map_mul,hfv,one_mul]
  have hk:zn*dn*zn⁻¹*dn∈f.ker:=c.quotient_kernel_eq.ge (c.line_le_kernel (c.odd_inversion d hd))
  have hi:f zn*f dn*(f zn)⁻¹*f dn=1:=by
    have hh:=MonoidHom.mem_ker.mp hk
    simpa only[map_mul,map_inv] using hh
  rw[hxd,←map_pow,hr2]
  exact eq_inv_of_mul_eq_one_left hi
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)
theorem quotientSylow_cyclic_four_normalizer :
    let B:=NormalizerAction.Star c.toSourceData.V
    let S:Subgroup B:=c.quotientSylow
    Subgroup.centralizer (S:Set B)≤S ∧
      Nonempty ((normalizer (S:Set B) ⧸ S.subgroupOf (normalizer (S:Set B)))≃*Multiplicative (ZMod 4)) := by
  let B:=NormalizerAction.Star c.toSourceData.V
  let S:Subgroup B:=c.quotientSylow
  let :IsElementaryAbelian 3 S:=c.quotientSylow_elementary
  change Subgroup.centralizer (S:Set B)≤S ∧ Nonempty ((normalizer (S:Set B) ⧸ S.subgroupOf (normalizer (S:Set B)))≃*Multiplicative (ZMod 4))
  obtain ⟨r,hr,hr4,hinv⟩:=c.quotient_rotation
  exact elementary_nine_cyclic_four_normalizer S c.quotientSylow_card
    c.quotientSylow_normalizer_card r hr hr4 hinv
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem original_cubic_exercise_two (h:IsType z) (P:Sylow 3 (centralizer z)) :
    ∃c:CubicGeometry.SourceConfiguration h P,
      let B:=NormalizerAction.Star c.toSourceData.V
      let S:Subgroup B:=c.quotientSylow
      IsElementaryAbelian 3 S ∧ Nat.card S=9 ∧
      (∀g:B,S⊓S.map (MulAut.conj g).toMonoidHom=⊥ ∨ S.map (MulAut.conj g).toMonoidHom=S) ∧
      Subgroup.centralizer (S:Set B)≤S ∧
      Nonempty ((normalizer (S:Set B) ⧸ S.subgroupOf (normalizer (S:Set B)))≃*Multiplicative (ZMod 4)) ∧
      ∃H:Subgroup B,Nonempty (H≃*Equiv.Perm (Fin 4)) ∧ H.index=15 := by
  classical
  obtain ⟨c⟩:=h.original_cubic_source_configuration P
  let B:=NormalizerAction.Star c.toSourceData.V
  let S:Subgroup B:=c.quotientSylow
  obtain ⟨hc,he⟩:=c.quotientSylow_cyclic_four_normalizer
  refine ⟨c,c.quotientSylow_elementary,c.quotientSylow_card,?_,hc,he,c.exists_symmetric_four_subgroup⟩
  intro g
  by_cases hg:g∈normalizer (S:Set B)
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · exact Or.inl (disjoint_iff_inf_le.mp (c.quotientSylow_Ti g hg) |>.antisymm bot_le)
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
