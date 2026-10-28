module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Order
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.SourceQuotient

/-!
# The original S₄ of index fifteen in the cubic normalizer quotient

The earlier source line normalizer has quotient S₄ by V. Its literal inclusion
in N(V), followed by the faithful quotient map, gives an actual S₄ subgroup.
The proved quotient order360 makes its index15. The final source theorem
packages this subgroup with the elementary-nine TI Sylow and normalizer36,
retaining only the original IsType hypothesis.
Source: Aschbacher, Sporadic Groups (1994),45.9 and Exercise2,p247–249.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem exists_symmetric_four_subgroup :
    ∃H:Subgroup (NormalizerAction.Star c.toSourceData.V),
      Nonempty (H≃*Equiv.Perm (Fin 4)) ∧ H.index=15 := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  obtain ⟨m,hVK,hi,hN,eK⟩:=h.exists_reflected_line_quotient_source P
  let U:=c.toSourceData.X⊓Subgroup.centralizer ({m.t}:Set G)
  let K:=normalizer (U:Set G)
  let : (V.subgroupOf K).Normal:=hN
  have hKM:K≤M:=by
    apply le_normalizer_iff.mpr
    intro k hk v hv
    exact hN.conj_mem (⟨v,hVK hv⟩:K) hv ⟨k,hk⟩
  let π:K→*NormalizerAction.Star V:=f.comp (inclusion hKM)
  have hker:π.ker=V.subgroupOf K:=by
    ext k
    change f (inclusion hKM k)=1 ↔ (k:G)∈V
    rw [←MonoidHom.mem_ker,c.quotient_kernel_eq]
    rfl
  let e:π.range≃*Equiv.Perm (Fin 4):=(QuotientGroup.quotientKerEquivRange π).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans eK.some)
  have hcard:Nat.card π.range=24:=by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hh:=π.range.card_mul_index
  rw [hcard,c.quotient_card] at hh
  exact ⟨π.range,⟨e⟩,by omega⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem original_cubic_quotient_structure (h:IsType z) (P:Sylow 3 (centralizer z)) :
    ∃c:CubicGeometry.SourceConfiguration h P,
      Nat.card (NormalizerAction.Star c.toSourceData.V)=360 ∧
      IsElementaryAbelian 3 c.quotientSylow ∧ Nat.card c.quotientSylow=9 ∧
      (∀g:NormalizerAction.Star c.toSourceData.V,
        g∉normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V))→
        Disjoint (c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V))
          ((c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V)).map (MulAut.conj g).toMonoidHom)) ∧
      Nat.card (normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V)))=36 ∧
      ∃H:Subgroup (NormalizerAction.Star c.toSourceData.V),Nonempty (H≃*Equiv.Perm (Fin 4)) ∧ H.index=15 := by
  obtain ⟨c⟩:=h.original_cubic_source_configuration P
  exact ⟨c,c.quotient_card,c.quotientSylow_elementary,c.quotientSylow_card,c.quotientSylow_Ti,
    c.quotientSylow_normalizer_card,c.exists_symmetric_four_subgroup⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
