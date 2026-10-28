module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.CoreQuotient
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Overgroups
public import Theory.GroupTheory.QuaternionCentralProductTransport.Factors

/-!
# The three original overgroups of Q and their quaternion-factor marking

The three coordinate lines of P/Q transport to distinct order-64 subgroups
of the original Sylow. They are its intersection with the normalizer of the
actual first quaternion factor, AQ, and BQ. The two marked elementary groups
both move that factor. These are the exact native inputs to the final
normality argument for B in C_G(z).

Source: Aschbacher–Smith 13.9.8(2), printed p.972 (PDF p.989).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath CentralizerStructure
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

def coreOvergroup (i : Fin 3) : Subgroup G := (SymmetricFourWreath.coreOvergroup i).map m.sylowModelEmbedding

theorem card_coreOvergroup (i : Fin 3) : Nat.card (m.coreOvergroup i)=64 := by
  rw [coreOvergroup,card_map_of_injective m.sylowModelEmbedding_injective,SymmetricFourWreath.card_coreOvergroup]

theorem core_le_coreOvergroup (i : Fin 3) : m.core≤m.coreOvergroup i :=
  map_mono (SymmetricFourWreath.core_le_coreOvergroup i)

theorem coreOvergroup_le_sylow (i : Fin 3) : m.coreOvergroup i≤(d.T:Subgroup G) := by
  rw [←m.range_sylowModelEmbedding]
  exact map_le_range _ _

theorem coreOvergroup_injective : Function.Injective m.coreOvergroup := by
  intro i j h
  exact SymmetricFourWreath.coreOvergroup_distinct ((map_injective m.sylowModelEmbedding_injective) h)

theorem diagonal_sup_core (b : Bool) : m.elementaryGroup b b⊔m.core=m.coreOvergroup (if b then 2 else 1) := by
  have hm : m.elementaryGroup b b=(elementaryInP b b).map m.sylowModelEmbedding := by
    change ((elementaryInP b b).map sylowEmbedding).map m.embedding=_
    rw [map_map]
    rfl
  rw [hm,core,←Subgroup.map_sup,elementary_sup_core]
  rfl

variable [Finite G]
variable (p : PairData d) (hz : p.z=m.z) (ht : p.t=m.t)

theorem coreData_left_image :
    ((m.coreData p hz ht).factors.left).map m.core.subtype=
      (quaternionEmbedding false).range.map m.sylowModelEmbedding := by
  change ((coreInPQuaternionData.map m.coreEquiv).left).map m.core.subtype=_
  rw [QuaternionCentralProductData.map_left]
  change (((quaternionEmbedding false).range.subgroupOf coreInP).map m.coreEquiv.toMonoidHom).map m.core.subtype=_
  rw [map_map]
  have he : m.core.subtype.comp m.coreEquiv.toMonoidHom=m.sylowModelEmbedding.comp coreInP.subtype := by
    ext x
    rfl
  rw [he,←map_map,map_subgroupOf_eq_of_le (quaternion_le_coreInP false)]

theorem coreOvergroup_zero : m.coreOvergroup 0 =
    (d.T:Subgroup G)⊓normalizer (((m.coreData p hz ht).factors.left).map m.core.subtype:Set G) := by
  rw [m.coreData_left_image p hz ht,coreOvergroup,←normalizer_quaternion_left]
  have he := comap_normalizer_eq_of_le_range
    ((quaternionEmbedding false).range.map_le_range m.sylowModelEmbedding)
  rw [comap_map_eq_self_of_injective m.sylowModelEmbedding_injective] at he
  rw [←he,map_comap_eq,m.range_sylowModelEmbedding,inf_comm]

theorem diagonal_not_normalizes_left (b : Bool) :
    ¬m.elementaryGroup b b≤normalizer (((m.coreData p hz ht).factors.left).map m.core.subtype:Set G) := by
  intro h
  apply elementary_not_le_quaternion_normalizer b
  have hm : m.elementaryGroup b b=(elementaryInP b b).map m.sylowModelEmbedding := by
    change ((elementaryInP b b).map sylowEmbedding).map m.embedding=_
    rw [map_map]
    rfl
  rw [hm,m.coreData_left_image p hz ht] at h
  have hc := (map_le_iff_le_comap).mp h
  rw [comap_normalizer_eq_of_le_range ((quaternionEmbedding false).range.map_le_range m.sylowModelEmbedding),
    comap_map_eq_self_of_injective m.sylowModelEmbedding_injective] at hc
  exact hc

omit [Finite G] in
/-- The three actual index-two overgroups of the original Q are distinct. -/
theorem three_core_overgroups :
    m.core≤m.coreOvergroup 0 ∧ m.coreOvergroup 0≤(d.T:Subgroup G) ∧
    Nat.card (m.coreOvergroup 0)=64 ∧
    Nat.card (m.elementaryGroup true true⊔m.core : Subgroup G)=64 ∧
    Nat.card (m.B⊔m.core : Subgroup G)=64 ∧
    m.coreOvergroup 0≠m.elementaryGroup true true⊔m.core ∧
    m.coreOvergroup 0≠m.B⊔m.core ∧
    m.elementaryGroup true true⊔m.core≠m.B⊔m.core := by
  rw [m.diagonal_sup_core true,show m.B=m.elementaryGroup false false from rfl,m.diagonal_sup_core false]
  refine ⟨m.core_le_coreOvergroup 0,m.coreOvergroup_le_sylow 0,m.card_coreOvergroup 0,
    m.card_coreOvergroup 2,m.card_coreOvergroup 1,?_,?_,?_⟩
  · exact fun h=>(by decide : (0:Fin 3)≠2) (m.coreOvergroup_injective h)
  · exact fun h=>(by decide : (0:Fin 3)≠1) (m.coreOvergroup_injective h)
  · exact fun h=>(by decide : (2:Fin 3)≠1) (m.coreOvergroup_injective h)
end CFSG.Quasithin.Chapter13.Section09.Marking
