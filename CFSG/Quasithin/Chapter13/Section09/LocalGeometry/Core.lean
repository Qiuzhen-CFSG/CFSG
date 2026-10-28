module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Marking

/-!
# The actual extraspecial core in the original Sylow

The marked wreath embedding carries the explicit quaternion central product
into the original group. Its center is the marked line ⟨z⟩, it contains t,
and it contains every square of the original Sylow. No normality in C_G(z)
is asserted by this construction.

Source: Aschbacher–Smith 13.9.6, printed p.971 (PDF p.988).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

def sylowModelEmbedding : P→*G := m.embedding.comp sylowEmbedding

theorem sylowModelEmbedding_injective : Function.Injective m.sylowModelEmbedding :=
  m.embedding_injective.comp sylowEmbedding_injective

theorem range_sylowModelEmbedding : m.sylowModelEmbedding.range=(d.T:Subgroup G) := by
  rw [sylowModelEmbedding,MonoidHom.range_comp,←standardSylow_coe]
  exact m.image_standardSylow

def core : Subgroup G := coreInP.map m.sylowModelEmbedding

noncomputable def coreEquiv : coreInP≃*m.core :=
  coreInP.equivMapOfInjective m.sylowModelEmbedding m.sylowModelEmbedding_injective

noncomputable def coreQuaternionData : QuaternionCentralProductData m.core :=
  coreInPQuaternionData.map m.coreEquiv

theorem core_le_sylow : m.core≤(d.T:Subgroup G) := by
  rw [←m.range_sylowModelEmbedding]
  exact map_le_range _ _

theorem card_core : Nat.card m.core=32 := by
  rw [core,card_map_of_injective m.sylowModelEmbedding_injective,card_coreInP]

theorem sylowModelEmbedding_center : m.sylowModelEmbedding centralInP=m.z := by
  change m.embedding (sylowEmbedding centralInP)=m.embedding SymmetricFourWreath.z
  rw [sylowEmbedding_centralInP]

theorem t_mem_core : m.t∈m.core := by
  refine ⟨pair (DihedralGroup.r 2,1),axis_mem_coreInP,?_⟩
  change m.embedding (sylowEmbedding (pair (DihedralGroup.r 2,1)))=m.embedding SymmetricFourWreath.t
  rw [sylowEmbedding_axis]

theorem z_mem_core : m.z∈m.core :=
  m.sylowModelEmbedding_center ▸ mem_map_of_mem m.sylowModelEmbedding centralInP_mem_coreInP

theorem z_central_sylow : (d.T:Subgroup G)≤centralizer ({m.z}:Set G) := by
  rw [←m.range_sylowModelEmbedding]
  rintro _ ⟨a,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←m.sylowModelEmbedding_center,←map_mul,←map_mul,centralInP_central]

theorem center_core [Finite G] : (center m.core).map m.core.subtype=zpowers m.z := by
  symm
  apply eq_of_le_of_card_ge
  · apply zpowers_le.mpr
    refine ⟨⟨m.z,m.z_mem_core⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (m.z_central_sylow (m.core_le_sylow x.property)))
  · rw [card_map_of_injective m.core.subtype_injective,m.coreQuaternionData.center_card,Nat.card_zpowers,
      ←m.sylowModelEmbedding_center,orderOf_injective m.sylowModelEmbedding m.sylowModelEmbedding_injective,centralInP_order]

theorem sylow_squares_mem_core (x : G) (hx : x∈(d.T:Subgroup G)) : x^2∈m.core := by
  rw [←m.range_sylowModelEmbedding] at hx
  obtain ⟨a,rfl⟩ := hx
  rw [←map_pow]
  exact mem_map_of_mem m.sylowModelEmbedding (square_mem_coreInP a)
end CFSG.Quasithin.Chapter13.Section09.Marking
