module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.InternalFusion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Reduction
public import Theory.GroupTheory.TwoInvolutionClassGeneration

/-!
# Actual generation of the Janko model by max1 and the full pair centralizer

A Sylow of max1 promotes to an ambient Sylow because max1 has odd index.
Its normal binary kernel contains both marked involutions. Their full
centralizers lie in L = M ∨ C(v), they are nonconjugate, and the preceding
internal fusion theorem covers every involution of this Sylow with L-valued
conjugators. Thompson's mixed-pair counting theorem therefore gives L = G.

This is unconditional and independent of the conditional amalgam producer.
Source context: GLS3 Table 5.3i; the two-involution-class counting argument
is documented in `Theory.GroupTheory.TwoInvolutionClassGeneration`.
-/
public section
noncomputable section
namespace Janko4.AdequateLocal
open Subgroup Cardinality Max1AmalgamRigidity Certificates
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed

/-- The image of any intrinsic Sylow has odd ambient index. -/
theorem sylow_image_odd_index (T : Sylow 2 M) :
    ¬ 2 ∣ (T.toSubgroup.map M.subtype).index := by
  rw [index_map_subtype]
  exact Nat.prime_two.not_dvd_mul T.not_dvd_index
    OuterReduction.max1_odd_index_unconditional

/-- A fixed actual ambient Sylow, obtained without conjugating the kernel. -/
@[expose] def ambientSylow : Sylow 2 Model :=
  ((default : Sylow 2 M).isPGroup'.map M.subtype).toSylow
    (sylow_image_odd_index default)

theorem ambientSylow_coe : (ambientSylow : Subgroup Model) =
    (default : Sylow 2 M).toSubgroup.map M.subtype := rfl

theorem ambientSylow_le_M : (ambientSylow : Subgroup Model) ≤ M :=
  map_subtype_le _

theorem E_le_ambientSylow : E ≤ (ambientSylow : Subgroup Model) :=
  map_mono (LocalStructure.localKernel_le_sylow (default : Sylow 2 M))

theorem seed_mem_ambientSylow : seed ∈ ambientSylow := E_le_ambientSylow seed_mem_E

theorem pair_mem_ambientSylow : pair ∈ ambientSylow := E_le_ambientSylow v_mem_E

/-- Both full ambient centralizers and internal Sylow fusion force generation. -/
theorem generated_eq_top : L = ⊤ := by
  apply Theory.GroupTheory.TwoInvolutionClassGeneration.eq_top_of_centralizers_le
    ambientSylow L (ambientSylow_le_M.trans M_le_L) seed pair
    seed_order pair_order seed_not_isConj_pair
    seed_mem_ambientSylow pair_mem_ambientSylow
  · exact InvolutionCentralizers.Second.ambient_le_max1.trans M_le_L
  · exact C_le_L
  · intro z hz ho
    exact max1_internal_fusion z (ambientSylow_le_M hz) ho

/-- The exact generation premise of the independently proved amalgam producer. -/
theorem centralizer_sup_max1_eq_top : C ⊔ M = ⊤ := by
  rw [sup_comm]
  exact generated_eq_top

end Janko4.AdequateLocal
