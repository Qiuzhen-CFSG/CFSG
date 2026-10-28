module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.BlockQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.FixedSpace
public import Theory.GroupTheory.PCoreSurjective

/-!
# The source center-preimage commutator identity

Restrict the map C_G(v) → C_G(v)/⟨v⟩ to K and give it its actual image
as codomain. Its kernel is a two-group when v²=1. The block calculation
then proves [Z₀,K]=U with Z₀ the literal preimage of Z(O₂(Ǩ)).
It also identifies the intrinsic blockU with the source [Z(O₂(K)),K].

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the final
paragraph of 13.6.22 on printed p.932.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches
variable {G : Type*} [Group G] (K : Subgroup G) (v : G) (hK : K ≤ Gv v)

/-- Restrict the specified checked quotient to K, with its literal image as codomain. -/
def checkedBlockProjection : K →* checkedImage v K :=
  ((checkedQuotientMap v).subgroupMap (K.subgroupOf (Gv v))).comp
    (subgroupOfEquivOfLe hK).symm.toMonoidHom

/-- Restriction is onto the literal checked image of K. -/
theorem checkedBlockProjection_surjective :
    Function.Surjective (checkedBlockProjection K v hK) :=
  ((checkedQuotientMap v).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hK).symm.surjective

/-- The restricted projection uses the prescribed checked map. -/
theorem checkedBlockProjection_apply (k : K) :
    (checkedBlockProjection K v hK k : Gcheck v) =
      checkedQuotientMap v (inclusion hK k) := rfl

/-- The exact kernel is the pullback of the central involution line. -/
theorem checkedBlockProjection_kernel :
    (checkedBlockProjection K v hK).ker = (vLine v).comap (inclusion hK) := by
  ext k
  change checkedBlockProjection K v hK k = 1 ↔ inclusion hK k ∈ vLine v
  rw [← checkedQuotientMap_kernel, MonoidHom.mem_ker]
  constructor
  · intro hk
    exact congrArg Subtype.val hk
  · intro hk
    exact Subtype.ext hk

/-- The involution relation makes the restricted kernel a two-group. -/
theorem checkedBlockProjection_kernel_twoGroup (hv : v ^ 2 = 1) :
    IsPGroup 2 (checkedBlockProjection K v hK).ker := by
  rw [checkedBlockProjection_kernel]
  have hp : IsPGroup 2 (vLine v) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change Nat.card (zpowers (centralElement v)) ∣ 2 ^ 1
    rw [Nat.card_zpowers]
    have hv' : centralElement v ^ 2 = 1 := Subtype.ext hv
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one hv'
  exact hp.comap_of_injective (inclusion hK) (inclusion_injective hK)

/-- The actual preimage in K of Z(O₂(Ǩ)), returned to the ambient group. -/
def checkedBlockCenterPreimage : Subgroup G :=
  (((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).comap
    (checkedBlockProjection K v hK)).map K.subtype

/-- The commutator from the short-group definition equals the source center commutator. -/
theorem blockU_eq_coreCenter_commutator (h : ChapterC.IsShort K) :
    (ChapterC.blockU K).map K.subtype =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ := by
  have hh := short_centerPreimage_commutator h (MonoidHom.id K)
    Function.surjective_id (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
  have hm := congrArg (Subgroup.map K.subtype) hh
  rw [comap_id, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.symm

/-- Source [Z₀,K]=U, with the specified checked quotient rather than an arbitrary quotient. -/
theorem checkedBlockCenterPreimage_commutator (h : ChapterC.IsShort K) (hv : v ^ 2 = 1) :
    ⁅checkedBlockCenterPreimage K v hK, K⁆ = (ChapterC.blockU K).map K.subtype := by
  have hh := short_centerPreimage_commutator h (checkedBlockProjection K v hK)
    (checkedBlockProjection_surjective K v hK) (checkedBlockProjection_kernel_twoGroup K v hK hv)
  have hm := congrArg (Subgroup.map K.subtype) hh
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The full source identity, with both Z₀ and U written as their literal subgroup expressions. -/
theorem checkedBlockCenterPreimage_commutator_eq_coreCenter
    (h : ChapterC.IsShort K) (hv : v ^ 2 = 1) :
    ⁅checkedBlockCenterPreimage K v hK, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ := by
  rw [checkedBlockCenterPreimage_commutator K v hK h hv,
    blockU_eq_coreCenter_commutator K h]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches

