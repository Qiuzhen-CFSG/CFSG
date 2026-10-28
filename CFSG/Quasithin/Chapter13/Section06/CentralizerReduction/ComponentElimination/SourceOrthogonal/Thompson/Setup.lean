module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import Theory.GroupTheory.PCoreActionCardKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The genuine local group and its centralizer kernel

The selected K lies in Y_z, T_v normalizes K, and L_v lies in K. Thus
K₋L_vT_v is literally KT_v. The earlier characteristic-two result puts
W_K in the elementary omega-center of O₂(G_v), hence in T_v.

The actual plus map has kernel C_{KT_v}(W_K). Its restriction to K has
kernel of order |O₂(K)|, because both K/O₂(K) and K⁺ have the specified
SL₄(2) models. Since KT_v/K is a two-group, the full kernel is a two-group.
This argument does not assume a centralizer/core identity or a split module.

The input record lists only earlier source facts and the two rank-four
identifications. Their production belongs to the source-selection owner.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the setup on
printed pp.928–930 and 13.6.23 on printed p.933.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}

/-- The earlier source facts used in the Thompson comparison. The two
linear identifications refer to K/O₂(K) and the actual image K⁺. -/
structure EarlierData (K L T : Subgroup G) (z v : G) where
  component : K ∈ Yz L T z v
  tvSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)
  normalizeL : Tv T v ≤ normalizer (Lv L v : Set G)
  fixSeed : Tv T v ≤ centralizer ({z} : Set G)
  normalizeK : Tv T v ≤ normalizer (K : Set G)
  lv_le : Lv L v ≤ K
  seedOmega : z ∈ omegaOneCenterAmbient (Tv T v)
  characteristicTwo : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)
  coreModel : K ⧸ pCore 2 K ≃* SL(4, ZMod 2)
  plusModel : plusImage K L T z v normalizeL fixSeed K ≃* SL(4, ZMod 2)

namespace EarlierData
variable (d : EarlierData K L T z v)
include d

omit [Finite G] in
theorem actor_eq : plusActor K L T v = K ⊔ Tv T v := by
  rw [plusActor, Kminus_eq_of_invariant K T v d.normalizeK, sup_eq_left.mpr d.lv_le]

omit d [Finite G] in
private theorem core_le_sylow {S H : Subgroup G}
    (hs : Chapter1.IsSylowIn 2 S H) : H.pCoreIn 2 ≤ S := by
  obtain ⟨P, rfl⟩ := hs
  exact pCoreIn_le_sylow H P

theorem WK_le_coreOmega : WK K L T z v ≤ omegaOneCenterAmbient (Qv v) :=
  (WK_le_Uv K L T z v d.component.1.1).trans
    (Uv_le_coreOmega T z v d.tvSylow d.seedOmega d.characteristicTwo)

theorem WK_le_Tv : WK K L T z v ≤ Tv T v := by
  intro w hw
  exact core_le_sylow d.tvSylow ((mem_omegaOneCenterAmbient_iff _ _).mp
    (d.WK_le_coreOmega hw)).1

theorem WK_le_actor : WK K L T z v ≤ plusActor K L T v :=
  d.WK_le_Tv.trans le_sup_right

/-- The elementary subgroup is W_K inside its actual actor, not K. -/
def internalW (_d : EarlierData K L T z v) : Subgroup (plusActor K L T v) :=
  (WK K L T z v).subgroupOf (plusActor K L T v)

instance internalW_normal : (d.internalW).Normal :=
  normal_subgroupOf_of_le_normalizer
    (plusActor_normalizes_WK K L T z v d.normalizeL d.fixSeed)

instance internalW_elementary : IsElementaryAbelian 2 (d.internalW) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv v)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (WK K L T z v) := IsElementaryAbelian.of_le d.WK_le_coreOmega
  exact IsElementaryAbelian.subgroupOf d.WK_le_actor

/-- The marked permutation map is the literal plus quotient followed by
one chosen model isomorphism. -/
def modelMap (e : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)) :
    plusActor K L T v →* Equiv.Perm (Fin 8) :=
  e.toMonoidHom.comp (plusMk K L T z v d.normalizeL d.fixSeed)

omit [Finite G] in
theorem modelMap_surjective (e : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)) :
    Function.Surjective (d.modelMap e) :=
  e.surjective.comp (plusMk_surjective K L T z v d.normalizeL d.fixSeed)

theorem modelMap_ker (e : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)) :
    (d.modelMap e).ker = centralizer (d.internalW : Set (plusActor K L T v)) := by
  rw [modelMap, MonoidHom.ker_comp_of_injective _ _ e.injective, plusMk_ker]
  ext a
  constructor
  · intro ha w hw
    exact Subtype.ext (ha w hw)
  · intro ha w hw
    exact congrArg Subtype.val (ha ⟨w, d.WK_le_actor hw⟩ hw)

/-- Kernel size on K is obtained from the two actual L₄(2) identifications;
the remaining quotient is a two-group because T_v supplements K. -/
theorem modelMap_kernel_isPGroup
    (e : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)) :
    IsPGroup 2 (d.modelMap e).ker := by
  let H := plusActor K L T v
  let C := K.subgroupOf H
  have hKH : K ≤ H := K_le_plusActor K L T v
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr (by
    change plusActor K L T v ≤ normalizer (K : Set G)
    rw [d.actor_eq]
    exact sup_le K.le_normalizer d.normalizeK)
  have hsup : C ⊔ (Tv T v).subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hKH (show Tv T v ≤ H from le_sup_right), ← d.actor_eq]
    exact subgroupOf_self _
  have hq : IsPGroup 2 (H ⧸ C) := isPGroup_quotient_of_sup_eq_top C _
    (Chapter1.isSylowIn_iff.mp d.tvSylow).1.comap_subtype hsup
  apply MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient (d.modelMap e) C hq
  have him : C.map (d.modelMap e) =
      (plusImage K L T z v d.normalizeL d.fixSeed K).map e.toMonoidHom := by
    rw [modelMap, ← map_map]
    rfl
  rw [him, card_map_of_injective e.injective]
  let c : C ≃* K := subgroupOfEquivOfLe hKH
  let cq : C ⧸ pCore 2 C ≃* K ⧸ pCore 2 K :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  exact (Nat.card_congr d.plusModel.toEquiv).trans
    ((Nat.card_congr (cq.trans d.coreModel).toEquiv).symm)

/-- The faithful binary action on the same W_K, retaining its full kernel. -/
noncomputable def modelRepresentation
    (e : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)) :=
  Representation.NormalElementaryQuotient.representation d.internalW
    (d.modelMap e) (d.modelMap_surjective e) (d.modelMap_ker e)

end EarlierData

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
