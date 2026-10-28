module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.PPrimeCore

/-!
# The literal local quotient in the rank-two application

The A.3.18 actor is H = K Lᵥ, its subgroup is C = K.subgroupOf H,
and its quotient is H/O₃′(H). These definitions retain both maps out of
the original K, including the established K → K* → K+ map. The ambient
SQTK hypothesis follows by restriction from the involution centralizer.

This is preparation for the application, not the missing assertion that
C is a C-component or that K/O₂(K) is quasisimple. In particular Yz's
C-component in KTᵥ is not identified with a C-component in KLᵥ.
Source: Aschbacher–Smith, combined manuscript, 13.6.20, p.931,
and A.3.18, pp.51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection
universe u
variable {G : Type u} [Group G]

abbrev localActor (K L : Subgroup G) (v : G) : Subgroup G := K ⊔ Lv L v

abbrev localComponent (K L : Subgroup G) (v : G) : Subgroup (localActor K L v) :=
  K.subgroupOf (localActor K L v)

abbrev localQuotient (K L : Subgroup G) (v : G) :=
  localActor K L v ⧸ pPrimeCore 3 (localActor K L v)

def localMk (K L : Subgroup G) (v : G) : localActor K L v →* localQuotient K L v :=
  QuotientGroup.mk' (pPrimeCore 3 (localActor K L v))

abbrev localImage (K L : Subgroup G) (v : G) : Subgroup (localQuotient K L v) :=
  (localComponent K L v).map (localMk K L v)

/-- The original component and its restriction have the same elements. -/
def localComponentEquiv (K L : Subgroup G) (v : G) : localComponent K L v ≃* K :=
  subgroupOfEquivOfLe le_sup_left

/-- The intrinsic two-core quotients are compared using transport of O₂. -/
noncomputable def localTwoCoreEquiv (K L : Subgroup G) (v : G) :
    (localComponent K L v ⧸ pCore 2 (localComponent K L v)) ≃* (K ⧸ pCore 2 K) :=
  QuotientGroup.congr _ _ (localComponentEquiv K L v)
    (pCore_map_iso 2 (localComponentEquiv K L v))

/-- The restricted quotient map, with its actual image as codomain. -/
def componentToLocalImage (K L : Subgroup G) (v : G) :
    localComponent K L v →* localImage K L v :=
  (localMk K L v).subgroupMap (localComponent K L v)

theorem componentToLocalImage_surjective (K L : Subgroup G) (v : G) :
    Function.Surjective (componentToLocalImage K L v) :=
  (localMk K L v).subgroupMap_surjective _

theorem componentToLocalImage_ker (K L : Subgroup G) (v : G) :
    (componentToLocalImage K L v).ker =
      (pPrimeCore 3 (localActor K L v)).subgroupOf (localComponent K L v) := by
  rw [componentToLocalImage, ker_subgroupMap, localMk, QuotientGroup.ker_mk']

def toLocalImage (K L : Subgroup G) (v : G) : K →* localImage K L v :=
  (componentToLocalImage K L v).comp (localComponentEquiv K L v).symm.toMonoidHom

theorem toLocalImage_surjective (K L : Subgroup G) (v : G) :
    Function.Surjective (toLocalImage K L v) :=
  (componentToLocalImage_surjective K L v).comp (localComponentEquiv K L v).symm.surjective

theorem toLocalImage_apply (K L : Subgroup G) (v : G) (k : K) :
    (toLocalImage K L v k : localQuotient K L v) =
      localMk K L v (inclusion le_sup_left k) := rfl

/-- Use the existing comparison through the genuine star quotient. -/
noncomputable def toPlusImage (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  (componentStarToPlus K L T z v hK hL hz).comp (starImageMap z v K hK)

theorem toPlusImage_surjective (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (toPlusImage K L T z v hK hL hz) :=
  (componentStarToPlus_surjective K L T z v hK hL hz).comp
    (starImageMap_surjective z v K hK)

theorem toPlusImage_apply (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (k : K) :
    (toPlusImage K L T z v hK hL hz k : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) :=
  componentStarToPlus_mk K L T z v hK hL hz k

variable [Finite G]

/-- SQTK for exactly KLᵥ, derived from the simple-QTKE clause of 13.3.1. -/
theorem localActor_sqtk {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v) :
    IsSQTK κ (localActor K L v) := by
  have hle : localActor K L v ≤ Gv v := sup_le hK.1.1 (Lv_le_Gv L v)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup ((localActor K L v).subgroupOf (Gv v)))

omit [Finite G] in
/-- Perfectness survives the actual restricted quotient map. -/
theorem localImage_perfect (K L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v) :
    Group.IsPerfect (localImage K L v) := by
  let := Chapter1.mem_L_isPerfect hK.1.2
  exact Group.IsPerfect.ofSurjective (toLocalImage_surjective K L v)

/-- The rank used by A.3.18 belongs to C, with no quotient-rank identification. -/
theorem localComponent_rank (K L : Subgroup G) (v : G) :
    primeRank 3 (localComponent K L v) = primeRank 3 K :=
  primeRank_equiv 3 (localComponentEquiv K L v)

/-- The two centers are compared through the actual two-core quotient isomorphism. -/
theorem localTwoCore_center_rank (K L : Subgroup G) (v : G) :
    primeRank 3 (center (localComponent K L v ⧸ pCore 2 (localComponent K L v))) =
      primeRank 3 (center (K ⧸ pCore 2 K)) :=
  primeRank_equiv 3 (centerCongr (localTwoCoreEquiv K L v))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
