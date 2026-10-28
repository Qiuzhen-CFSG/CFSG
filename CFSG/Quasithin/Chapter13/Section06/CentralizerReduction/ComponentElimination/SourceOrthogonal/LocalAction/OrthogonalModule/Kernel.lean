module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreActionCardKernel

/-!
# The kernel of the actual plus quotient

The intrinsic quotient K/O₂(K) and the actual image K⁺ have equal orders
under the source marking. Hence the restricted action kernel has the order
of O₂(K). The full kernel is an extension of that two-group by a subgroup
of KTᵥ/K, so is itself a two-group. This supplies the kernel condition in
LocalAction's residual/core quotient transports. The intrinsic quotient
marking is a separate source obligation, produced during the proof of 13.6.23.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23 and its final paragraph, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The source intrinsic quotient marking and the two-group supplement prove
that the literal plus action has a two-group kernel. The intrinsic quotient
marking is not inferred from the abstract type of the action image. -/
theorem plusMk_kernel_isPGroup
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K) :
    IsPGroup 2 (plusMk K L T z v hL hz).ker := by
  let A := plusActor K L T v
  let N := K.subgroupOf A
  let f := plusMk K L T z v hL hz
  have hKA : K ≤ A := K_le_plusActor K L T v
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hKA).mpr (by
    change plusActor K L T v ≤ normalizer (K : Set G)
    rw [plusActor_eq K L T v hK hLK]
    exact sup_le K.le_normalizer hK)
  have hgen : N ⊔ (Tv T v).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKA,
      map_subgroupOf_eq_of_le (show Tv T v ≤ A from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    exact (plusActor_eq K L T v hK hLK).symm
  have hquot : IsPGroup 2 (A ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((Tv T v).subgroupOf A) hT.comap_subtype hgen
  apply MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient f N hquot
  let c : N ≃* K := subgroupOfEquivOfLe hKA
  let cq : N ⧸ pCore 2 N ≃* K ⧸ pCore 2 K :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  exact (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr cq.toEquiv).symm

/-- The actual local Sylow subgroup maps to a Sylow subgroup of the plus
quotient. This needs no assumption about the size of the action kernel. -/
theorem exists_plus_sylow
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hKGv : K ≤ Gv v) (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    ∃ S : Sylow 2 (Gplus K L T z v hL hz),
      (S : Subgroup _) = plusImage K L T z v hL hz (Tv T v) := by
  obtain ⟨P, hP⟩ := hSyl.restrict
    (show Tv T v ≤ plusActor K L T v from le_sup_right)
    (plusActor_le_Gv K L T v hKGv)
  refine ⟨P.mapSurjective (f := plusMk K L T z v hL hz) (plusMk_surjective K L T z v hL hz), ?_⟩
  rw [Sylow.coe_mapSurjective, plusImage, ← hP]
  change (P : Subgroup (plusActor K L T v)).map (plusMk K L T z v hL hz) =
    (((P : Subgroup (plusActor K L T v)).map (plusActor K L T v).subtype).comap
      (plusActor K L T v).subtype).map (plusMk K L T z v hL hz)
  rw [comap_map_eq_self_of_injective (plusActor K L T v).subtype_injective]

/-- Application to the actual O₂(XTᵥ) transport. The source intrinsic
quotient markings discharge the kernel premise of the published transport. -/
theorem residual_join_core_image_of_intrinsic_model
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K) :
    plusImage K L T z v hL hz ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2) =
      (plusImage K L T z v hL hz (Source.orthogonalResidual K z) ⊔
        plusImage K L T z v hL hz (Tv T v)).pCoreIn 2 :=
  residual_join_core_image K L T z v hL hz
    (plusMk_kernel_isPGroup K L T z v hL hz hK hLK hT e)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
