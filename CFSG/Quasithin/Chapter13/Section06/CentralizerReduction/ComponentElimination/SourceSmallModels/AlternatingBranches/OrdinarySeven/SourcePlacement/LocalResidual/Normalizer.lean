module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The ordinary A₇ normalizer comparison through the actual plus map

Compatibility on K identifies the restricted action kernel with O₂(K).
The quotient of KTᵥ by K is a two-group, so the full action kernel is a
two-group and lies in the source Sylow subgroup Tᵥ. The preimage of S⁺
therefore lies between S = Baum(Tᵥ) and Tᵥ. Baumann heredity recovers S
from that preimage, and normalizers pass through the quotient exactly.
This proves the relative normalizer comparison needed in the Frattini step,
without the incompatible printed equality N_{KTᵥ}(S) = (Tᵥ ∩ K)Lᵥ.
The source Sylow information is extracted from the actual Y_z membership.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949), and B.2.3(4).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

-- Baumann heredity recovers the actual subgroup from its saturated preimage.
theorem mem_normalizer_of_image (H R S : Subgroup G) (q : H →* Q)
    (hRH : R ≤ H) (hS : S = ChapterB.baumann R)
    (hk : q.ker ≤ R.subgroupOf H) (x : H)
    (hx : q x ∈ normalizer (((S.subgroupOf H).map q) : Set Q)) :
    (x : G) ∈ normalizer (S : Set G) := by
  let B : Subgroup G := (((S.subgroupOf H).map q).comap q).map H.subtype
  have hSR : S ≤ R := hS ▸ inf_le_left
  have hSB : S ≤ B := by
    intro s hs
    exact ⟨⟨s, hRH (hSR hs)⟩, ⟨⟨s, hRH (hSR hs)⟩, hs, rfl⟩, rfl⟩
  have hBR : B ≤ R := by
    apply map_le_iff_le_comap.mpr
    rw [comap_map_eq]
    exact sup_le (subgroupOf_mono H hSR) hk
  have hBS : ChapterB.baumann B = S := by
    rw [hS]
    exact (ChapterB.lemma_B_2_3_4 R B (hS ▸ hSB) hBR).symm
  have hxB : (x : G) ∈ normalizer (B : Set G) := by
    apply (((S.subgroupOf H).map q).comap q).le_normalizer_map H.subtype
    exact ⟨x, ((S.subgroupOf H).map q).le_normalizer_comap q hx, rfl⟩
  rw [← hBS]
  exact Stellmacher.normalizer_le_normalizer_baumann B hxB

theorem image_relative_normalizer (H K R S : Subgroup G) (q : H →* Q)
    (hRH : R ≤ H) (hS : S = ChapterB.baumann R)
    (hk : q.ker ≤ R.subgroupOf H) :
    ((K ⊓ normalizer (S : Set G)).subgroupOf H).map q =
      (K.subgroupOf H).map q ⊓ normalizer (((S.subgroupOf H).map q) : Set Q) := by
  have hSH : S ≤ H := (show S ≤ R from hS ▸ inf_le_left).trans hRH
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    apply (S.subgroupOf H).le_normalizer_map q
    refine ⟨x, ?_, rfl⟩
    rw [← subgroupOf_normalizer_eq hSH]
    exact hx.2
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, mem_normalizer_of_image H R S q hRH hS hk x hn⟩, rfl⟩

omit [Finite G] in
theorem kernel_isPGroup_of_supplement (A R : Subgroup G) [A.Normal]
    (q : G →* Q) (hR : IsPGroup 2 R) (hgen : A ⊔ R = ⊤)
    (hA : IsPGroup 2 (q.comp A.subtype).ker) : IsPGroup 2 q.ker := by
  have hquot := isPGroup_quotient_of_sup_eq_top A R hR hgen
  intro x
  obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' A x)
  have hxA : (x : G) ^ 2 ^ n ∈ A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' A ((x : G) ^ 2 ^ n) = 1
    rwa [map_pow]
  have hxq : (q.comp A.subtype) ⟨(x : G) ^ 2 ^ n, hxA⟩ = 1 := by
    change q ((x : G) ^ 2 ^ n) = 1
    rw [map_pow, show q x = 1 from x.property, one_pow]
  obtain ⟨m, hm⟩ := hA ⟨⟨(x : G) ^ 2 ^ n, hxA⟩, hxq⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have he := congrArg (fun a : (q.comp A.subtype).ker => (a : G)) hm
  simpa only [coe_pow, coe_one, pow_add, pow_mul] using he
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

open Subgroup Equiv
open CFSG.Quasithin
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem component_le_actor (K L T : Subgroup G) (v : G) : K ≤ plusActor K L T v :=
  (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)

omit [Finite G] in
theorem actor_eq (K L T : Subgroup G) (v : G)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusActor K L T v = K ⊔ Tv T v := by
  have hm : Kminus K T v = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hK) (le_conjugateSpanBy _ _)
  rw [plusActor, hm, sup_eq_left.mpr hLK]

omit [Finite G] in
theorem plus_kernel_isPGroup (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7))) :
    IsPGroup 2 (plusMk K L T z v hL hz).ker := by
  let H := plusActor K L T v
  let q := plusMk K L T z v hL hz
  have hKH : K ≤ H := component_le_actor K L T v
  have hTH : Tv T v ≤ H := le_sup_right
  let A := K.subgroupOf H
  let R := (Tv T v).subgroupOf H
  let f : K →* Gplus K L T z v hL hz := q.comp (inclusion hKH)
  have hf : f.ker = pCore 2 K := by
    ext k
    change q ⟨k, hKH k.property⟩ = 1 ↔ k ∈ pCore 2 K
    rw [← hφ.eq_iff, φ.map_one, hcompat]
    change (blockProjection K e k : Perm (Fin 7)) = 1 ↔ _
    change (blockProjection K e k : Perm (Fin 7)) = ((1 : alternatingGroup (Fin 7)) : Perm (Fin 7)) ↔ _
    rw [← Subtype.ext_iff]
    change k ∈ (blockProjection K e).ker ↔ _
    rw [blockProjection_kernel]
  have hn : H ≤ normalizer (K : Set G) := by
    rw [show H = K ⊔ Tv T v from actor_eq K L T v hK hLK]
    exact sup_le K.le_normalizer hK
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  have hgen : A ⊔ R = ⊤ := by
    rw [← subgroupOf_sup hKH hTH, ← actor_eq K L T v hK hLK]
    exact subgroupOf_self _
  have hfA : IsPGroup 2 (q.comp A.subtype).ker := by
    have he : q.comp A.subtype = f.comp (subgroupOfEquivOfLe hKH).toMonoidHom := rfl
    rw [he, ← MonoidHom.comap_ker, hf]
    exact pCore_isPGroup.comap_of_injective _ (subgroupOfEquivOfLe hKH).injective
  exact kernel_isPGroup_of_supplement A R q hT.comap_subtype hgen hfA

theorem plus_normalizer_comparison (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7))) :
    plusImage K L T z v hL hz (K ⊓ normalizer (S : Set G)) =
      plusImage K L T z v hL hz K ⊓
        normalizer (plusImage K L T z v hL hz S : Set _) := by
  have hSyl : Chapter1.IsSylowIn 2 (Tv T v) (K ⊔ Tv T v) := hY.1.2.2.1
  have hT : IsPGroup 2 (Tv T v) := (Chapter1.isSylowIn_iff.mp hSyl).1
  have hk := plus_kernel_isPGroup K L T z v hL hz hK hLK hT e φ hφ hcompat
  rw [← actor_eq K L T v hK hLK] at hSyl
  obtain ⟨P, hP⟩ := hSyl
  have hkT : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v) := by
    intro x hx
    change (x : G) ∈ Tv T v
    rw [← hP]
    exact ⟨x, hk.le_sylow_of_normal P hx, rfl⟩
  exact image_relative_normalizer (plusActor K L T v) K (Tv T v) S
    (plusMk K L T z v hL hz) le_sup_right hS hkT
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
variable {G Q : Type*} [Group G] [Group Q]
theorem map_relative_normalizer_of_injective
    (K S : Subgroup G) (f : G →* Q) (hf : Function.Injective f) :
    (K ⊓ normalizer (S : Set G)).map f =
      K.map f ⊓ normalizer (S.map f : Set Q) := by
  have he : (normalizer (S.map f : Set Q)).comap f = normalizer (S : Set G) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range f S),
      comap_map_eq_self_of_injective hf]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha.1, rfl⟩, S.le_normalizer_map f ⟨a, ha.2, rfl⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, hn⟩
    exact ⟨a, ⟨ha, he ▸ hn⟩, rfl⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
end
