module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.FixedSpace
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreSurjective

/-!
# The source center preimage in the block branches of 13.6.22

Two-perfect commutator idempotence gives [U,K]=U. The short-group axioms
place U in Z(O₂(K)), so [Z(O₂(K)),K]=U. For a surjection with two-group
kernel, the preimage of the target two-core is O₂(K). The preimage of its
center contains U and therefore has the same commutator with K.

The final application constructs the surjection K→Ǩ inside the literal
C_G(v)/⟨v⟩ and takes precisely the preimage of Z(O₂(Ǩ)). Thus it proves
[Z₀,K]=U for the source Z₀, rather than a freely chosen intermediate group.
Source: Aschbacher–Smith, Lemma 13.6.22, printed pp.932–933.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CenterPreimage

theorem blockU_commutator {K : Type*} [Group K] (h : IsShort K) :
    ⁅blockU K, (⊤ : Subgroup K)⁆ = blockU K := by
  let : Finite K := h.finite
  exact commutator_isPPerfect_idempotent (⊤ : Subgroup K) (pCore 2 K)
    (h.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
      (topEquiv (G := K)).symm.surjective)
    pCore_isPGroup (by rw [normalizer_eq_top])

theorem blockU_le_core_center {K : Type*} [Group K] (h : IsShort K) :
    blockU K ≤ (center (pCore 2 K)).map (pCore 2 K).subtype := by
  intro u hu
  refine ⟨⟨u, blockU_le_core hu⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_iff.mp (h.central hu) x x.property)

theorem core_center_commutator {K : Type*} [Group K] (h : IsShort K) :
    ⁅(center (pCore 2 K)).map (pCore 2 K).subtype, (⊤ : Subgroup K)⁆ = blockU K := by
  apply le_antisymm (commutator_mono (map_subtype_le _) le_rfl)
  change blockU K ≤ _
  rw [← blockU_commutator h]
  exact commutator_mono (blockU_le_core_center h) le_rfl

theorem center_preimage_commutator {K H : Type*} [Group K] [Group H]
    [Finite H] (h : IsShort K) (f : K →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ⁅((center (pCore 2 H)).map (pCore 2 H).subtype).comap f,
      (⊤ : Subgroup K)⁆ = blockU K := by
  let : Finite K := h.finite
  have hcore : (pCore 2 H).comap f = pCore 2 K :=
    f.comap_pCore_of_ker_isPGroup hf hk
  have hzle : ((center (pCore 2 H)).map (pCore 2 H).subtype).comap f ≤ pCore 2 K := by
    rw [← hcore]
    exact comap_mono (map_subtype_le _)
  have hmap : (pCore 2 K).map f = pCore 2 H := by
    rw [← hcore, map_comap_eq_self_of_surjective hf]
  have hu : blockU K ≤ ((center (pCore 2 H)).map (pCore 2 H).subtype).comap f := by
    intro u hu
    refine ⟨⟨f u, ?_⟩, ?_, rfl⟩
    · rw [← hmap]
      exact mem_map_of_mem f (blockU_le_core hu)
    · apply mem_center_iff.mpr
      intro x
      have hx : (x : H) ∈ (pCore 2 K).map f := by
        rw [hmap]; exact x.property
      obtain ⟨y, hy, he⟩ := hx
      apply Subtype.ext
      change (x : H) * f u = f u * (x : H)
      rw [← he, ← map_mul, ← map_mul]
      exact congrArg f (mem_centralizer_iff.mp (h.central hu) y hy)
  apply le_antisymm (commutator_mono hzle le_rfl)
  change blockU K ≤ _
  rw [← blockU_commutator h]
  exact commutator_mono hu le_rfl

variable {G : Type*} [Group G]

def checkedKMap (K : Subgroup G) (v : G) (hK : K ≤ Gv v) : K →* checkedImage v K :=
  ((checkedQuotientMap v).comp (inclusion hK)).codRestrict _ (by
    intro k
    exact ⟨inclusion hK k, k.property, rfl⟩)

theorem checkedKMap_surjective (K : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    Function.Surjective (checkedKMap K v hK) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem checkedKMap_kernel (K : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    (checkedKMap K v hK).ker = (vLine v).comap (inclusion hK) := by
  ext k
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change (QuotientGroup.mk (inclusion hK k) : Gcheck v) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

theorem checkedKMap_pKernel (K : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hv : v ^ 2 = 1) : IsPGroup 2 (checkedKMap K v hK).ker := by
  have hp : IsPGroup 2 (vLine v) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change Nat.card (zpowers (centralElement v)) ∣ 2 ^ 1
    rw [Nat.card_zpowers]
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one
      (show centralElement v ^ 2 = 1 from Subtype.ext hv)
  rw [checkedKMap_kernel]
  exact hp.comap_of_injective (inclusion hK) (inclusion_injective hK)

noncomputable def sourceZ0 (K : Subgroup G) (v : G) (hK : K ≤ Gv v) : Subgroup G :=
  (((center (pCore 2 (checkedImage v K))).map (pCore 2 (checkedImage v K)).subtype).comap
    (checkedKMap K v hK)).map K.subtype

theorem sourceZ0_commutator [Finite G] (K : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1) (h : IsShort K) :
    ⁅sourceZ0 K v hK, K⁆ = (blockU K).map K.subtype := by
  let : Finite (Gcheck v) := inferInstanceAs (Finite (Gv v ⧸ vLine v))
  have ht : (⊤ : Subgroup K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hc := congrArg (Subgroup.map K.subtype)
    (center_preimage_commutator h (checkedKMap K v hK)
      (checkedKMap_surjective K v hK) (checkedKMap_pKernel K v hK hv))
  rw [map_commutator, ht] at hc
  exact hc
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CenterPreimage
