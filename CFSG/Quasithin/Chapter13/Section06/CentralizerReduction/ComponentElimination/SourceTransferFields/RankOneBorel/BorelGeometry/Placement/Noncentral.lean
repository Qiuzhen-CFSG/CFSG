module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Kernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# Thompson noncentrality from the source characteristic obstruction

If J(T_v) lay in the normal two-kernel C_{KT_v}(W_K), heredity would
identify it with the Thompson subgroup of that kernel. Thus it would be
normal in KT_v. Its intrinsic version is characteristic in T_v and is
nontrivial because the source seed is an involution moved by K. This
contradicts the strict characteristic-normalizer assertion of 13.6.16(2).

The block and natural section supply the two-kernel through Kernel.lean.
This discharges E.2.3's noncentrality hypothesis on the literal W_K;
it does not assert the subsequent rank-one image comparison.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.16(2) and 13.6.18, printed pp.930–931; B.2.3(3), p.75.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection HigherFieldParabolics
variable {G D : Type*} [Group G] [Group D] [Finite G]

omit [Finite G] in
private theorem thompson_subgroupOf (S : Subgroup G) :
    (elementaryAbelianMaxJ S).subgroupOf S =
      elementaryAbelianMaxJ (⊤ : Subgroup S) := by
  apply map_injective S.subtype_injective
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  rw [map_subgroupOf_eq_of_le hJS,
    ← elementaryAbelianMaxJ_map_injective S.subtype S.subtype_injective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- If the nontrivial Thompson subgroup lay in the normal two-kernel,
B.2.3(3) would make it normal in KT, contradicting 13.6.16(2). -/
theorem thompson_not_le_kernel (K S : Subgroup G)
    (hS : Chapter1.IsSylowIn 2 S (K ⊔ S))
    (f : (K ⊔ S : Subgroup G) →* D) (hk : IsPGroup 2 f.ker)
    (hne : elementaryAbelianMaxJ S ≠ ⊥)
    (hpush : CharacteristicNormalizerObstruction S K) :
    ¬ (elementaryAbelianMaxJ S).subgroupOf (K ⊔ S) ≤ f.ker := by
  intro h
  let H := K ⊔ S
  let N := f.ker.map H.subtype
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have hNS : N ≤ S := by
    obtain ⟨P, hP⟩ := hS
    exact (map_mono (f := H.subtype) (hk.le_sylow_of_normal P)).trans hP.le
  have hJN : elementaryAbelianMaxJ S ≤ N := by
    have hm := map_mono (f := H.subtype) h
    rwa [map_subgroupOf_eq_of_le (hJS.trans le_sup_right)] at hm
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq N S hNS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S N hJN
  have ho := le_antisymm hsmall.1 hlarge.1
  have he : elementaryAbelianMaxJ S = elementaryAbelianMaxJ N :=
    le_antisymm (hlarge.2 ho.symm) (hsmall.2 ho)
  have hHN : H ≤ normalizer (N : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    change ((f.ker.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hHJ : H ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
    rw [he]
    intro x hx
    have hxN := mem_normalizer_iff_map_conj_eq.mp (hHN hx)
    change N.map (MulAut.conj x).toMonoidHom = N at hxN
    rw [mem_normalizer_iff_map_conj_eq]
    change (elementaryAbelianMaxJ N).map (MulAut.conj x).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x), hxN]
  let C := (elementaryAbelianMaxJ S).subgroupOf S
  have hC : C.Characteristic := by
    rw [show C = elementaryAbelianMaxJ (⊤ : Subgroup S) from thompson_subgroupOf S]
    exact elementaryAbelianMaxJ_top_characteristic
  have hCm : C.map S.subtype = elementaryAbelianMaxJ S := map_subgroupOf_eq_of_le hJS
  have hCne : C ≠ ⊥ := by
    intro hb
    apply hne
    rw [← hCm, hb, Subgroup.map_bot]
  apply (characteristic_exclusion S K hpush C hC hCne)
  apply normal_subgroupOf_of_le_normalizer
  rw [hCm]
  exact hHJ

private theorem thompson_ne_bot_of_seed (S : Subgroup G) (z : G)
    (hz : z ∈ omegaOneCenterAmbient S) (hne : z ≠ 1) :
    elementaryAbelianMaxJ S ≠ ⊥ := by
  have hm := (mem_omegaOneCenterAmbient_iff S z).mp hz
  have he : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hm.2.1
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hc := hA.2.2 (zpowers z) (zpowers_le.mpr hm.1) he
  intro hb
  have hAb : A = ⊥ := bot_unique ((le_sSup hA).trans hb.le)
  have hzcard : Nat.card (zpowers z) ≤ 1 := by simpa [hAb] using hc
  have hzb : zpowers z = ⊥ := (Subgroup.card_le_one_iff_eq_bot (zpowers z)).mp hzcard
  exact hne (by simpa only [hzb, mem_bot] using mem_zpowers z)

/-- The earlier seed and 13.6.16(2) supply E.2.3's actual noncentrality
hypothesis; it is not a requested Borel-normalization premise. -/
theorem local_thompson_noncentral (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hpush : CharacteristicNormalizerObstruction (Tv T v) K) :
    ¬ elementaryAbelianMaxJ (Tv T v) ≤ centralizer (WK K L T z v : Set G) := by
  have hzNe : z ≠ 1 := by
    intro he
    have hm := (invariant_component_consequences K L T z v hK hnorm).1.2
    apply hm
    intro x hx
    rw [he]
    exact mem_centralizer_singleton_iff.mpr (by simp)
  have hnot := thompson_not_le_kernel K (Tv T v) hK.1.2.2.1
    (localMap K L T z v hL hz)
    (localMap_kernel_isPGroup K L T z v hL hz hK hnorm hF hb s)
    (thompson_ne_bot_of_seed (Tv T v) z hzOmega hzNe) hpush
  rw [localMap_ker] at hnot
  exact fun h => hnot (comap_mono h)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement

end
