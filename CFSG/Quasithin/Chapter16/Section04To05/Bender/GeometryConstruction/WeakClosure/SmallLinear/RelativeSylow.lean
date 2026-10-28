module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.SylowTransport

/-!
# Retaining an involution while arranging a relative Sylow subgroup

An involution in K′ ∩ T lies in K′ ∩ N_G(K). Its cyclic group extends to
a Sylow subgroup of that relative normalizer. Sylow conjugacy inside
N_G(K) moves this subgroup into T, retaining the involution. The involution
also proves the even-order condition defining Δ; distinctness from K is
preserved by this conjugation.

This is the setup transport needed to apply source 16.4.6 to every conjugate
of Ω₁(R) in the PSL₂(4) argument of Proposition 16.5.1.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Notation
16.4.1 and Lemma 16.4.2, printed p.1183; Proposition 16.5.1, printed p.1194.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear
open Subgroup

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z b r : G} {L : Subgroup G}

/-- Extend the marked involution to an actual relative Sylow, then arrange
Notation 16.4.1 by conjugating inside N_G(K). -/
theorem exists_intersectionSetup_containing_involution
    (h : StandardSetup T z L)
    (hb : (centralizer (L : Set G)).conjBy b ≠ centralizer (L : Set G))
    (hrK : r ∈ (centralizer (L : Set G)).conjBy b) (hrT : r ∈ T)
    (hr2 : orderOf r = 2) :
    ∃ c ∈ normalizer (centralizer (L : Set G) : Set G), ∃ S : Subgroup G,
      IntersectionSetup T z L (c * b) S ∧ MulAut.conj c r ∈ S := by
  let K := centralizer (L : Set G)
  let N := normalizer (K : Set G)
  let H := K.conjBy b ⊓ N
  have hrN : r ∈ normalizer (centralizer (L : Set G) : Set G) := by
    rw [h.normalizers_eq]
    exact h.sylow_normalizes hrT
  have hrH : r ∈ H := ⟨hrK, hrN⟩
  have hd : K.conjBy b ∈ delta L := by
    refine ⟨⟨b, rfl⟩, hb, even_iff_two_dvd.mpr ?_⟩
    rw [← hr2]
    exact H.orderOf_dvd_natCard hrH
  have hQ : zpowers r ≤ H := zpowers_le.mpr hrH
  have hp : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  obtain ⟨P, hP⟩ := (hp.of_equiv (subgroupOfEquivOfLe hQ).symm).exists_le_sylow
  let R₀ := (P : Subgroup H).map H.subtype
  have hR₀ : SylowIn R₀ H := ⟨P, rfl⟩
  have hrR : r ∈ R₀ := by
    have hle : zpowers r ≤ R₀ := by
      rw [← map_subgroupOf_eq_of_le hQ]
      exact map_mono hP
    exact hle (mem_zpowers r)
  obtain ⟨c, hc, hle⟩ := h.sylowIn_normalizer.exists_conjugate_le
    hR₀.isPGroup (hR₀.le.trans inf_le_right)
  have hN := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (K : Set G)).le_normalizer hc)
  change N.map (MulAut.conj c).toMonoidHom = N at hN
  refine ⟨c, hc, R₀.conjBy c, ?_, mem_map_of_mem _ hrR⟩
  refine ⟨h, ?_, ?_, hle⟩
  · have hd' := delta_conjugate hd hc
    simpa only [conjBy_conjBy] using hd'
  · have hm := hR₀.map (MulAut.conj c)
    change SylowIn (R₀.conjBy c) ((K.conjBy b ⊓ N).map _) at hm
    rw [map_inf _ _ _ (MulAut.conj c).injective] at hm
    change SylowIn (R₀.conjBy c) ((K.conjBy b).map (MulAut.conj c).toMonoidHom ⊓
      N.map (MulAut.conj c).toMonoidHom) at hm
    rw [hN] at hm
    change SylowIn (R₀.conjBy c) ((K.conjBy b).conjBy c ⊓ N) at hm
    simpa only [conjBy_conjBy] using hm

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.SmallLinear
