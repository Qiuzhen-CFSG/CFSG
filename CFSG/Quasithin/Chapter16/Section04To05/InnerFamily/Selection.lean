module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport

/-!
# Positioning the intersection Sylow subgroup

Given a member of Δ and a Sylow two-subgroup R of its relative normalizer,
conjugation inside N_G(K) puts R into the fixed T while preserving L.
This constructs Notation 16.4.1 from the standard setup and Δ nonemptiness.
The same construction transports a bound proved for this notation back to
every relative Sylow subgroup in the definition of Δ₀.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 16.4.1 and Lemma 16.4.9(1), printed pp.1183 and 1189.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The normalizing conjugator positions the chosen R inside T. -/
theorem StandardSetup.exists_normalized_intersection {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : StandardSetup T z L)
    (hJ : (centralizer (L : Set G)).conjBy g ∈ delta L)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g ⊓
      normalizer (centralizer (L : Set G) : Set G))) :
    ∃ n ∈ normalizer (centralizer (L : Set G) : Set G),
      IntersectionSetup T z L (n * g) (R.conjBy n) := by
  have hTN : (T : Subgroup G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    h.normalizers_eq ▸ h.sylow_normalizes
  have hTS : SylowIn (T : Subgroup G)
      (normalizer (centralizer (L : Set G) : Set G)) :=
    ⟨T.subtype hTN, map_subgroupOf_eq_of_le hTN⟩
  obtain ⟨n, hn, hRn⟩ := SylowIn.exists_conjugate_le hTS hR.isPGroup (hR.le.trans inf_le_right)
  have hnL : L.conjBy n = L := mem_normalizer_iff_map_conj_eq.mp (h.normalizers_eq ▸ hn)
  have hnK : (centralizer (L : Set G)).conjBy n = centralizer (L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp hn
  refine ⟨n, hn, ?_⟩
  refine { toStandardSetup := h, mem_delta := ?_, sylow := ?_, le_sylow := hRn }
  · have hd := mem_delta_map hJ (MulAut.conj n)
    change ((centralizer (L : Set G)).conjBy g).conjBy n ∈ delta (L.conjBy n) at hd
    simpa only [conjBy_conjBy, hnL] using hd
  · have hs := hR.map (MulAut.conj n)
    change SylowIn (R.conjBy n)
      (((centralizer (L : Set G)).conjBy g ⊓ normalizer (centralizer (L : Set G) : Set G)).map
        (MulAut.conj n).toMonoidHom) at hs
    rw [map_inf _ _ _ (MulAut.conj n).injective, map_equiv_normalizer_eq] at hs
    change SylowIn (R.conjBy n) (((centralizer (L : Set G)).conjBy g).conjBy n ⊓
      normalizer ((centralizer (L : Set G)).conjBy n : Set G)) at hs
    simpa only [conjBy_conjBy, hnK] using hs


/-- Construct the chosen setup of 16.4.1 from Δ nonemptiness. -/
theorem StandardSetup.exists_intersectionSetup {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) (hne : (delta L).Nonempty) :
    ∃ g R, IntersectionSetup T z L g R := by
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨g, rfl⟩ := hJ.1
  let H := (centralizer (L : Set G)).conjBy g ⊓
    normalizer (centralizer (L : Set G) : Set G)
  let S : Sylow 2 H := Classical.choice inferInstance
  let R := (S : Subgroup H).map H.subtype
  obtain ⟨n, _, hn⟩ := StandardSetup.exists_normalized_intersection h hJ (show SylowIn R H from ⟨S, rfl⟩)
  exact ⟨n * g, R.conjBy n, hn⟩

/-- A proof of 16.4.9(1) in its source notation covers all relative Sylow choices. -/
theorem StandardSetup.orderTwoOutsideDeltaZero_of_local {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L)
    (hlocal : ∀ (g : G) (R : Subgroup G), IntersectionSetup T z L g R →
      (centralizer (L : Set G)).conjBy g ∉ deltaZero L → Nat.card R = 2) :
    OrderTwoOutsideDeltaZero L := by
  intro J hJ hnot R hR
  obtain ⟨g, rfl⟩ := hJ.1
  obtain ⟨n, hn, hs⟩ := StandardSetup.exists_normalized_intersection h hJ hR
  have hnL : L.conjBy n = L := mem_normalizer_iff_map_conj_eq.mp (h.normalizers_eq ▸ hn)
  have hout : (centralizer (L : Set G)).conjBy (n * g) ∉ deltaZero L := by
    intro hh
    apply hnot
    apply (mem_deltaZero_conjBy_iff n).mp
    simpa only [conjBy_conjBy, hnL] using hh
  have hc := hlocal _ _ hs hout
  change Nat.card (R.map (MulAut.conj n).toMonoidHom) = 2 at hc
  rwa [card_map_of_injective (MulAut.conj n).injective] at hc

end CFSG.Quasithin.Chapter16.Intersections
