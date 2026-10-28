module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Alignment
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Sylow restriction in the paired Suzuki orbit

The actual Sylow subgroup of C_G(v) restricts to T₀ = Tᵥ ∩ K₀ because
Tᵥ normalizes K₀. Passing through the central quotient makes an aligned
image equal to the product root group. A two-group center lies in T₀,
so the inverse image is also exact. The lifted Borel consequently
normalizes T₀, its first omega subgroup, and its centralizer inside T₀.

These statements do not identify the centralizer inside the larger Tᵥ.
That step must retain the kernel of its action on K₀.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 / PDF p.944.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
private theorem restrict_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (N : Subgroup G) (hn : (P : Subgroup G) ≤ normalizer (N : Set G)) :
    ∃ Q : Sylow 2 N, (Q : Subgroup N) = (P : Subgroup G).subgroupOf N := by
  obtain ⟨R, hR⟩ := (P.subtype hn).exists_subgroupOf_eq_of_normal
    (N.subgroupOf (normalizer (N : Set G)))
  let e := subgroupOfEquivOfLe N.le_normalizer
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (R : Subgroup _).map e.toMonoidHom = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, N.le_normalizer x.property⟩, x.property⟩, hx, rfl⟩

/-- Restrict the actual Sylow subgroup of C_G(v) to its normalized component orbit. -/
theorem intersection_sylow {G : Type*} [Group G] [Finite G] (T K : Subgroup G) (v : G)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) :
    ∃ Q : Sylow 2 (orbit T K v), (Q : Subgroup (orbit T K v)) =
      (Tv T v).subgroupOf (orbit T K v) := by
  have hO : orbit T K v ≤ Gv v :=
    conjugateSpanBy_le hK (inf_le_right.trans (Gv v).le_normalizer)
  let N := (orbit T K v).subgroupOf (Gv v)
  have hPN : (P : Subgroup (Gv v)) ≤ normalizer (N : Set (Gv v)) := by
    intro x hx
    have hxt : (x : G) ∈ Tv T v := hP ▸ mem_map_of_mem _ hx
    have hxN := le_normalizer_conjugateSpanBy K (Tv T v) hxt
    exact le_normalizer_comap (Gv v).subtype hxN
  obtain ⟨R, hR⟩ := restrict_sylow P N hPN
  let e := subgroupOfEquivOfLe hO
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (R : Subgroup N).map e.toMonoidHom = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hP ▸ mem_map_of_mem _ hy
  · intro hx
    obtain ⟨y, hy, he⟩ := show (x : G) ∈ (P : Subgroup (Gv v)).map (Gv v).subtype from
      hP.symm ▸ hx
    refine ⟨⟨y, ?_⟩, hy, ?_⟩
    · change (y : G) ∈ orbit T K v
      change (Gv v).subtype y ∈ orbit T K v
      rw [he]
      exact x.property
    · exact Subtype.ext he

variable {G : Type*} [Group G] [Finite G] {T K : Subgroup G} {v : G}

/-- Alignment of the genuine Sylow intersection is equality with the product root group. -/
theorem Marking.aligned_image_eq (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap =
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter) := by
  obtain ⟨Q, hQ⟩ := intersection_sylow T K v P hP hK
  let U := SuzukiRootSubgroup d.parameter
  have hp : IsPGroup 2 (U.prod U) := by
    apply IsPGroup.of_equiv (G := U × U) _ (U.prodEquiv U).symm
    apply IsPGroup.of_card (n := 4 * (2 * d.parameter + 1))
    rw [Nat.card_prod, suzukiRootSubgroup_card d.parameter d.positive, ← pow_mul, ← pow_add]
    congr 1
    omega
  simpa only [Sylow.coe_mapSurjective, hQ] using
    ((Q.mapSurjective d.quotientMap_surjective).is_maximal' hp
    (by simpa only [Sylow.coe_mapSurjective, hQ] using ha)).symm

/-- The full central kernel lies in T₀, so the root preimage is exactly T₀. -/
theorem Marking.aligned_preimage_eq (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    ((SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)).comap
      d.quotientMap = (Tv T v).subgroupOf (orbit T K v) := by
  rw [← d.aligned_image_eq P hP hK ha]
  apply comap_map_eq_self
  rw [d.quotientMap_ker]
  obtain ⟨Q, hQ⟩ := intersection_sylow T K v P hP hK
  exact hQ ▸ hZ.le_sylow_of_normal Q

/-- The lifted Borel normalizes T₀, including in the central-cover case. -/
theorem Marking.borel_normalizes_intersection (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    d.borel ≤ normalizer (intersection T K v : Set G) := by
  have hsingle : SuzukiBorelSubgroup d.parameter ≤ normalizer
      (SuzukiRootSubgroup d.parameter : Set (SuzukiMatrixGroup d.parameter)) := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact sup_le le_normalizer (suzukiSplitTorus_le_normalizer_root _)
  have hn : (SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter) ≤
      normalizer ((SuzukiRootSubgroup d.parameter).prod
        (SuzukiRootSubgroup d.parameter) : Set _) := by
    apply le_normalizer_iff.mpr
    intro b hb u hu
    exact ⟨le_normalizer_iff.mp hsingle b.1 hb.1 u.1 hu.1,
      le_normalizer_iff.mp hsingle b.2 hb.2 u.2 hu.2⟩
  have hpre := (comap_mono (f := d.quotientMap) hn).trans
    (le_normalizer_comap d.quotientMap)
  rw [d.aligned_preimage_eq P hP hK hZ ha] at hpre
  have hamb := (map_mono (f := (orbit T K v).subtype) hpre).trans
    (le_normalizer_map (orbit T K v).subtype)
  simpa only [subgroupOf_map_subtype, Marking.borel, Marking.borelInOrbit, intersection]
    using hamb


/-- The lifted Borel preserves the actual first omega subgroup of T₀. -/
theorem Marking.borel_normalizes_omega (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    d.borel ≤ normalizer (omega T K v : Set G) := by
  let := omega₁_characteristic (intersection T K v) (p := 2)
  exact (d.borel_normalizes_intersection P hP hK hZ ha).trans
    (normalizer_le_normalizer_characteristic_image _ (omega₁ _ (p := 2)))

/-- The lifted Borel preserves C_{T₀}(Ω₁(T₀)). This is not yet C_{Tᵥ}(Ω₁(T₀)). -/
theorem Marking.borel_normalizes_intersection_centralizer (d : Marking T K v)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    d.borel ≤ normalizer
      ((intersection T K v ⊓ centralizer (omega T K v : Set G) : Subgroup G) : Set G) :=
  (le_inf (d.borel_normalizes_intersection P hP hK hZ ha)
    ((d.borel_normalizes_omega P hP hK hZ ha).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
