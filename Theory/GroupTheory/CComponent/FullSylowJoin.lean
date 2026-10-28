module
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Sylow
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.QuotientIntersection

/-!
# Full Sylow intersections and missing primes in C-component joins

Pass through the actual ambient two-core quotient, where the C-component
becomes quasisimple. Commuting conjugates transport its prescribed Sylow
subgroup into the original two-group, making that two-group Sylow in the
join. The same component-orbit calculation introduces no factor of three;
the two-group kernel preserves this property on lifting.

Source application: Aschbacher--Smith C.2.4(1), printed p.144, and the
moved-component branch of 13.3.12, printed p.889.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem component_full_sylow_join {p : ℕ} [Fact p.Prime]
    {J R : Subgroup G} (hJ : IsComponent G J) (hR : IsPGroup p R)
    (S : Sylow p J) (hS : (S : Subgroup J).map J.subtype ≤ R) :
    ∃ T : Sylow p (J ⊔ R : Subgroup G),
      (T : Subgroup (J ⊔ R : Subgroup G)) = R.subgroupOf (J ⊔ R) := by
  obtain ⟨P,hP⟩ := hJ.exists_sylow_local_orbit_le (E := J) (D := R) (T := R)
    le_rfl inf_le_right le_rfl S hS
  have h := exists_sylow_join_eq_intersection (componentOrbit J R) R R hR le_rfl
    (le_normalizer_componentOrbit J R) P hP
  rwa [componentOrbit_sup] at h

/-- A two-subgroup containing the ambient two-core and a full Sylow subgroup
of a C-component is Sylow in their join, even if it moves the component. -/
theorem IsCComponent.full_sylow_join {J R : Subgroup G} (hJ : J.IsCComponent)
    [IsQuasisimple (J ⧸ pCore 2 J)] (hR : IsPGroup 2 R)
    (hcore : pCore 2 G ≤ R) (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype ≤ R) :
    ∃ T : Sylow 2 (J ⊔ R : Subgroup G),
      (T : Subgroup (J ⊔ R : Subgroup G)) = R.subgroupOf (J ⊔ R) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := J.map q
  let A := R.map q
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hJ.subnormal.quotient, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hJ)⟩
  let S' : Sylow 2 B := S.mapSurjective (f := q.subgroupMap J) (q.subgroupMap_surjective J)
  have hS' : (S' : Subgroup B).map B.subtype ≤ A := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact mem_map_of_mem q (hS (mem_map_of_mem J.subtype hy))
  obtain ⟨P,hP⟩ := component_full_sylow_join hB (hR.map q) S' hS'
  have h : ∃ P : Sylow 2 ((J ⊔ R).map q),
      (P : Subgroup ((J ⊔ R).map q)) = A.subgroupOf ((J ⊔ R).map q) := by
    rw [Subgroup.map_sup]
    exact ⟨P,hP⟩
  obtain ⟨P,hP⟩ := h
  let D := J ⊔ R
  let f := q.subgroupMap D
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap D).ker
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := G)).comap_subtype
  have hf : Function.Surjective f := q.subgroupMap_surjective D
  refine ⟨P.comapOfKerIsPGroup f hk (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top), ?_⟩
  change (P : Subgroup (D.map q)).comap f = R.subgroupOf D
  rw [hP]
  ext x
  change q (x : G) ∈ R.map q ↔ (x : G) ∈ R
  change (x : G) ∈ (R.map q).comap q ↔ _
  rw [comap_map_eq_self (show q.ker ≤ R from (QuotientGroup.ker_mk' _).trans_le hcore)]

/-- A three-free quasisimple two-core quotient stays three-free after adjoining
a two-subgroup. The actual component image and the two-group kernel are used. -/
theorem IsCComponent.three_free_join {J R : Subgroup G} (hJ : J.IsCComponent)
    [IsQuasisimple (J ⧸ pCore 2 J)] (hR : IsPGroup 2 R)
    (hthree : ¬ 3 ∣ Nat.card (J ⧸ pCore 2 J)) :
    ¬ 3 ∣ Nat.card (J ⊔ R : Subgroup G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := J.map q
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hJ.subnormal.quotient, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hJ)⟩
  have hB3 : ¬ 3 ∣ Nat.card B := by
    rwa [← Nat.card_congr (cComponentTwoCoreQuotientEquiv hJ).toEquiv]
  have hR3 : ¬ 3 ∣ Nat.card (R.map q) := by
    obtain ⟨n,hn⟩ := (hR.map q).exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hD3 := hB.not_dvd_card_local_adjoin Nat.prime_three le_rfl inf_le_right hB3 hR3
  let D := J ⊔ R
  let f := q.subgroupMap D
  have hf : Function.Surjective f := q.subgroupMap_surjective D
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap D).ker
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := G)).comap_subtype
  have hk3 : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  intro hd
  rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
  · apply hD3
    change 3 ∣ Nat.card ((J ⊔ R).map q) at hd
    rwa [Subgroup.map_sup] at hd
  · exact hk3 hd
end Subgroup
