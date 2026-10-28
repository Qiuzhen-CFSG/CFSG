module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Faithful
public import CFSG.Quasithin.Chapter10.SourceA5OddOvergroups
public import Theory.Alternating.FivePairBorel
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The actual Borel placement in the A₅ Hall argument

The HStar intersection with the local join is a proper Sylow overgroup, hence
has only the primes two and three. Projecting its orbit intersection onto the
original A₅ pair places it in the actual Sylow normalizer. Every odd subgroup
there lies in its two-residual, the original B₀. Faithful odd actors are first
placed in L₀ by the separate residual argument.

Source: Aschbacher–Smith, 10.2.3, printed p.745. The Borel is formed before
quotienting, and retains the entire original two-core.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter4
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include D e

omit e in
private theorem orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩

/-- The actual HStar intersection normalizes the original orbit Sylow subgroup. -/
theorem source_a5_hstar_orbit_intersection_normalizes_sylow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ localOrbit T L ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) := by
  let R := localOrbit T L
  let P := H ⊓ localJoin T L
  obtain ⟨S,hS⟩ := orbit_sylow_intersection D
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_⟩ := source_a5_original_product_quotient D e hn ht htn
  have hP6 : IsPGroup 6 P := source_a5_proper_overgroup_six D e hn P
    (le_inf hH.1.1.2 le_sup_right) (source_hstar_inf_localJoin_lt D hH)
  let U := P.subgroupOf R
  have hSU : (S : Subgroup R) ≤ U := by
    rw [hS]
    intro s hs
    exact ⟨hH.1.1.2 hs,(show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hs⟩
  have hquot := Theory.AlternatingFive.pair_six_overgroup_le_sylow_normalizer
    (S.mapSurjective hq) (U.map q) (hP6.comap_subtype.map q) (map_mono hSU)
  have hcore : q.ker ≤ (S : Subgroup R) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  have hUN : U ≤ normalizer (S : Set R) := by
    have hh := map_le_iff_le_comap.mp hquot
    change U ≤ (normalizer ((S : Subgroup R).map q : Set _)).comap q at hh
    rwa [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hcore] at hh
  have hnmap : U.map R.subtype ≤ normalizer ((S : Subgroup R).map R.subtype : Set G) :=
    (map_mono hUN).trans (le_normalizer_map _)
  have hsmap : (S : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
    rw [hS]
    change ((T : Subgroup G).subgroupOf R).map R.subtype = _
    rw [subgroupOf_map_subtype]
  rw [hsmap] at hnmap
  intro x hx
  apply hnmap
  exact ⟨⟨x,hx.2⟩,⟨hx.1,(show R ≤ localJoin T L from le_sup_left) hx.2⟩,rfl⟩

/-- The literal normalizer N_{L₀}(T ∩ L₀), as an ambient subgroup. -/
@[expose] def sourceOrbitSylowNormalizer (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  localOrbit T L ⊓ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G)

/-- The source B₀ is the two-residual of the actual Sylow normalizer. -/
@[expose] def sourceOrbitBorel (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (pResidual 2 (sourceOrbitSylowNormalizer T L)).map (sourceOrbitSylowNormalizer T L).subtype

omit D e in
private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have ho : Odd (Nat.card (A ⧸ N)) := hodd.of_dvd_nat N.index_dvd_card
  have hc : Nat.card (A ⧸ N) = 1 := hp.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat
  exact N.index_eq_one.mp hc

/-- Odd actors already placed in the orbit lie in the original Borel. -/
theorem source_a5_hstar_odd_subgroup_le_borel_of_le_orbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBR : B ≤ localOrbit T L)
    (hodd : Odd (Nat.card B)) : B ≤ sourceOrbitBorel T L := by
  let N := sourceOrbitSylowNormalizer T L
  have hBN : B ≤ N := le_inf hBR ((le_inf hBH hBR).trans
    (source_a5_hstar_orbit_intersection_normalizes_sylow D e hn hH))
  have hBodd : Odd (Nat.card (B.subgroupOf N)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv]
  have hp := le_pResidual_of_isPPerfect (B.subgroupOf N) (odd_twoPerfect hBodd)
  have hh := map_mono (f := N.subtype) hp
  rwa [map_subgroupOf_eq_of_le hBN] at hh

/-- Faithfulness supplies the preceding orbit containment for the original Borel. -/
theorem source_a5_hstar_faithful_odd_subgroup_le_borel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBM : B ≤ D.maximalLocal)
    (hodd : Odd (Nat.card B))
    (hfaith : B ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    B ≤ sourceOrbitBorel T L :=
  source_a5_hstar_odd_subgroup_le_borel_of_le_orbit D e hn hH B hBH
    (source_a5_faithful_odd_subgroup_le_orbit D e hn B hBM hodd hfaith) hodd

end CFSG.Quasithin.Chapter10
