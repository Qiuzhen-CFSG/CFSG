module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.Residuals
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The two actual components in the strict-orbit branch

The normalizer-index bound from 1.2.1(3) bounds the actual S-conjugacy family.
Strict containment then supplies a moving element of S. Its conjugation swaps
the two members of that family. Ordinary component calculus, used inside I,
proves that they commute. Once the source model comparison gives a trivial
center, they are disjoint and both simple.

The trivial-center premise is explicit: comparing the lists in 1.2.1(3) and
1.1.5(3) is still required for the source application. No ambient normality of
the component is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.39,
printed pp.1137--1138; 1.1.5 and 1.2.1, printed pp.501--504.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

private theorem conjugate_conjugate (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conjugate_subgroupOf {L I : Subgroup G} (hLI : L ≤ I) (s : I) :
    ((L.subgroupOf I).map (MulAut.conj s).toMonoidHom).map I.subtype =
      L.map (MulAut.conj (s : G)).toMonoidHom := by
  rw [map_map]
  have he : I.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : G)).toMonoidHom.comp I.subtype := by ext; rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hLI]

/-- Restrict the source normalizer-index bound to the actual S-orbit. -/
theorem component_orbit_card_le_two [Finite G] {L I S : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I)
    (hi : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) :
    (Set.range fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom).ncard ≤ 2 := by
  let F := Set.range fun i : I => (L.subgroupOf I).map (MulAut.conj i).toMonoidHom
  have hsub : (Set.range fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⊆
      Subgroup.map I.subtype '' F := by
    rintro K ⟨s, rfl⟩
    exact ⟨_, ⟨⟨s, hSI s.property⟩, rfl⟩,
      map_conjugate_subgroupOf hLI ⟨s, hSI s.property⟩⟩
  exact (Set.ncard_le_ncard hsub ((Set.finite_range _).image _)).trans ((Set.ncard_image_le (f := Subgroup.map I.subtype) (Set.finite_range _)).trans
    ((ncard_conjugates_eq_index_normalizer (L.subgroupOf I)).le.trans hi))

/-- A moving member of a two-element conjugacy orbit swaps its two members. -/
theorem exists_swapping_conjugate [Finite G] {L S : Subgroup G}
    (hstrict : L < componentOrbit L S)
    (hbound : (Set.range fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom).ncard ≤ 2) :
    ∃ s : S, L.map (MulAut.conj (s : G)).toMonoidHom ≠ L ∧
      componentOrbit L S = L ⊔ L.map (MulAut.conj (s : G)).toMonoidHom ∧
      (L.map (MulAut.conj (s : G)).toMonoidHom).map (MulAut.conj (s : G)).toMonoidHom = L := by
  classical
  have hm : ∃ s : S, L.map (MulAut.conj (s : G)).toMonoidHom ≠ L := by
    by_contra! hn
    exact (not_le_of_gt hstrict) (iSup_le fun s => (hn s).le)
  obtain ⟨s, hs⟩ := hm
  have hpair : ({L, L.map (MulAut.conj (s : G)).toMonoidHom} : Set (Subgroup G)) =
      Set.range (fun a : S => L.map (MulAut.conj (a : G)).toMonoidHom) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.finite_range _)
    · intro K hK
      rcases Set.mem_insert_iff.mp hK with rfl | hK
      · exact ⟨1, by simp only [Subgroup.coe_one, map_one]; change K.map (MonoidHom.id G) = K; exact Subgroup.map_id K⟩
      · exact ⟨s, (Set.mem_singleton_iff.mp hK).symm⟩
    · simpa only [Set.ncard_pair hs.symm] using hbound
  have htwo (a : S) : L.map (MulAut.conj (a : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj (s : G)).toMonoidHom := by
    have h : L.map (MulAut.conj (a : G)).toMonoidHom ∈
        ({L, L.map (MulAut.conj (s : G)).toMonoidHom} : Set (Subgroup G)) :=
      hpair ▸ ⟨a, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  refine ⟨s, hs, componentOrbit_eq_sup_of_two_conjugates L S s htwo, ?_⟩
  rcases htwo (s * s) with h | h
  · simpa only [conjugate_conjugate, Subgroup.coe_mul] using h
  · have hfix : (L.map (MulAut.conj (s : G)).toMonoidHom).map
        (MulAut.conj (s : G)).toMonoidHom = L.map (MulAut.conj (s : G)).toMonoidHom := by
      simpa only [conjugate_conjugate, Subgroup.coe_mul] using h
    exact (hs (Subgroup.map_injective (MulAut.conj (s : G)).injective hfix)).elim

private theorem disjoint_of_centerless_of_commuting {A B : Subgroup G}
    (hZ : center A = ⊥) (hc : A ≤ centralizer (B : Set G)) : Disjoint A B := by
  apply Subgroup.disjoint_def.mpr
  intro x hxA hxB
  have hz : (⟨x, hxA⟩ : A) ∈ center A := by
    rw [mem_center_iff]
    intro a
    exact Subtype.ext ((le_centralizer_iff.mp hc) hxB a a.property)
  exact congrArg Subtype.val (show (⟨x, hxA⟩ : A) = 1 from by simpa only [hZ, mem_bot] using hz)

/-- Distinct conjugates of a relative component commute in the ambient group.
The centerless hypothesis, to be supplied by the source model comparison,
then makes their product direct. No ambient normality is required. -/
theorem relative_component_conjugate_disjoint_commuting {L I : Subgroup G}
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hZ : center L = ⊥) (s : I)
    (hne : L.map (MulAut.conj (s : G)).toMonoidHom ≠ L) :
    Disjoint L (L.map (MulAut.conj (s : G)).toMonoidHom) ∧
      L ≤ centralizer (L.map (MulAut.conj (s : G)).toMonoidHom : Set G) := by
  have hne' : L.subgroupOf I ≠ (L.subgroupOf I).map (MulAut.conj s).toMonoidHom := by
    intro he
    have he' := congrArg (Subgroup.map I.subtype) he
    rw [map_subgroupOf_eq_of_le hLI, map_conjugate_subgroupOf hLI s] at he'
    exact hne he'.symm
  have hh := congrArg (Subgroup.map I.subtype)
    (hL.commutator_eq_bot_of_ne (hL.map_conj s) hne')
  rw [map_commutator, map_subgroupOf_eq_of_le hLI,
    map_conjugate_subgroupOf hLI s, Subgroup.map_bot] at hh
  have hc := commutator_eq_bot_iff_le_centralizer.mp hh
  exact ⟨disjoint_of_centerless_of_commuting hZ hc, hc⟩

/-- Once the source comparison kills the center, both actual components
are simple, by the ordinary component definition and conjugation. -/
theorem relative_component_conjugates_simple {L I : Subgroup G}
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hZ : center L = ⊥) (s : G) :
    IsSimpleGroup L ∧ IsSimpleGroup (L.map (MulAut.conj s).toMonoidHom) := by
  let := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  have hh : IsSimpleGroup (L ⧸ (⊥ : Subgroup L)) :=
    (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hZ)).mp IsQuasisimple.simple
  have hs : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).mp hh
  exact ⟨hs, (MulEquiv.isSimpleGroup_congr ((MulAut.conj s).subgroupMap L)).mp hs⟩

/-- An S-invariant component is normal in I once the source orbit bound
and the actual Sylow realization of S are available. -/
theorem relative_normal_of_componentOrbit_eq [Finite G] {L I S : Subgroup G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hi : (normalizer (L.subgroupOf I : Set I)).index ≤ 2)
    (he : L = componentOrbit L S) : (L.subgroupOf I).Normal := by
  have hSN : S ≤ normalizer (L : Set G) := by
    conv_rhs => rw [he]
    exact le_normalizer_componentOrbit L S
  have hPN : (P : Subgroup I) ≤ normalizer (L.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hLI]
    intro p hp
    exact hSN (hP ▸ (show (p : G) ∈ (P : Subgroup I).map I.subtype from ⟨p, hp, rfl⟩))
  have hnot : ¬ 2 ∣ (normalizer (L.subgroupOf I : Set I)).index :=
    fun h => P.not_dvd_index (h.trans (index_dvd_of_le hPN))
  have hpos := (normalizer (L.subgroupOf I : Set I)).index_ne_zero_of_finite
  have hidx : (normalizer (L.subgroupOf I : Set I)).index = 1 := by omega
  exact normalizer_eq_top_iff.mp (index_eq_one.mp hidx)

end CFSG.Quasithin.Chapter15.Section03.RankTwo
