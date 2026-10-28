module
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Geometry
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# The opposite component inside the moved normalizer

Let W=[V,L] and let B be the other Sylow conjugate of L. The index-two
stabilizer makes conjugation twice fix W, so the source crossed centralization
also gives [W,B]=1. The opposite component belongs to the local family for the
half-Sylow: its local two-core contains the original nontrivial module.
Original 1.2.4 then places B in a normal C-component of the actual N_G(W).

Source: Aschbacher--Smith, Lemma 10.2.6, printed pp.748--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The given crossed centralization implies its opposite-factor counterpart. -/
theorem source_a5_moved_normalizer_opposite_cross
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ⁅⁅D.fullModule,L⁆, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hW := conjugate_twice_eq_of_index_two ⁅D.fullModule,L⁆ (T : Subgroup G)
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) hR ht
  have hz := congrArg (map (MulAut.conj t).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr hcross)
  rwa [map_commutator, hW, Subgroup.map_bot] at hz

/-- The opposite Sylow conjugate lies in a normal C-component of the actual moved normalizer. -/
theorem source_a5_moved_normalizer_opposite_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ∃ J : Subgroup G,
      J ∈ cComponentsIn (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ∧
      (J.subgroupOf (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))).Normal ∧
      L.map (MulAut.conj t).toMonoidHom ≤ J := by
  let H := normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let B := L.map (MulAut.conj t).toMonoidHom
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hpair : localOrbit T L = L ⊔ B := componentOrbit_eq_sup_of_index_two L T
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    inf_le_right ht htn
  have hBorb : B ≤ localOrbit T L := le_sup_right.trans hpair.ge
  have hBH : B ≤ H := hBorb.trans (source_orbit_le_moved_normalizer D hn)
  have hRH : R ≤ H :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hlocalB : B ∈ Chapter1.L G (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr D.maximal.1
    have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rwa [he] at hh
  have hV : D.moduleSubgroup ≤ R := le_inf D.module_le_sylow
    (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hJT : B ⊔ R ≤ localJoin T L :=
    sup_le (hBorb.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hlocal : B ∈ Chapter1.L G R := by
    refine ⟨hlocalB.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)), ?_, ?_⟩
    · exact (source_a5_moved_normalizer_sylow D e ht htn hcross).restrict
        le_sup_right (sup_le hBH hRH)
    · have hcore : D.moduleSubgroup ≤ (B ⊔ R).pCoreIn 2 :=
        le_pCoreIn_of_normalizes D.module_elementary.isPGroup (hV.trans le_sup_right)
          (hJT.trans D.join_normalizes_module)
      exact fun he => D.module_ne_bot (bot_unique (hcore.trans_eq he))
  obtain ⟨S,hS⟩ := source_a5_moved_normalizer_sylow D e ht htn hcross
  have hSe : (S : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRH]
  have hloc : B.subgroupOf H ∈ Chapter1.L H S := by
    rw [hSe]
    exact (mem_LIn_iff_subgroupOf hRH hBH).mp ⟨hBH,hlocal⟩
  have hRB : R ≤ normalizer (B : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans (le_normalizer_componentOrbit L T))).trans
      (source_nonnormal_component_normalizer_fixes_opposite D hn ht htn)
  have hSB : (S : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [hSe,←subgroupOf_normalizer_eq hBH]
    exact fun x hx => hRB hx
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hh := source_moved_normalizer_sqtk D
    refine ⟨?_,hh.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hh.stronglyQuasithin p hp hop)
  obtain ⟨I,⟨hI,hBI,hIN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ S hloc hSB
  let J := I.map H.subtype
  have hJH : J ≤ H := map_subtype_le I
  have hBJ : B ≤ J := by
    have hh := map_mono (f := H.subtype) hBI
    rwa [map_subgroupOf_eq_of_le hBH] at hh
  have hJI : J.subgroupOf H = I :=
    comap_map_eq_self_of_injective H.subtype_injective I
  have hJ : J ∈ cComponentsIn H := by
    exact ⟨hJH,hJI.symm ▸ hI⟩
  have hJN : (J.subgroupOf H).Normal := by
    exact hJI.symm ▸ hIN
  exact ⟨J,hJ,hJN,hBJ⟩

end CFSG.Quasithin.Chapter10
