module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Completion
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
/-!
# The actual moved-factor normalizer and its half-Sylow

Let W=[V,L] for the original source module. The original pair stabilizer in M
normalizes L, while the stabilizer of L in M normalizes W. Hence their
intersections with M agree. The normalizer bound for the source half-Sylow
promotes that same subgroup to a Sylow subgroup of the full N_G(W).
Original 1.2.4 then supplies a normal containing C-component; a contrary
moved-factor normalizer makes the containment strict.

Source: Aschbacher--Smith, Lemma 10.2.6, printed pp.748--749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- The original M-stabilizer of L normalizes its actual moved group. -/
theorem source_moved_normalizer_local_containment :
    D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
    (D.maximalLocal_normalizes_fullModule hg.1),mem_normalizer_iff_map_conj_eq.mp hg.2]

/-- The whole original orbit normalizes W, before any point-centralizer control. -/
theorem source_orbit_le_moved_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    localOrbit T L ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
  (le_inf (localOrbit T L).le_normalizer (source_nonnormal_orbit_le_normalizer D hn)).trans
    (source_moved_normalizer_local_containment D)

/-- The literal O₂(L₀T) normalizes the original moved group. -/
theorem source_join_core_le_moved_normalizer :
    (localJoin T L).pCoreIn 2 ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
  (le_inf ((pCoreIn_le 2 _).trans
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)))
    (source_join_core_le_component_normalizer D)).trans
      (source_moved_normalizer_local_containment D)

/-- The original moved normalizer is genuinely a two-local SQTK group. -/
theorem source_moved_normalizer_sqtk :
    IsSQTK KnownSimple.IsKnownSimple
      (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :=
  D.simpleQTKE.twoLocal_sqtk ⟨⁅D.fullModule,L⁆, source_full_moved_ne_bot D,
    (source_original_full_moved_elementary D).isPGroup, rfl⟩

/-- The full N_G(W) retains the literal original half-Sylow. -/
theorem source_a5_moved_normalizer_sylow
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hRM : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      D.maximalLocal ⊓ normalizer (L : Set G) :=
    le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
  have hs := (source_nonnormal_stabilizer_sylow D hn).restrict
    (le_inf (hRM.trans inf_le_left)
      (hRM.trans (source_moved_normalizer_local_containment D)))
    (le_inf inf_le_left (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross))
  exact exists_sylow_eq_of_relative_normalizer_le hs inf_le_right
    (le_inf (inf_le_right.trans (source_a5_sylow_stabilizer_normalizer_le D e hn)) inf_le_left)

/-- A contrary moved-factor normalizer supplies a strict normal overcomponent of L. -/
theorem source_a5_moved_normalizer_enlargement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hout : ¬ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup G,
      K ∈ cComponentsIn (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ∧
      (K.subgroupOf (normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))).Normal ∧ L < K := by
  let H := normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hLH : L ≤ H := normalizer_commutator_ge_right _ _
  have hRH : R ≤ H := (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
    (source_moved_normalizer_local_containment D)
  have hV : D.moduleSubgroup ≤ R := le_inf D.module_le_sylow
    (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hJT : L ⊔ R ≤ localJoin T L :=
    sup_le ((le_componentOrbit L T).trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hlocal : L ∈ Chapter1.L G R := by
    refine ⟨D.maximal.1.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
    · exact (source_a5_moved_normalizer_sylow D e ht htn hcross).restrict
        le_sup_right (sup_le hLH hRH)
    · have hcore : D.moduleSubgroup ≤ (L ⊔ R).pCoreIn 2 :=
        le_pCoreIn_of_normalizes D.module_elementary.isPGroup (hV.trans le_sup_right)
          (hJT.trans D.join_normalizes_module)
      exact fun he => D.module_ne_bot (bot_unique (hcore.trans_eq he))
  obtain ⟨S,hS⟩ := source_a5_moved_normalizer_sylow D e ht htn hcross
  have hSe : (S : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRH]
  have hloc : L.subgroupOf H ∈ Chapter1.L H S := by
    rw [hSe]
    exact (mem_LIn_iff_subgroupOf hRH hLH).mp ⟨hLH,hlocal⟩
  have hSL : (S : Subgroup H) ≤ normalizer (L.subgroupOf H : Set H) := by
    rw [hSe,←subgroupOf_normalizer_eq hLH]
    exact fun x hx => hx.2
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hh := source_moved_normalizer_sqtk D
    refine ⟨?_,hh.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hh.stronglyQuasithin p hp hop)
  obtain ⟨I,⟨hI,hLI,hIN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ S hloc hSL
  let K := I.map H.subtype
  have hKH : K ≤ H := map_subtype_le I
  have hLI' : L ≤ K := by
    have hh := map_mono (f := H.subtype) hLI
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  have hKI : K.subgroupOf H = I := comap_map_eq_self_of_injective H.subtype_injective I
  have hK : K ∈ cComponentsIn H := by
    exact ⟨hKH,hKI.symm ▸ hI⟩
  have hKN : (K.subgroupOf H).Normal := by
    exact hKI.symm ▸ hIN
  refine ⟨K,hK,hKN,lt_of_le_of_ne hLI' ?_⟩
  intro he
  have hHN : H ≤ normalizer (L : Set G) := by
    rw [he]
    exact (normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  exact hout (hHN.trans (source_a5_component_normalizer_le D e hn))
end CFSG.Quasithin.Chapter10
