module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Matrix
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.AmalgamLocalCores

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Intrinsic

/-!
# Intrinsic roots and normal generation in original 4.3.6

The marked matrix embedding identifies the full source module with the plane
radical, its fixed subgroup with the short root, and the second subgroup's
two-core with the point radical. The two matrix generation calculations thus
give normal generation of the second subgroup by the full module and place
its two-core in the root-normalizer span.

The marked Sylow identifies the literal intersection T ∩ L with the standard
unipotent subgroup. Transporting the intrinsic commutator formula then proves
that T normalizes the long root. The final application discharges that premise
and full-module generation in the existing contradiction consumer. The
root-core decomposition, FF equality and secondary-component premises remain
explicit; this module does not assert the completed ordinary contradiction.

Source: Aschbacher--Smith 4.3.6, printed pp.614--615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace OrdinarySymplecticMarking
variable {c : SourceConfiguration T L} {n : ℕ}

theorem planeRadical_image (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    ((Plane.radical (F := m.Field)).map planeLocal.subtype).map m.modelEmbedding =
      c.ordinaryModule := by
  have hh := AmalgamLocalCores.pCoreIn_map_of_injective 2
    m.modelEmbedding m.modelEmbedding_injective (planeLocal (F := m.Field))
  rw [m.planeLocal_image] at hh
  simp only [pCoreIn, planeLocal_core_eq m.card hn] at hh
  exact hh.symm.trans m.full_module.symm

theorem pointRadical_image (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    ((pointRadical (F := m.Field)).map pointLocal.subtype).map m.modelEmbedding =
      m.second.pCoreIn 2 := by
  rw [← m.pointLocal_image hn,
    AmalgamLocalCores.pCoreIn_map_of_injective 2 _ m.modelEmbedding_injective,
    pCoreIn, pointLocal_core_eq m.card hn]

theorem fullModule_le_second (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    c.ordinaryModule ≤ m.second := by
  rw [← m.planeRadical_image hn, ← m.pointLocal_image hn]
  exact map_mono OrdinaryRootCoreMatrix.plane_radical_le_point

theorem fullModule_conjugateSpan_second (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    conjugateSpanBy c.ordinaryModule m.second = m.second := by
  rw [← m.planeRadical_image hn, ← m.pointLocal_image hn, ← map_conjugateSpanBy,
    OrdinaryRootCoreMatrix.plane_radical_span m.card hn]

theorem shortRoot_image (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    (RootSubgroup.group (F := m.Field) 4).map m.modelEmbedding =
      c.ordinaryModule ⊓ centralizer (L : Set G) := by
  have hh := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective
    ((Plane.radical (F := m.Field)).map planeLocal.subtype) planeLocal
  rw [m.planeRadical_image hn, m.planeLocal_image,
    OrdinaryRootCoreMatrix.plane_fixed_eq_root_four] at hh
  exact hh.symm

theorem second_le_rootNormalizer (m : OrdinarySymplecticMarking c n) :
    m.second ≤ m.rootNormalizer := (map_subtype_le _).trans inf_le_right

theorem rootSpan_le_rootNormalizer (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    m.rootSpan ≤ m.rootNormalizer :=
  conjugateSpanBy_le_self (inf_le_left.trans
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer))

theorem second_core_conjugateSpan (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    conjugateSpanBy (c.ordinaryModule ⊓ centralizer (L : Set G)) m.second =
      m.second.pCoreIn 2 := by
  rw [← m.shortRoot_image hn, ← m.pointLocal_image hn, ← map_conjugateSpanBy,
    OrdinaryRootCoreMatrix.root_four_span m.card hn]
  rw [AmalgamLocalCores.pCoreIn_map_of_injective 2 _ m.modelEmbedding_injective,
    pCoreIn, pointLocal_core_eq m.card hn]

theorem second_core_le_rootSpan (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    m.second.pCoreIn 2 ≤ m.rootSpan := by
  rw [← m.second_core_conjugateSpan hn]
  exact conjugateSpanBy_mono le_rfl m.second_le_rootNormalizer

theorem unipotent_image (m : OrdinarySymplecticMarking c n) :
    (unipotent (F := m.Field)).map m.modelEmbedding = (T : Subgroup G) ⊓ L := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have hb : m.componentEquiv.symm a ∈
          (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf c.K := by
        obtain ⟨b, hb, he⟩ := m.sylow.ge ha
        have he' : b = m.componentEquiv.symm a := m.componentEquiv.injective
          (he.trans (m.componentEquiv.apply_symm_apply a).symm)
        exact he' ▸ hb
      exact hb.1
    · exact m.planeLocal_image.le (mem_map_of_mem m.modelEmbedding ha.2)
  · rintro x ⟨hxT, hxL⟩
    obtain ⟨a, ha, he⟩ := m.planeLocal_image.ge hxL
    refine ⟨a, ?_, he⟩
    have hb : m.componentEquiv.symm a ∈
        (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf c.K :=
      ⟨he.symm ▸ hxT, (m.componentEquiv.symm a).val.property⟩
    have hh := m.sylow.le (mem_map_of_mem m.componentEquiv.toMonoidHom hb)
    change m.componentEquiv (m.componentEquiv.symm a) ∈ unipotent at hh
    change a ∈ unipotent
    simpa only [MulEquiv.apply_symm_apply] using hh

theorem sylowNormalizer_image (m : OrdinarySymplecticMarking c n) :
    (planeLocal (F := m.Field) ⊓ normalizer (unipotent (F := m.Field) : Set (Sp m.Field))).map
        m.modelEmbedding = L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  have hpre : (normalizer ((unipotent (F := m.Field)).map m.modelEmbedding : Set G)).comap
      m.modelEmbedding = normalizer (unipotent (F := m.Field) : Set (Sp m.Field)) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective m.modelEmbedding_injective]
  rw [← m.unipotent_image]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨m.planeLocal_image.le (mem_map_of_mem m.modelEmbedding hx.1),
      hpre.ge hx.2⟩
  · rintro y ⟨hyL, hyN⟩
    obtain ⟨x, hx, he⟩ := m.planeLocal_image.ge hyL
    refine ⟨x, ⟨hx, ?_⟩, he⟩
    apply hpre.le
    change m.modelEmbedding x ∈ normalizer _
    rwa [he]

/-- The source description of Z, using the actual intersection T ∩ L. -/
theorem root_commutator (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    ⁅c.ordinaryModule ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G),
      L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)⁆ = m.root := by
  have hh := congrArg (fun A : Subgroup (Sp m.Field) => A.map m.modelEmbedding)
    (OrdinaryRootCoreMatrix.root_zero_commutator m.card hn)
  rw [map_commutator, ← map_inf_centralizer_of_injective _ m.modelEmbedding_injective,
    m.planeRadical_image hn, m.unipotent_image, m.sylowNormalizer_image, m.root_image] at hh
  exact hh

/-- T normalizes the long root because both entries in its intrinsic
commutator description are T-invariant. -/
theorem sylow_le_rootNormalizer (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (T : Subgroup G) ≤ m.rootNormalizer := by
  have hTL := D.sylow_normalizes_component
  have hTW : (T : Subgroup G) ≤ normalizer (c.ordinaryModule : Set G) := by
    rw [m.full_module]
    exact hTL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hTP : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTL).trans inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ≤ normalizer
      (c.ordinaryModule ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Set G) :=
    (le_inf hTW (hTP.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hTB : (T : Subgroup G) ≤ normalizer
      (L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Set G) :=
    (le_inf hTL (hTP.trans (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change m.root.map (MulAut.conj t).toMonoidHom = m.root
  have hc : (c.ordinaryModule ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).map
      (MulAut.conj t).toMonoidHom = _ :=
    mem_normalizer_iff_map_conj_eq.mp (hTC ht)
  have hb : (L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).map
      (MulAut.conj t).toMonoidHom = _ :=
    mem_normalizer_iff_map_conj_eq.mp (hTB ht)
  rw [← m.root_commutator hn, map_commutator]
  exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆) hc hb

end OrdinarySymplecticMarking

/-- The full-module generation premise of the literal root-module consumer is
now constructed. The root-core decomposition, the FF equality
and the secondary-component premises remain explicit. -/
theorem SourceConfiguration.ordinary_false_of_generated_root_module
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    {n : ℕ} (hn : 1 < n) (m : OrdinarySymplecticMarking c n) (KZ : Subgroup G)
    (hU : m.rootSpan = m.second.pCoreIn 2)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (himage : KZ ≤ m.second ⊔ m.rootCore)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False :=
  c.ordinary_false_of_root_module D hn m KZ (m.sylow_le_rootNormalizer hn D) (m.fullModule_conjugateSpan_second hn)
    hU hQ hKZ himage hnormal
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
