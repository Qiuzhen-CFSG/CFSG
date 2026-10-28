module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Intrinsic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Matrix
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The literal ordinary roots before full-normalizer identification

The original matrix embedding gives the long root Z, its full ambient
normalizer, and the second residual K₂ inside K. The two marked local
residuals generate K, and the full module normally generates K₂. The root
commutator formula uses the original T intersection and proves T ≤ N_G(Z).
The previously proved failure of T-normalization of K then gives
T not≤ N_G(K₂), without H = N_G(K).

These are earlier-boundary versions of OrdinaryRootGeometry/OrdinaryRootCore.
The root-core and terminal modules consume these literal maps.
Source: Aschbacher–Smith 4.3.3–6, printed pp.613–615.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace OutsideSymplecticMarking
variable {c : OutsideChoice T L} {K : Subgroup c.H} {n : ℕ}
/-- The marked matrix carrier embedded through the original `K ≤ H ≤ G`. -/
@[expose] noncomputable def modelEmbedding (m : OutsideSymplecticMarking c K n) :
    Sp m.Field →* G :=
  (c.H.subtype.comp K.subtype).comp m.componentEquiv.symm.toMonoidHom

theorem modelEmbedding_injective (m : OutsideSymplecticMarking c K n) :
    Function.Injective m.modelEmbedding :=
  c.H.subtype_injective.comp (K.subtype_injective.comp m.componentEquiv.symm.injective)

theorem modelEmbedding_range (m : OutsideSymplecticMarking c K n) :
    m.modelEmbedding.range = K.map c.H.subtype := by
  have hr : m.componentEquiv.symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr m.componentEquiv.symm.surjective
  rw [modelEmbedding, MonoidHom.range_comp,
    hr, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]

/-- The actual long-root image, using both original subtype maps. -/
@[expose] noncomputable def root (m : OutsideSymplecticMarking c K n) : Subgroup G :=
  (RootSubgroup.group (F := m.Field) 0).map m.modelEmbedding

/-- The full ambient normalizer of that root. -/
@[expose] noncomputable def rootNormalizer (m : OutsideSymplecticMarking c K n) : Subgroup G :=
  normalizer (m.root : Set G)

/-- The literal second residual inside the same original component. -/
@[expose] noncomputable def second (m : OutsideSymplecticMarking c K n) : Subgroup G :=
  (solvableResidual (K.map c.H.subtype ⊓ m.rootNormalizer : Subgroup G)).map
    (K.map c.H.subtype ⊓ m.rootNormalizer).subtype

/-- The span of the original short-root space under the full long-root
normalizer, without an identification with the second component core. -/
@[expose] noncomputable def rootSpan (m : OutsideSymplecticMarking c K n) : Subgroup G :=
  conjugateSpanBy (c.ordinaryModule ⊓ centralizer (L : Set G)) m.rootNormalizer

@[expose] noncomputable def rootCore (m : OutsideSymplecticMarking c K n) : Subgroup G :=
  m.rootNormalizer.pCoreIn 2

theorem planeLocal_image (m : OutsideSymplecticMarking c K n) :
    (planeLocal (F := m.Field)).map m.modelEmbedding = L := by
  have hLH : L ≤ c.H := m.contains.trans (map_subtype_le K)
  have hLK : L.subgroupOf c.H ≤ K := by
    intro x hx
    obtain ⟨k, hk, he⟩ := m.contains hx
    exact (Subtype.ext he : k = x) ▸ hk
  have hm : (planeLocal (F := m.Field)).map m.componentEquiv.symm.toMonoidHom =
      (L.subgroupOf c.H).subgroupOf K :=
    (map_symm_eq_iff_map_eq _ (e := m.componentEquiv)).mpr m.original_local
  rw [modelEmbedding, ← map_map, hm, ← map_map,
    map_subgroupOf_eq_of_le hLK, map_subgroupOf_eq_of_le hLH]

theorem root_image (m : OutsideSymplecticMarking c K n) :
    (RootSubgroup.group (F := m.Field) 0).map m.modelEmbedding = m.root := by
  rfl

/-- The literal root retains the order of the marked field. -/
theorem root_card (m : OutsideSymplecticMarking c K n) :
    Nat.card m.root = 2 ^ n := by
  rw [← m.root_image, card_map_of_injective m.modelEmbedding_injective,
    RootSubgroup.card, m.card]

theorem root_isPGroup (m : OutsideSymplecticMarking c K n) :
    IsPGroup 2 m.root :=
  IsPGroup.of_card m.root_card

theorem root_ne_bot (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    m.root ≠ ⊥ := by
  intro hroot
  have hc := m.root_card
  rw [hroot, card_bot] at hc
  have hgt : 2 < 2 ^ n :=
    (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  omega

/-- This is an ambient two-local, not merely the normalizer in the matrix model. -/
theorem rootNormalizer_twoLocal (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    IsTwoLocal m.rootNormalizer :=
  ⟨m.root, m.root_ne_bot hn, m.root_isPGroup, rfl⟩

theorem pointParabolic_image (m : OutsideSymplecticMarking c K n) :
    (pointParabolic (F := m.Field)).map m.modelEmbedding =
      K.map c.H.subtype ⊓ m.rootNormalizer := by
  have hroot : m.root ≤ m.modelEmbedding.range :=
    m.root_image ▸ map_le_range m.modelEmbedding (RootSubgroup.group (F := m.Field) 0)
  have hpre : m.rootNormalizer.comap m.modelEmbedding = pointParabolic := by
    rw [rootNormalizer, comap_normalizer_eq_of_le_range hroot, ← m.root_image,
      comap_map_eq_self_of_injective m.modelEmbedding_injective,
      RootNormalizerResidual.normalizer_zero_eq]
  rw [← hpre, map_comap_eq, m.modelEmbedding_range]

private theorem map_embedded_residual {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Injective f) (P : Subgroup X) :
    ((solvableResidual P).map P.subtype).map f =
      (solvableResidual (P.map f)).map (P.map f).subtype := by
  let e := P.equivMapOfInjective f hf
  have hh := congrArg (fun D => D.map (P.map f).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  rw [map_map] at hh
  rw [map_map]
  convert hh using 1
  congr 1

theorem pointLocal_image (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    (pointLocal (F := m.Field)).map m.modelEmbedding = m.second := by
  rw [← pointParabolic_solvableResidual_eq m.card hn,
    map_embedded_residual _ m.modelEmbedding_injective, m.pointParabolic_image]
  rfl

theorem original_sup_second (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    L ⊔ m.second = K.map c.H.subtype := by
  calc
    L ⊔ m.second = (planeLocal (F := m.Field)).map m.modelEmbedding ⊔
        (pointLocal (F := m.Field)).map m.modelEmbedding :=
      congrArg₂ (· ⊔ ·) m.planeLocal_image.symm (m.pointLocal_image hn).symm
    _ = K.map c.H.subtype := by
      rw [← Subgroup.map_sup, sup_comm, locals_sup_eq_top m.card hn, ← MonoidHom.range_eq_map,
        m.modelEmbedding_range]

theorem planeRadical_image (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    ((Plane.radical (F := m.Field)).map planeLocal.subtype).map m.modelEmbedding =
      c.ordinaryModule := by
  have hh := AmalgamLocalCores.pCoreIn_map_of_injective 2
    m.modelEmbedding m.modelEmbedding_injective (planeLocal (F := m.Field))
  rw [m.planeLocal_image] at hh
  simp only [pCoreIn, planeLocal_core_eq m.card hn] at hh
  exact hh.symm.trans m.full_module.symm

theorem pointRadical_image (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    ((pointRadical (F := m.Field)).map pointLocal.subtype).map m.modelEmbedding =
      m.second.pCoreIn 2 := by
  rw [← m.pointLocal_image hn,
    AmalgamLocalCores.pCoreIn_map_of_injective 2 _ m.modelEmbedding_injective,
    pCoreIn, pointLocal_core_eq m.card hn]

theorem fullModule_le_second (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    c.ordinaryModule ≤ m.second := by
  rw [← m.planeRadical_image hn, ← m.pointLocal_image hn]
  exact map_mono OrdinaryRootCoreMatrix.plane_radical_le_point

theorem fullModule_conjugateSpan_second (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    conjugateSpanBy c.ordinaryModule m.second = m.second := by
  rw [← m.planeRadical_image hn, ← m.pointLocal_image hn, ← map_conjugateSpanBy,
    OrdinaryRootCoreMatrix.plane_radical_span m.card hn]

theorem unipotent_image (m : OutsideSymplecticMarking c K n) :
    (unipotent (F := m.Field)).map m.modelEmbedding = (T : Subgroup G) ⊓ L := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have hb : m.componentEquiv.symm a ∈
          (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K := by
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
        (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K :=
      ⟨he.symm ▸ hxT, (m.componentEquiv.symm a).val.property⟩
    have hh := m.sylow.le (mem_map_of_mem m.componentEquiv.toMonoidHom hb)
    change m.componentEquiv (m.componentEquiv.symm a) ∈ unipotent at hh
    change a ∈ unipotent
    simpa only [MulEquiv.apply_symm_apply] using hh

theorem sylowNormalizer_image (m : OutsideSymplecticMarking c K n) :
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
theorem root_commutator (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    ⁅c.ordinaryModule ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G),
      L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)⁆ = m.root := by
  have hh := congrArg (fun A : Subgroup (Sp m.Field) => A.map m.modelEmbedding)
    (OrdinaryRootCoreMatrix.root_zero_commutator m.card hn)
  rw [map_commutator, ← map_inf_centralizer_of_injective _ m.modelEmbedding_injective,
    m.planeRadical_image hn, m.unipotent_image, m.sylowNormalizer_image, m.root_image] at hh
  exact hh

/-- T normalizes the long root because both entries in its intrinsic
commutator description are T-invariant. -/
theorem sylow_le_rootNormalizer (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
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

/-- Non-normalization of the same K suffices for the terminal two-generator
obstruction; the full ambient normalizer equality is not needed. -/
theorem second_not_normalized [Finite G] (m : OutsideSymplecticMarking c K n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (ho : IsComponent c.H K)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    ¬ (T : Subgroup G) ≤ normalizer (m.second : Set G) := by
  intro ht
  apply c.ordinary_component_not_normalized_by_sylow D h hpsl K ho m.contains hout hKN
  rw [←m.original_sup_second hn]
  exact (le_inf D.sylow_normalizes_component ht).trans
    (normalizer_inf_normalizer_le_normalizer_sup L m.second)

end OutsideSymplecticMarking
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
