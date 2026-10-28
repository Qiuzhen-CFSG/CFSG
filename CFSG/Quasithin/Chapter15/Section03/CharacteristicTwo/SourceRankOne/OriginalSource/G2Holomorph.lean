module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2WholeCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Actual free-holomorph geometry for the original G₂ source

Realize the original Sylow pair inside the generic MS93 amalgam. Its local
two-residual is the source component, and the commutator core pulls back to
[O₂(L),L] through the literal embeddings. Characteristic two excludes critical
distance zero. A whole-core bound in the omega-center then gives the elementary
and central conditions consumed by the existing G₂ terminal.

The core identity from MS93 (3.6) and full natural coordinates from (3.2)(vii)
remain explicit in the final application; a natural constituent alone does not
supply them. Source: Meierfrankenfeld–Stellmacher (1993), §§2–3, pp.854–877;
Aschbacher–Smith C.1.32 and 15.3.31, pp.136,1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open EightGeometry.NaturalModule.Recognition ChapterC
open Stellmacher.PushingUp.AmalgamGraph
namespace G2Holomorph
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

omit [Finite G] in
theorem edge_eq_sylow : d.S.subgroupOf I = (s.sylow : Subgroup I) := by
  apply map_injective I.subtype_injective
  exact (map_subgroupOf_eq_of_le
    ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1)).trans s.sylow_eq.symm

include s

omit [Finite G] in
theorem edge_two_group : IsPGroup 2 (d.S.subgroupOf I) :=
  by
  rw [edge_eq_sylow s]
  exact s.sylow.isPGroup'

omit [Finite G] in
theorem core_le_edge : pCore 2 I ≤ d.S.subgroupOf I := by
  rw [(edge_eq_sylow s)]
  exact pCore_isPGroup.le_sylow_of_normal s.sylow

theorem edge_ne_bot : d.S.subgroupOf I ≠ ⊥ := by
  intro he
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1
  have hS : d.S=⊥ := by
    have hh := congrArg (map I.subtype) he
    simpa only [map_subgroupOf_eq_of_le hSI,Subgroup.map_bot] using hh
  have hZS : d.ZS ≤ d.S := d.action.fixedPlane_le_stabilizer d.T d.sylow_le
    (localModule_le d.T d.sylow_le) 1
  have hz : d.ZS=⊥ := le_bot_iff.mp (hS ▸ hZS)
  have hh := s.omega.2
  rw [hz,Subgroup.card_bot] at hh
  norm_num at hh

omit [Finite G] in
theorem edge_characteristic : MSCharacteristicCondition (d.S.subgroupOf I) := by
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1
  let R := d.S.subgroupOf I
  let e : R ≃* d.S := subgroupOfEquivOfLe hSI
  intro C hC hne hn
  let D := C.map e.toMonoidHom
  have hD : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let b : MulAut R := e.trans (a.trans e.symm)
    exact ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,e.apply_symm_apply _⟩
  have hDne : D ≠ ⊥ := fun hz => hne ((map_eq_bot_iff_of_injective C e.injective).mp hz)
  have he : (D.map d.S.subtype).subgroupOf I = C.map R.subtype := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans hSI),map_map,map_map]
    rfl
  exact s.characteristic D hD hDne (he.symm ▸ hn)

theorem residual_eq_component : pResidual 2 I = c.L.subgroupOf I := by
  let := s.normal
  let : Group.IsPerfect c.L := component_isPerfect_of_containment d c s.contains
  let : Group.IsPerfect (c.L.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe (component_le c)).symm.toMonoidHom)
      (subgroupOfEquivOfLe (component_le c)).symm.surjective
  have hp : IsPPerfect 2 (c.L.subgroupOf I) := by
    intro N hn hq
    let := hn
    have hs : Subsingleton ((c.L.subgroupOf I) ⧸ N) := by
      by_contra! hnt
      exact Group.IsPerfect.not_isNilpotent _ hq.isNilpotent
    apply eq_top_iff.mpr
    intro l _
    exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
  apply pResidual_eq_of_isPPerfect_sup (c.L.subgroupOf I) (d.S.subgroupOf I) hp (edge_two_group s)
  rw [←subgroupOf_sup (component_le c)
    ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]

/-- The actual free holomorph has critical endpoints and the generic MS geometry. -/
theorem geometry : BinaryMS.MS93.Geometry (d.S.subgroupOf I) :=
  BinaryMS.MS93.geometry _ (edge_two_group s) (edge_ne_bot s) (edge_characteristic s)

theorem Q_pullback :
    (BinaryMS.MS93.Q (d.S.subgroupOf I) (BinaryMS.MS93.alpha (d.S.subgroupOf I))).comap
      (embedM (d.S.subgroupOf I)) = pCore 2 I :=
  BinaryMS.MS93.Q_alpha_comap _ (edge_two_group s) (core_le_edge s)

theorem residual_embedded :
    BinaryMS.MS93.Ltilde (d.S.subgroupOf I) (BinaryMS.MS93.alpha (d.S.subgroupOf I)) =
      (c.L.subgroupOf I).map (embedM (d.S.subgroupOf I)) := by
  rw [BinaryMS.MS93.Ltilde_alpha,(residual_eq_component s)]

theorem core_pullback :
    ((BinaryMS.MS93.core (d.S.subgroupOf I) (BinaryMS.MS93.alpha (d.S.subgroupOf I))).comap
      (embedM (d.S.subgroupOf I))).map I.subtype = extensionCore c.L := by
  rw [BinaryMS.MS93.core_alpha _ (edge_two_group s) (core_le_edge s) (residual_eq_component s),
    comap_map_eq_self_of_injective (embedM_injective _),map_commutator,
    map_subgroupOf_eq_of_le (component_le c)]
  exact (extensionCore_eq_overgroup d c s.contains s.normal).symm

open BinaryMS.MS93

/-- Omega-centers commute with the literal source embedding. -/
theorem X_pullback :
    (X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))).comap
      (embedM (d.S.subgroupOf I)) = omegaCenter (pCore 2 I) := by
  rw [X, Q_alpha _ (edge_two_group s) (core_le_edge s),
    omegaCenter_map _ _ (embedM_injective _),
    comap_map_eq_self_of_injective (embedM_injective _)]

/-- The source characteristic-two condition excludes critical distance zero. -/
theorem positive_distance : 0 < (geometry s).b (d.S.subgroupOf I) := by
  by_contra! hb
  have hz : (geometry s).b (d.S.subgroupOf I) = 0 := Nat.eq_zero_of_le_zero hb
  obtain ⟨a', hd, hne⟩ := criticalPair_exists (d.S.subgroupOf I)
    (alpha (d.S.subgroupOf I)) ((geometry s).exists_critical _ rfl)
  have ha' : alpha (d.S.subgroupOf I) = a' :=
    (cosetGraph_connected _).dist_eq_zero_iff.mp (hd.trans hz)
  subst a'
  apply hne
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y : I, embedM (d.S.subgroupOf I) y = x := by
    have hm := Z_le_stabilizer (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) hx
    rw [alpha, stabilizer_m_base] at hm
    exact hm
  have hy : y ∈ centralizer (pCore 2 I : Set I) := by
    intro z hz
    apply embedM_injective (d.S.subgroupOf I)
    simpa only [map_mul] using
      (commutator_eq_bot_iff_le_centralizer.mp ((geometry s).centralizes _ rfl) hx)
        (embedM (d.S.subgroupOf I) z)
        ((Q_alpha _ (edge_two_group s) (core_le_edge s)).symm ▸
          mem_map_of_mem (embedM (d.S.subgroupOf I)) hz)
  have hyQ : y ∈ pCore 2 I := by
    rw [← s.characteristicTwo] at hy ⊢
    exact centralizer_generalizedFitting_le I hy
  rw [Q_alpha _ (edge_two_group s) (core_le_edge s)]
  exact mem_map_of_mem _ hyQ

/-- The remaining source branch has even critical distance at least two. -/
theorem distance_ge_two : 2 ≤ (geometry s).b (d.S.subgroupOf I) := by
  have hp := positive_distance s
  have he := (geometry s).even (alpha (d.S.subgroupOf I)) rfl
  change Even ((geometry s).b (d.S.subgroupOf I)) at he
  obtain ⟨n, hn⟩ := he
  omega

/-- A whole-core bound in X yields the corresponding bound in the original group. -/
theorem core_le_omegaCenter
    (hX : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))) :
    extensionCore c.L ≤ (omegaCenter (pCore 2 I)).map I.subtype := by
  rw [← core_pullback s, ← X_pullback s]
  exact map_mono (comap_mono hX)

/-- The MS93 whole-core bound makes the original intrinsic block core elementary. -/
theorem blockCore_elementary
    (hX : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))) :
    IsElementaryAbelian 2 (blockU c.L) := by
  let : IsElementaryAbelian 2 (omegaCenter (pCore 2 I)) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((omegaCenter (pCore 2 I)).map I.subtype) :=
    IsElementaryAbelian.map _
  have hle : (blockU c.L).map c.L.subtype ≤ (omegaCenter (pCore 2 I)).map I.subtype := by
    rw [CentralCover.BlockModels.blockU_map]
    exact core_le_omegaCenter s hX
  let f : blockU c.L →* (omegaCenter (pCore 2 I)).map I.subtype :=
    ((c.L.subtype.comp (blockU c.L).subtype).codRestrict _
      (fun x => hle (mem_map_of_mem _ x.property)))
  apply IsElementaryAbelian.of_injective f
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (omegaCenter (pCore 2 I)).map I.subtype => (z : G)) he

/-- The same whole-core bound centralizes O₂(L) with its actual inclusion. -/
theorem blockCore_central
    (hX : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))) :
    blockU c.L ≤ centralizer (pCore 2 c.L : Set c.L) := by
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal
  have hcore : c.L.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
      ((pCoreIn_le 2 c.L).trans (component_le c))
      (hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))
  intro x hx y hy
  have hx' : (x : G) ∈ extensionCore c.L := by
    rw [← CentralCover.BlockModels.blockU_map]
    exact mem_map_of_mem _ hx
  obtain ⟨xI, hxI, hxx⟩ := core_le_omegaCenter s hX hx'
  obtain ⟨yI, hyI, hyy⟩ := hcore (mem_map_of_mem c.L.subtype hy)
  apply Subtype.ext
  change (y : G) * (x : G) = (x : G) * (y : G)
  change (xI : G) = (x : G) at hxx
  change (yI : G) = (y : G) at hyy
  rw [← hxx, ← hyy]
  exact congrArg Subtype.val ((mem_omegaCenter_iff.mp hxI).2.2 yI hyI)

/-- Equality with U reduces the full-core bound to the already proved geometry. -/
theorem core_le_X_of_eq_U
    (hU : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) =
      U (d.S.subgroupOf I) (alpha (d.S.subgroupOf I))) :
    core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) := by
  have hUZ : U (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      Z (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) := by
    apply le_normalizer_iff_commutator_le_left.mp
    exact (map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp
        ((geometry s).Z_normal _))
  exact hU ▸ hUZ.trans ((geometry s).omega_bound _ rfl (positive_distance s))

/-- Literal application to the original G₂ exclusion: the MS93 core bound
replaces both elementary-core and centrality premises. -/
theorem g2_false_of_core_le_X
    (m : Parabolics.RankTwoParabolicMarking d I c.L CentralCover.BlockModels.G2.Actor
      Parabolics.g2DerivedParabolic)
    (hX : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) ≤
      X (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)))
    (model : BlockModuleModel c.L (CentralCover.BlockModels.multiplicativeAction
      CentralCover.BlockModels.G2.action)) : False :=
  source_g2_false_of_elementary_central_core s m (blockCore_elementary s hX)
    (blockCore_central s hX) model

/-- The source (3.6) core identity and the source (3.2)(vii) full natural model
suffice for the original marked G₂ branch. Both source conclusions remain explicit. -/
theorem g2_false_of_core_eq_U
    (m : Parabolics.RankTwoParabolicMarking d I c.L CentralCover.BlockModels.G2.Actor
      Parabolics.g2DerivedParabolic)
    (hU : core (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)) =
      U (d.S.subgroupOf I) (alpha (d.S.subgroupOf I)))
    (model : BlockModuleModel c.L (CentralCover.BlockModels.multiplicativeAction
      CentralCover.BlockModels.G2.action)) : False :=
  g2_false_of_core_le_X s m (core_le_X_of_eq_U s hU) model

end G2Holomorph
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
