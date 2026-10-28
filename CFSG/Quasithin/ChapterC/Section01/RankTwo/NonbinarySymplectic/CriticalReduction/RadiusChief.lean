module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ChiefQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChiefInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NoncentralPair

/-!
# The chief-factor argument and radius centrality on the replacement

The full reverse seed is an elementary actor of quotient order at least q².
Its fixed index on the actual radius modulo the full starting seed is at
most q³. The nonbinary symplectic chief budget therefore permits at most
one noncentral factor. MS3 excludes zero such factors, so every chief
series has exactly one. The residual fixed-or-covering alternative applies
to every normal subgroup of the radius.

If radius centrality fails, the earlier root calculation selects a large
critical image at distance four. The proved residual alternative and
abelian edge generation contradict that failure. Transport by the actual
graph action gives centrality at every original-group vertex. The derived
radius lies in X, and the full critical triple commutator vanishes.

This proves MS93 (5.2) for the minimum characteristic replacement at every
original nonbinary field degree. The later shifted-path and terminal
exclusions are still needed to construct a distance-two witness.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed pp.914--915.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h in
/-- The actual replacement projection onto its simple component image. -/
theorem Input.replacement_inner_component_projection
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical) :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    ∃ q : d.overgroup →* C, Function.Surjective q ∧ q.ker = pCore 2 d.overgroup := by
  let π := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map π
  have htop : C = ⊤ := by
    have hpre : C.comap π = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map π from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let q := π.codRestrict C (fun x => htop ▸ mem_top (π x))
  refine ⟨q,?_,?_⟩
  · intro c
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 d.overgroup) c.val
    exact ⟨x,Subtype.ext hx⟩
  · have hker : q.ker = π.ker := by
      ext x
      exact Subtype.ext_iff
    rw [hker,QuotientGroup.ker_mk']

/-- The full radius and full starting seed inside the literal replacement. -/
abbrev chiefRadius (d : CharacteristicReduction K R) : Subgroup d.overgroup :=
  (V d.radical (alpha d.radical)).comap (embedM d.radical)
abbrev chiefSeed (d : CharacteristicReduction K R) : Subgroup d.overgroup :=
  (Z d.radical (alpha d.radical)).comap (embedM d.radical)
instance chiefRadius_normal (d : CharacteristicReduction K R) : (chiefRadius d).Normal :=
  radius_comap_normal
instance chiefSeed_normal (d : CharacteristicReduction K R) : (chiefSeed d).Normal :=
  SymplecticSeed.Z_comap_normal d.radical

/-- The full radius modulo its full seed, in the literal ambient quotient. -/
@[expose] def chiefRadiusQuotient (d : CharacteristicReduction K R) : Subgroup (d.overgroup ⧸ chiefSeed d) :=
  (chiefRadius d).map (QuotientGroup.mk' (chiefSeed d))
instance chiefRadiusQuotient_normal (d : CharacteristicReduction K R) :
    (chiefRadiusQuotient d).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

include h in
/-- The actor and fixed-index budget on the actual radius quotient. -/
theorem Input.replacement_radius_chief_data
    {geometry : Geometry d.radical} {z : Vertex d.radical}
    (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ A : Subgroup d.overgroup, IsElementaryAbelian 2 A ∧
      Nat.card F^2 ≤ (pCore 2 d.overgroup).relIndex A ∧
      (centralizerModulo (chiefRadius d) A (chiefSeed d)).relIndex (chiefRadius d) ≤ Nat.card F^3 := by
  let f := embedM d.radical
  let A := (Z d.radical z).comap f
  let P := (Q d.radical (path.walk.getVert (path.walk.length-2))).comap f
  have hAS : Z d.radical z ≤ f.range := by
    change Z d.radical z ≤ Mbar d.radical
    rw [←stabilizer_m_base]
    exact critical_Z_le_stabilizer d.radical geometry (alpha d.radical) rfl (by change 0 < geometry.b d.radical; omega) path.critical
  have hAm : A.map f = Z d.radical z := map_comap_eq_self hAS
  have hVm : (chiefRadius d).map f = V d.radical (alpha d.radical) :=
    map_comap_eq_self ((geometry.V_local _ rfl (by change 2 < geometry.b d.radical; omega)).trans_eq (stabilizer_m_base d.radical))
  have hZm : (chiefSeed d).map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  let := geometry.Z_elementary (by omega) z path.end_color
  have helem : IsElementaryAbelian 2 A := by
    let j : A →* Z d.radical z := (f.comp A.subtype).codRestrict _ (fun x => x.property)
    exact IsElementaryAbelian.of_injective j
      (fun x y he => Subtype.ext (embedM_injective d.radical (congrArg Subtype.val he)))
  refine ⟨A,helem,?_,?_⟩
  · have he := h.replacement_large_critical_reverse_index d path (by omega) hlarge
    rw [←hAm,Q_alpha d.radical (h.replacement_two_group d) (h.replacement_core_le d),
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical)] at he
    exact he
  · have hcomm : ⁅chiefRadius d ⊓ P,A⁆ ≤ chiefSeed d := by
      apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
      rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective d.radical),hVm,hAm,hZm]
      exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans
        (h.replacement_large_critical_radius_commutator d path hb hlarge)
    have hindex : P.relIndex (chiefRadius d) ≤ Nat.card F^3 := by
      rw [relIndex_comap,hVm]
      exact h.replacement_critical_radius_image_le_cube d path hb
    exact (SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator _ _ _ P hcomm).trans hindex

include h in
/-- Every normal subgroup of the actual radius has the fixed-or-covering
residual alternative, modulo the full starting seed. -/
theorem Input.replacement_critical_radius_residual_dichotomy
    {geometry : Geometry d.radical} {z : Vertex d.radical}
    (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (Y : Subgroup d.overgroup) [Y.Normal] (hY : Y ≤ chiefRadius d) :
    ⁅Y,pResidual 2 d.overgroup⁆ ≤ chiefSeed d ∨
      ⁅chiefRadius d,pResidual 2 d.overgroup⁆ ≤ Y ⊔ chiefSeed d := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  obtain ⟨_,_,hs,hqs,_⟩ := h.replacement_component_image_structure d
  let := hs
  let := hqs
  obtain ⟨q,hq,hker⟩ := h.replacement_inner_component_projection d geometry hb
  have hp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  obtain ⟨A,helem,hA,hidx⟩ := h.replacement_radius_chief_data d path hb hlarge
  let := helem
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hlargeA : Nat.card F^2 ≤ Nat.card (A.map q) := by
    rw [←relIndex_ker,hker]
    exact hA
  have hV : chiefRadius d ≤ q.ker := by
    rw [hker]
    have hh := comap_mono (f := embedM d.radical) (geometry.V_le_Q (by omega) (alpha d.radical) rfl)
    rwa [Q_alpha_comap d.radical (h.replacement_two_group d) (h.replacement_core_le d)] at hh
  exact symplectic_residual_dichotomy_modulo h.field_card h.nonbinary
    (h.replacement_component_image_card_sp d) (h.replacement_component_image_sqtk d)
    q hq hp (chiefRadius d) (chiefSeed d)
    (comap_mono (Z_le_VBall d.radical (alpha d.radical) 2)) hV A hlargeA hidx Y hY

omit [Finite F] [CharP F 2] in
include h in
/-- MS3 excludes a wholly central radius quotient. -/
theorem Input.replacement_radius_quotient_moving_ne_bot
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical) :
    ⁅chiefRadiusQuotient d,pResidual 2 (d.overgroup ⧸ chiefSeed d)⁆ ≠ ⊥ := by
  intro hz
  have hne : Z d.radical (alpha d.radical) ≠ ⊥ := by
    obtain ⟨z,hz⟩ := criticalPair_exists d.radical (alpha d.radical)
      (geometry.exists_critical _ rfl)
    intro hh
    exact hz.2 (hh ▸ bot_le)
  apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.radius_moving_not_le_Z_of_residual_edge_generation
    (h.replacement_characteristic d) (h.replacement_residual_edge_generation d)
    geometry hb rfl (base_adjacent d.radical) hne
  let π := QuotientGroup.mk' (chiefSeed d)
  have hm : (⁅chiefRadius d,pResidual 2 d.overgroup⁆).map π = ⊥ := by
    rw [map_commutator,map_pResidual_quotient]
    exact hz
  have hh := (Subgroup.map_eq_bot_iff _).mp hm
  have hc : ⁅chiefRadius d,pResidual 2 d.overgroup⁆ ≤ chiefSeed d := by
    simpa only [π,QuotientGroup.ker_mk'] using hh
  have hc' := map_mono (f := embedM d.radical) hc
  have hV : (chiefRadius d).map (embedM d.radical) = V d.radical (alpha d.radical) :=
    map_comap_eq_self ((geometry.V_local _ rfl hb).trans_eq (stabilizer_m_base d.radical))
  have hZ : (chiefSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  rwa [map_commutator,hV,←Ltilde_alpha,hZ] at hc'

include h in
/-- Every chief series of the literal radius quotient has exactly one
noncentral factor in the source large-critical-image case. -/
theorem Input.replacement_critical_radius_unique_noncentral_factor
    {geometry : Geometry d.radical} {z : Vertex d.radical}
    (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (s : SeriesOn (chiefRadiusQuotient d)) : s.noncentralCount = 1 := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  obtain ⟨_,_,hs,hqs,_⟩ := h.replacement_component_image_structure d
  let := hs
  let := hqs
  obtain ⟨q,hq,hker⟩ := h.replacement_inner_component_projection d geometry hb
  have hp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  obtain ⟨A,helem,hA,hidx⟩ := h.replacement_radius_chief_data d path hb hlarge
  let := helem
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hlargeA : Nat.card F^2 ≤ Nat.card (A.map q) := by
    rw [←relIndex_ker,hker]
    exact hA
  have hV : chiefRadius d ≤ q.ker := by
    rw [hker]
    have hh := comap_mono (f := embedM d.radical) (geometry.V_le_Q (by omega) (alpha d.radical) rfl)
    rwa [Q_alpha_comap d.radical (h.replacement_two_group d) (h.replacement_core_le d)] at hh
  have hcount : s.noncentralCount ≤ 1 := symplectic_noncentralCount_le_one_modulo h.field_card h.nonbinary
    (h.replacement_component_image_card_sp d) (h.replacement_component_image_sqtk d)
    q hq hp (chiefRadius d) (chiefSeed d)
    (comap_mono (Z_le_VBall d.radical (alpha d.radical) 2)) hV A hlargeA hidx s
  have hpos : s.noncentralCount ≠ 0 := by
    intro hz
    have hh := s.series.residual_commutator_le_head_of_central_steps
      (show IsPGroup 2 s.series.last.val by
        rw [s.last_eq]
        exact (hp.to_le hV).map (QuotientGroup.mk' (chiefSeed d)))
      (s.noncentralCount_eq_zero_iff.mp hz)
    rw [s.last_eq,s.head_eq] at hh
    exact h.replacement_radius_quotient_moving_ne_bot d geometry (by omega) (le_bot_iff.mp hh)
  omega

include h in
/-- The distance-four chief-factor argument supplies radius centrality on
any replacement geometry of distance at least four. -/
theorem Input.replacement_radius_commutator_central
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  have hbase : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    by_contra hnot
    have hfour := SectionFive.distance_eq_four_of_radius_commutator_not_central
      d.radical geometry (by omega) rfl hnot
    obtain ⟨z,path,hlarge⟩ := h.replacement_noncentral_base_large_critical_path d geometry hfour hnot
    have hd := h.replacement_critical_radius_residual_dichotomy d path hb hlarge
      ⁅chiefRadius d,pCore 2 d.overgroup⁆ (commutator_le_left _ _)
    exact hnot (RadiusEdge.radius_commutator_central_of_preimage_dichotomy geometry
      (h.replacement_two_group d) (h.replacement_core_le d)
      (h.replacement_residual_edge_generation d) (by omega) hd)
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hV : V d.radical (mVertex d.radical g) =
      (V d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act d.radical g (alpha d.radical)
  have hQ : Q d.radical (mVertex d.radical g) =
      (Q d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act d.radical g (alpha d.radical)
  rw [hV,hQ,←map_commutator]
  exact (map_mono hbase).trans (map_centralizer_le_centralizer_image _ _)

include h in
/-- The derived radius and the full critical triple commutator in MS93 (5.2). -/
theorem Input.replacement_radius_commutator_bounds
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) (z c : Vertex d.radical) :
    ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical z ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ := by
  have hc := h.replacement_radius_commutator_central d geometry hb ha
  exact ⟨SectionFive.radius_derived_le_X d.radical geometry (by omega) ha hc,
    SectionFive.critical_radius_triple_commutator d.radical hc⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
