module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CriticalActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusStructure

/-!
# Centrality of the radius for both symmetric central covers

Noncentrality at distance four selects a large critical image. The natural
quotient supplies an even involution in the reverse image, while the point
core bounds the radius index by eight. The chief-factor budget gives the
residual dichotomy and the abelian-edge argument forces centrality.

Larger distances have abelian radius. Conjugation then proves the radius
centrality, derived-layer containment and critical triple-commutator identity
at every component vertex. The original central cover is retained throughout.
This is the point-core branch of MS93 (5.2)(ii)--(iii), pp.914--915; point-core
containment still belongs to the final large-distance source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {r : Replacement L R} (s : FullSymmetricAction h e hz hn r)

omit [Finite G] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam r.radical))
    (hJ : stabilizer r.radical (alpha r.radical) ≤ normalizer (J : Set (FreeAmalgam r.radical))) :
    (J.comap (embedM r.radical)).Normal := by
  constructor
  intro n hn g
  change embedM r.radical (g*n*g⁻¹) ∈ J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM r.radical g)
    (by change embedM r.radical g ∈ stabilizer r.radical (mVertex r.radical 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

/-- The S6 chief-factor dichotomy on the literal radius, transported through
its source embedding. -/
theorem radius_residual_dichotomy_of_index
    (hb : 2 < (replacementGeometry h r).b r.radical) (hq : Function.Surjective s.projection)
    (A K : Subgroup (FreeAmalgam r.radical))
    (hA : A ≤ stabilizer r.radical (alpha r.radical))
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ (A.comap (embedM r.radical)).map s.projection)
    (hc : ⁅V r.radical (alpha r.radical) ⊓ K,A⁆ ≤ Z r.radical (alpha r.radical))
    (hindex : K.relIndex (V r.radical (alpha r.radical)) ≤ 8) :
    ⁅⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆,Ltilde r.radical (alpha r.radical)⁆ ≤ Z r.radical (alpha r.radical) ∨
      ⁅V r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆ ≤
        ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ⊔ Z r.radical (alpha r.radical) := by
  let f := embedM r.radical
  let V₀ := (V r.radical (alpha r.radical)).comap f
  let Z₀ := (Z r.radical (alpha r.radical)).comap f
  let A₀ := A.comap f
  let K₀ := K.comap f
  let : V₀.Normal := normalized_comap_normal _ (V_normalized (alpha r.radical))
  let : Z₀.Normal := normalized_comap_normal _ (Z_normalized r.radical (alpha r.radical))
  have hVQ : V r.radical (alpha r.radical) ≤ Q r.radical (alpha r.radical) := V_le_Q r.radical rfl hb
  have hVrange : V r.radical (alpha r.radical) ≤ f.range :=
    (hVQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base r.radical)
  have hZV : Z r.radical (alpha r.radical) ≤ V r.radical (alpha r.radical) := by
    apply le_iSup_of_le (alpha r.radical)
    exact le_iSup_of_le (by simp) le_rfl
  have hVm : V₀.map f = V r.radical (alpha r.radical) := by
    rw [map_comap_eq,inf_eq_right.mpr hVrange]
  have hZm : Z₀.map f = Z r.radical (alpha r.radical) := by
    rw [map_comap_eq,inf_eq_right.mpr (hZV.trans hVrange)]
  have hAm : A₀.map f = A := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (hA.trans_eq (stabilizer_m_base r.radical))
  have hVker : V₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective r.radical)).mp
    rw [hVm,←Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)]
    exact hVQ
  have hp : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hc₀ : ⁅V₀ ⊓ K₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective r.radical)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective r.radical),hVm,hAm,hZm]
    exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans hc
  have hi₀ : K₀.relIndex V₀ ≤ 8 := by
    rw [relIndex_comap,hVm]
    exact hindex
  have hh := NoncentralChiefRefinement.SymmetricSixBudget.kernel_commutator_residual_dichotomy_of_index
    s.projection hq hp V₀ Z₀ (comap_mono hZV) hVker A₀ a ha heven haA K₀ hc₀ hi₀
  have hQm : s.projection.ker.map f = Q r.radical (alpha r.radical) := by
    rw [s.projection_kernel,Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)]
  have hLm : (pResidual 2 r.overgroup).map f = Ltilde r.radical (alpha r.radical) := (Ltilde_alpha r.radical).symm
  rcases hh with hh | hh
  · left
    have hh := map_mono (f := f) hh
    rwa [map_commutator,map_commutator,hVm,hQm,hLm,hZm] at hh
  · right
    have hh := map_mono (f := f) hh
    rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hLm,hQm,hZm] at hh

/-- On the actual critical path, the source radius estimate discharges the
index-eight premise of the chief-factor argument. -/
theorem critical_radius_residual_dichotomy
    (t : Theory.SpecificGroups.SymmetricSix.BinaryFlags.S)
    (hR : r.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : (replacementGeometry h r).b r.radical = 4) {e : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) (alpha r.radical) e)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ ((Z r.radical e).comap (embedM r.radical)).map s.projection)
    (hc : ⁅V r.radical (alpha r.radical) ⊓ Q r.radical (p.walk.getVert (p.walk.length-2)),Z r.radical e⁆ ≤ Z r.radical (alpha r.radical)) :
    ⁅⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆,Ltilde r.radical (alpha r.radical)⁆ ≤ Z r.radical (alpha r.radical) ∨
      ⁅V r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆ ≤
        ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ⊔ Z r.radical (alpha r.radical) := by
  apply radius_residual_dichotomy_of_index s (by omega)
    s.surjective
    (Z r.radical e) (Q r.radical (p.walk.getVert (p.walk.length-2)))
    (critical_Z_le_stabilizer r.radical (replacementGeometry h r) (alpha r.radical) rfl (replacementDistance_pos h r) p.critical)
    a ha heven haA hc
  exact critical_radius_image_index_le_eight s t hR hb p

/-- The marked critical-path inputs now imply actual radius centrality. -/
theorem critical_radius_central_of_marked_actor
    (t : Theory.SpecificGroups.SymmetricSix.BinaryFlags.S)
    (hR : r.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : (replacementGeometry h r).b r.radical = 4) {e : Vertex r.radical}
    (p : CriticalPath r.radical (replacementGeometry h r) (alpha r.radical) e)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ ((Z r.radical e).comap (embedM r.radical)).map s.projection)
    (hc : ⁅V r.radical (alpha r.radical) ⊓ Q r.radical (p.walk.getVert (p.walk.length-2)),Z r.radical e⁆ ≤ Z r.radical (alpha r.radical)) :
    ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤ centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) :=
  radius_commutator_central_of_residual_dichotomy (h := h) (r := r) (by omega)
    (critical_radius_residual_dichotomy s t hR hb p a ha heven haA hc)


/-- The genuine source (5.2)(ii) centrality assertion at critical distance four. -/
theorem radius_commutator_central_of_b_eq_four (hc : DistanceTwo.CentralLayer r)
    (u : S) (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : (replacementGeometry h r).b r.radical = 4) :
    ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤ centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  by_contra hn
  obtain ⟨e,p,hforward⟩ := exists_base_large_critical_path (h := h) (r := r) hb hn
  obtain ⟨a,haA,ha,heven⟩ :=
    exists_even_involution_reverse_critical_image s hc (by omega) p hforward
  exact hn (critical_radius_central_of_marked_actor s u hR hb p a ha heven haA
    (critical_radius_commutator_le_Z s hc u hR
      (by change 2 < (replacementGeometry h r).b r.radical; omega) p hforward))

/-- Both the distance-four and greater-distance branches of source (5.2)(ii). -/
theorem radius_commutator_central_of_two_lt (hc : DistanceTwo.CentralLayer r)
    (u : S) (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < (replacementGeometry h r).b r.radical) :
    ⁅V r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤ centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  by_cases hlarge : 4 < (replacementGeometry h r).b r.radical
  · exact CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_commutator_central_of_four_lt r.radical (replacementGeometry h r) hlarge rfl
  · have heven : Even ((replacementGeometry h r).b r.radical) := (replacementGeometry h r).even (alpha r.radical) rfl
    rw [Nat.even_iff] at heven
    exact radius_commutator_central_of_b_eq_four s hc u hR (by omega)

/-- The same centrality at every original-group vertex, through literal graph conjugation. -/
theorem radius_commutator_central_at (hc : DistanceTwo.CentralLayer r)
    (u : S) (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < (replacementGeometry h r).b r.radical) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅V r.radical a,Q r.radical a⁆ ≤ centralizer (V r.radical a : Set (FreeAmalgam r.radical)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color r.radical ha
  have hV : V r.radical (mVertex r.radical g) = (V r.radical (alpha r.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act r.radical g (alpha r.radical)
  have hQ : Q r.radical (mVertex r.radical g) = (Q r.radical (alpha r.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act r.radical g (alpha r.radical)
  rw [hV,hQ,←map_commutator]
  exact (map_mono (radius_commutator_central_of_two_lt s hc u hR hb)).trans
    (map_centralizer_le_centralizer_image (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical))
      (MulAut.conj g⁻¹).toMonoidHom)

/-- All three source (5.2)(ii)--(iii) radius conclusions, with no additional
centrality, quotient, actor or chief-factor premise. -/
theorem radius_bounds_of_two_lt (hc : DistanceTwo.CentralLayer r)
    (u : S) (hR : r.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < (replacementGeometry h r).b r.radical) {a : Vertex r.radical} (ha : color r.radical a = false)
    (a' c : Vertex r.radical) :
    ⁅V r.radical a,Q r.radical a⁆ ≤ centralizer (V r.radical a : Set (FreeAmalgam r.radical)) ∧
    ⁅V r.radical a,V r.radical a⁆ ≤ X r.radical a ∧
    ⁅⁅X r.radical a' ⊓ Q r.radical a,V r.radical a ⊓ Q r.radical c⁆,V r.radical a ⊓ Q r.radical c⁆ = ⊥ := by
  have hc := radius_commutator_central_at s hc u hR hb a ha
  exact ⟨hc,⟨CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_derived_le_X r.radical (replacementGeometry h r) hb ha hc, CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.critical_radius_triple_commutator r.radical hc⟩⟩
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
