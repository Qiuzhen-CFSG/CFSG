module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PointControl
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality

/-!
# The radius centrality deduction for the unsplit cover

The incident edge radius normally generates the full radius. The residual
and radical generate the literal replacement, and the edge radius is abelian.
A residual fixed-or-covering dichotomy therefore forces its kernel
commutator to centralize the radius. This is the group-theoretic deduction
in MS93 (5.2)(ii), pp.914--915, with no natural subgroup assumption.

The full-cover chief-budget application in RadiusCentrality supplies the
remaining dichotomy. These proofs follow SymplecticSetup.EdgeCentrality,
retaining the original replacement maps and the entire moving cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {r : Replacement L R}

include h in
private theorem replacement_sup_eq_top : replacementComponent r ⊔ r.radical = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k,hk,t,ht,rfl⟩ := replacement_product h r g
  exact mul_mem (mem_sup_left hk) (mem_sup_right ht)

omit [Finite G] in
private theorem adjacent_seed_le_radius {a t : Vertex r.radical}
    (hat : Adjacent r.radical a t) : Z r.radical a ≤ V r.radical t := by
  apply le_iSup_of_le a
  exact le_iSup_of_le
    (show (cosetGraph r.radical).dist a t ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hat)).le.trans (by decide)) le_rfl

omit [Finite G] in
private theorem comap_normal_of_base_normalized (N : Subgroup (FreeAmalgam r.radical))
    (hN : stabilizer r.radical (alpha r.radical) ≤ normalizer (N : Set (FreeAmalgam r.radical))) :
    (N.comap (embedM r.radical)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  change embedM r.radical (g * x * g⁻¹) ∈ N
  rw [map_mul, map_mul, map_inv]
  have hg : embedM r.radical g ∈ stabilizer r.radical (alpha r.radical) := by
    rw [show alpha r.radical = mVertex r.radical 1 from rfl, stabilizer_m_base]
    exact ⟨g, rfl⟩
  exact le_normalizer_iff.mp hN _ hg _ hx

omit [Finite G] in
private theorem map_comap_of_le_base (N : Subgroup (FreeAmalgam r.radical))
    (hN : N ≤ stabilizer r.radical (alpha r.radical)) : (N.comap (embedM r.radical)).map (embedM r.radical) = N := by
  rw [map_comap_eq]
  apply inf_eq_right.mpr
  change N ≤ stabilizer r.radical (mVertex r.radical 1) at hN
  rwa [stabilizer_m_base] at hN

omit [Finite G] in
private theorem base_normalizes_image (N : Subgroup r.overgroup) [N.Normal] :
    stabilizer r.radical (alpha r.radical) ≤ normalizer (N.map (embedM r.radical) : Set (FreeAmalgam r.radical)) := by
  rw [show alpha r.radical = mVertex r.radical 1 from rfl, stabilizer_m_base]
  change (embedM r.radical).range ≤ _
  rw [MonoidHom.range_eq_map]
  simpa only [normalizer_eq_top] using N.le_normalizer_map (embedM r.radical)


omit [Finite G] in
/-- The original local group normalizes its radius preimage. -/
theorem radius_comap_normal : ((V r.radical (alpha r.radical)).comap (embedM r.radical)).Normal :=
  comap_normal_of_base_normalized _ (V_normalized _)

theorem radius_comap_map (hb : 2 < (replacementGeometry h r).b r.radical) :
    ((V r.radical (alpha r.radical)).comap (embedM r.radical)).map (embedM r.radical) = V r.radical (alpha r.radical) :=
  map_comap_of_le_base _ ((replacementGeometry h r).V_local _ rfl hb)

theorem edge_radius_comap_map (hb : 2 < (replacementGeometry h r).b r.radical) :
    ((V r.radical (beta r.radical)).comap (embedM r.radical)).map (embedM r.radical) = V r.radical (beta r.radical) :=
  map_comap_of_le_base _ ((edge_radius_le_radius rfl (base_adjacent r.radical)).trans
    ((replacementGeometry h r).V_local _ rfl hb))

/-- Normal generation in the literal original replacement group, through embedM. -/
theorem radius_comap_eq_normalClosure_edge (hb : 2 < (replacementGeometry h r).b r.radical) :
    (V r.radical (alpha r.radical)).comap (embedM r.radical) =
      normalClosure ((V r.radical (beta r.radical)).comap (embedM r.radical) : Set r.overgroup) := by
  let V₀ := (V r.radical (alpha r.radical)).comap (embedM r.radical)
  let E := (V r.radical (beta r.radical)).comap (embedM r.radical)
  let := radius_comap_normal (r := r)
  apply le_antisymm
  · have hV : V r.radical (alpha r.radical) ≤ (normalClosure (E : Set r.overgroup)).map (embedM r.radical) := by
      apply CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.radius_le_of_normalized_edge rfl (base_adjacent r.radical)
      · change V r.radical (beta r.radical) ≤ _
        rw [←edge_radius_comap_map (h := h) (r := r) hb]
        exact map_mono le_normalClosure
      · exact base_normalizes_image _
    have h := comap_mono (f := embedM r.radical) hV
    rwa [comap_map_eq_self_of_injective (embedM_injective r.radical)] at h
  · apply normalClosure_le_normal
    exact comap_mono (f := embedM r.radical) (edge_radius_le_radius rfl (base_adjacent r.radical))

/-- The original radical normalizes the edge radius in the replacement. -/
theorem radical_normalizes_edge_radius_comap :
    r.radical ≤ normalizer ((V r.radical (beta r.radical)).comap (embedM r.radical) : Set r.overgroup) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  change embedM r.radical (g*x*g⁻¹) ∈ V r.radical (beta r.radical)
  rw [map_mul,map_mul,map_inv]
  have hr' : embedM r.radical g ∈ stabilizer r.radical (beta r.radical) := by
    have hq : embedM r.radical g ∈ Q r.radical (beta r.radical) := by
      rw [Q_beta]
      exact mem_map_of_mem _ hg
    exact hq.1
  exact le_normalizer_iff.mp (V_normalized (beta r.radical)) _ hr' _ hx

/-- The actual component–radical product supplies the edge-plus-moving cover. -/
theorem radius_comap_le_edge_sup_commutator (hb : 2 < (replacementGeometry h r).b r.radical) :
    (V r.radical (alpha r.radical)).comap (embedM r.radical) ≤
      (V r.radical (beta r.radical)).comap (embedM r.radical) ⊔ ⁅(V r.radical (alpha r.radical)).comap (embedM r.radical), (replacementComponent r)⁆ := by
  let := replacementComponent_normal h r
  let V₀ := (V r.radical (alpha r.radical)).comap (embedM r.radical)
  let E := (V r.radical (beta r.radical)).comap (embedM r.radical)
  let := radius_comap_normal (r := r)
  have hEV : E ≤ V₀ := comap_mono (f := embedM r.radical)
    (edge_radius_le_radius rfl (base_adjacent r.radical))
  let D := E ⊔ ⁅V₀,(replacementComponent r)⁆
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←(replacement_sup_eq_top (h := h) (r := r))]
    apply sup_le
    · exact le_normalizer_sup_of_commutator_le V₀ (replacementComponent r) E ⁅V₀,(replacementComponent r)⁆ hEV le_rfl
    · exact (le_inf (radical_normalizes_edge_radius_comap (r := r)) le_normalizer_of_normal).trans
        (normalizer_inf_normalizer_le_normalizer_sup E ⁅V₀,(replacementComponent r)⁆)
  calc
    V₀ = normalClosure (E : Set r.overgroup) := radius_comap_eq_normalClosure_edge (h := h) (r := r) hb
    _ ≤ D := normalClosure_le_normal (show E ≤ D from le_sup_left)


/-- The source residual dichotomy forces centrality of the actual radius
commutator. All normality and edge-generation hypotheses are proved from the replacement. -/
theorem radius_commutator_central_of_residual_dichotomy (hb : 2 < (replacementGeometry h r).b r.radical)
    (hd : ⁅⁅V r.radical (alpha r.radical), Q r.radical (alpha r.radical)⁆, Ltilde r.radical (alpha r.radical)⁆ ≤ Z r.radical (alpha r.radical) ∨
      ⁅V r.radical (alpha r.radical), Ltilde r.radical (alpha r.radical)⁆ ≤ ⁅V r.radical (alpha r.radical), Q r.radical (alpha r.radical)⁆ ⊔ Z r.radical (alpha r.radical)) :
    ⁅V r.radical (alpha r.radical), Q r.radical (alpha r.radical)⁆ ≤ centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  let := replacementComponent_normal h r
  let f := embedM r.radical
  let V₀ := (V r.radical (alpha r.radical)).comap f
  let E := (V r.radical (beta r.radical)).comap f
  let Z₀ := (Z r.radical (alpha r.radical)).comap f
  let P := pCore 2 r.overgroup
  let := radius_comap_normal (r := r)
  let := SymplecticSeed.Z_comap_normal r.radical
  have hVm : V₀.map f = V r.radical (alpha r.radical) := radius_comap_map (h := h) (r := r) hb
  have hEm : E.map f = V r.radical (beta r.radical) := edge_radius_comap_map (h := h) (r := r) hb
  have hZm : Z₀.map f = Z r.radical (alpha r.radical) := map_comap_of_le_base _
    ((Z_le_VBall r.radical (alpha r.radical) 2).trans ((replacementGeometry h r).V_local _ rfl hb))
  have hPm : P.map f = Q r.radical (alpha r.radical) := (Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)).symm
  have hLm : (replacementComponent r).map f = Ltilde r.radical (alpha r.radical) := by rw [Ltilde_alpha,(replacement_residual h r)]
  have hVP : V₀ ≤ P := by
    have hbound := comap_mono (f := f) ((replacementGeometry h r).V_le_Q hb (alpha r.radical) rfl)
    rwa [Q_alpha_comap r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)] at hbound
  have hEV : E ≤ V₀ := comap_mono (f := f)
    (edge_radius_le_radius rfl (base_adjacent r.radical))
  have hZE : Z₀ ≤ E := comap_mono (f := f) (adjacent_seed_le_radius (base_adjacent r.radical))
  have hE : E ≤ centralizer (E : Set r.overgroup) := by
    have hc := le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative (replacementGeometry h r) hb (alpha r.radical) (beta r.radical) rfl (base_adjacent r.radical))
    intro x hx y hy
    apply embedM_injective r.radical
    simpa only [map_mul] using hc hx (f y) hy
  have hcentral : ⁅V₀,P⁆ ≤ centralizer (V₀ : Set r.overgroup) := by
    rcases hd with hd | hd
    · have hfixed : ⁅⁅V₀,P⁆,(replacementComponent r)⁆ ≤ Z₀ := by
        apply (map_le_map_iff_of_injective (embedM_injective r.radical)).mp
        rwa [map_commutator,map_commutator,hVm,hPm,hLm,hZm]
      exact edge_commutator_central_of_residual_fixed V₀ P E Z₀ (replacementComponent r) r.radical
        (radius_comap_eq_normalClosure_edge (h := h) (r := r) hb) hEV hZE
        (radical_normalizes_edge_radius_comap (r := r)) (replacement_core_le_radical h r) (replacement_sup_eq_top (h := h) (r := r)) hE hfixed
    · have hcover : ⁅V₀,(replacementComponent r)⁆ ≤ E ⊔ ⁅V₀,P⁆ := by
        have hc : ⁅V₀,(replacementComponent r)⁆ ≤ ⁅V₀,P⁆ ⊔ Z₀ := by
          apply (map_le_map_iff_of_injective (embedM_injective r.radical)).mp
          rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hPm,hLm,hZm]
        exact hc.trans (sup_le le_sup_right (hZE.trans le_sup_left))
      exact edge_commutator_central_of_residual_cover V₀ P E (replacementComponent r) hVP (hEV.trans hVP)
        (pCore_isPGroup (p := 2) (G := r.overgroup)).isNilpotent
        ((replacement_core_le_radical h r).trans (radical_normalizes_edge_radius_comap (r := r))) hE
        (radius_comap_le_edge_sup_commutator (h := h) (r := r) hb) hcover
  rw [←hVm,←hPm,←map_commutator]
  exact (map_mono hcentral).trans (map_centralizer_le_centralizer_image (V₀ : Set r.overgroup) f)


/-- Direct input from the chief-budget theorem in the replacement: the only preimages are
through the specified embedM, and both the residual and kernel are literal. -/
theorem radius_commutator_central_of_preimage_dichotomy (hb : 2 < (replacementGeometry h r).b r.radical)
    (hd : ⁅⁅(V r.radical (alpha r.radical)).comap (embedM r.radical), pCore 2 r.overgroup⁆, pResidual 2 r.overgroup⁆ ≤
        (Z r.radical (alpha r.radical)).comap (embedM r.radical) ∨
      ⁅(V r.radical (alpha r.radical)).comap (embedM r.radical), pResidual 2 r.overgroup⁆ ≤
        ⁅(V r.radical (alpha r.radical)).comap (embedM r.radical), pCore 2 r.overgroup⁆ ⊔
          (Z r.radical (alpha r.radical)).comap (embedM r.radical)) :
    ⁅V r.radical (alpha r.radical), Q r.radical (alpha r.radical)⁆ ≤ centralizer (V r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  apply radius_commutator_central_of_residual_dichotomy (h := h) (r := r) hb
  have hZ := map_comap_of_le_base (Z r.radical (alpha r.radical))
    ((Z_le_VBall r.radical (alpha r.radical) 2).trans ((replacementGeometry h r).V_local _ rfl hb))
  rcases hd with hd | hd
  · left
    have hm := map_mono (f := embedM r.radical) hd
    rwa [map_commutator,map_commutator,radius_comap_map (h := h) (r := r) hb,
      ←Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r),←Ltilde_alpha,hZ] at hm
  · right
    have hm := map_mono (f := embedM r.radical) hd
    rwa [map_commutator,Subgroup.map_sup,map_commutator,radius_comap_map (h := h) (r := r) hb,
      ←Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r),←Ltilde_alpha,hZ] at hm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
