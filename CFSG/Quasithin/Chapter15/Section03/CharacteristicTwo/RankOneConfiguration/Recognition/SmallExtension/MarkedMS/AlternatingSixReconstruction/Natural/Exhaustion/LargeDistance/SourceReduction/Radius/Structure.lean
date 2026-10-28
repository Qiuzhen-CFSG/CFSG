module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Geometry

/-!
# The actual radius derived subgroup in the A₆ branch

Each noncommuting pair of radius-two generators is critical and has the
radius center as midpoint. Midpoint fixedness therefore places the entire
derived radius in the fixed core. The moving radius centralizes this
derived subgroup and has class at most two. The residual and an abelian
edge radius generate the radius; consequently an abelian moving radius
would make the whole radius abelian, contradicting critical noncommutation.

These are the group-theoretic reductions in MS93 (3.8), pp.878--879.
The final small-module argument excluding the nonabelian moving radius
remains to be proved. The proofs adapt Exclusion.Radius's group arguments
to the original A₆ replacement, without its SL₃(2) LocalSource.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

private theorem normalizes_sup_of_commutator_le {G : Type*} [Group G]
    (A B K : Subgroup G) (hKA : K ≤ normalizer (A : Set G))
    (hc : ⁅B, K⁆ ≤ A) : K ≤ normalizer (A ⊔ B : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    apply sup_le
    · exact (mem_normalizer_iff_map_conj_eq.mp (hKA hk)).le.trans le_sup_left
    · rintro _ ⟨b, hb, rfl⟩
      have hcb : ⁅k, b⁆ ∈ A := by
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator hk hb)
      have h := (A ⊔ B).mul_mem (mem_sup_left hcb) (mem_sup_right hb)
      simpa [commutatorElement_def, mul_assoc] using h
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)


omit [Finite G] in
private theorem fixedCore_normalized (a : Vertex r.radical) :
    stabilizer r.radical a ≤ normalizer (fixedCore r.radical a : Set (FreeAmalgam r.radical)) := by
  have heq : (fixedCore r.radical a).subgroupOf (stabilizer r.radical a) =
      (Q r.radical a).subgroupOf (stabilizer r.radical a) ⊓
        centralizer (pResidual 2 (stabilizer r.radical a) : Set (stabilizer r.radical a)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro l hl
      apply Subtype.ext
      exact hx.2 l (mem_map_of_mem (stabilizer r.radical a).subtype hl)
    · rintro ⟨hx,hc⟩
      refine ⟨hx, ?_⟩
      rintro _ ⟨l,hl,rfl⟩
      exact congrArg Subtype.val (hc l hl)
  apply (normal_subgroupOf_iff_le_normalizer
    (show fixedCore r.radical a ≤ stabilizer r.radical a from inf_le_left.trans (fun _ hx => hx.1))).mp
  rw [heq]
  let := Q_normal r.radical a
  infer_instance

private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer D) (hc : ∀ i, ⁅A i,Y⁆ ≤ D) :
    ⁅⨆ i, A i,Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)


/-- The moving radius and each incident edge radius generate the whole radius. -/
theorem radius_eq_moving_sup_edge (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    {a t : Vertex r.radical} (ha : color r.radical a = false) (hat : Adjacent r.radical a t) :
    V r.radical a = Vcirc r.radical a ⊔ V r.radical t := by
  have htV := edge_radius_le_radius ha hat
  have hn : stabilizer r.radical a ≤ normalizer (Vcirc r.radical a ⊔ V r.radical t : Subgroup (FreeAmalgam r.radical)) := by
    rw [← local_generation h m hz hn r himage a ha]
    apply sup_le
    · exact normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
        (commutator_mono htV le_rfl)
    · exact (le_inf
        ((show Q r.radical a ≤ stabilizer r.radical a from fun _ hx => hx.1).trans (Vcirc_normalized a))
        ((show Q r.radical a ≤ stabilizer r.radical t from fun _ hx => hx.2 t hat).trans (V_normalized t))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hmov : Vcirc r.radical a ≤ V r.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  apply le_antisymm _ (sup_le hmov htV)
  apply radius_le_of_m_ball ha
  intro d hd hdist
  by_cases hda : d = a
  · subst d
    apply (show Z r.radical a ≤ V r.radical t from ?_).trans le_sup_right
    apply le_iSup_of_le a
    exact le_iSup_of_le
      (show (cosetGraph r.radical).dist a t ≤ 2 from
        (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hat)).le.trans (by decide)) le_rfl
  have htwo : (cosetGraph r.radical).dist a d = 2 := by
    have hne : (cosetGraph r.radical).dist a d ≠ 0 := by
      intro hz
      exact hda ((cosetGraph_connected r.radical).dist_eq_zero_iff.mp hz).symm
    have heven : Even ((cosetGraph r.radical).dist a d) := by
      obtain ⟨w, hw⟩ := (cosetGraph_connected r.radical).exists_walk_length_eq_dist a d
      rw [← hw, walk_even_iff_color_eq, ha, hd]
    rw [Nat.even_iff] at heven
    rw [SimpleGraph.dist_comm] at hdist
    omega
  obtain ⟨u, hau, hdu⟩ := exists_common_neighbor_of_dist_two r.radical a d htwo
  obtain ⟨g, hg, hgu⟩ := stabilizer_transitive_neighbors r.radical a hat hau
  have hVu : V r.radical u ≤ Vcirc r.radical a ⊔ V r.radical t := by
    rw [← hgu, V_act]
    exact (map_mono (show V r.radical t ≤ Vcirc r.radical a ⊔ V r.radical t from le_sup_right)).trans
      (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer r.radical a).inv_mem hg))).le
  apply (show Z r.radical d ≤ V r.radical u from ?_).trans hVu
  apply le_iSup_of_le d
  exact le_iSup_of_le
    (show (cosetGraph r.radical).dist d u ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj r.radical _ _).mpr hdu)).le.trans (by decide)) le_rfl


/-- Every radius-generator commutator is fixed by the actual local residual. -/
theorem radius_derived_le_fixed
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅V r.radical a,V r.radical a⁆ ≤ fixedCore r.radical a := by
  let geometry := replacementGeometry h r
  have hb : 2 < geometry.b r.radical := by
    change 2 < replacementDistance h r
    rw [fg.distance]
    decide
  have hfour : geometry.b r.radical = 4 := fg.distance
  let I := {d : Vertex r.radical // color r.radical d = false ∧ (cosetGraph r.radical).dist d a ≤ 2}
  have heq : V r.radical a = ⨆ d : I, Z r.radical d.val := by
    apply le_antisymm
    · apply radius_le_of_m_ball ha
      intro d hd hdist
      exact le_iSup_of_le (⟨d, hd, hdist⟩ : I) le_rfl
    · apply iSup_le
      intro d
      exact le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  have hnormal : V r.radical a ≤ normalizer (fixedCore r.radical a : Set (FreeAmalgam r.radical)) :=
    ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)).trans (fixedCore_normalized r a)
  rw [heq] at hnormal ⊢
  apply commutator_iSup_le_of_normalizes _ _ _ hnormal
  intro d
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes _ _ _ hnormal
  intro e
  by_cases hZQ : Z r.radical e.val ≤ Q r.radical d.val
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hZQ.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d.val d.property.1))))).le.trans bot_le
  have hmin := criticalDistance_le r.radical e.val (geometry.exists_critical e.val e.property.1) hZQ
  have hecrit : criticalDistance r.radical e.val (geometry.exists_critical e.val e.property.1) = 4 :=
    (geometry.distance_constant e.val e.property.1).trans hfour
  have hdcrit : criticalDistance r.radical d.val (geometry.exists_critical d.val d.property.1) = 4 :=
    (geometry.distance_constant d.val d.property.1).trans hfour
  rw [hecrit] at hmin
  have hda : (cosetGraph r.radical).dist a d.val ≤ 2 := by
    simpa only [SimpleGraph.dist_comm] using d.property.2
  have htri := (cosetGraph_connected r.radical).dist_triangle (u := e.val) (v := a) (w := d.val)
  have hd : (cosetGraph r.radical).dist e.val d.val = 4 := by omega
  have hc : CriticalPair r.radical e.val d.val (geometry.exists_critical e.val e.property.1) :=
    ⟨by rw [hecrit]; exact hd, hZQ⟩
  have hZXe := geometry.omega_bound e.val e.property.1 (by
    rw [hecrit]; decide)
  have hZXd := geometry.omega_bound d.val d.property.1 (by
    rw [hdcrit]; decide)
  exact (commutator_mono hZXe hZXd).trans
    (critical_commutator_le_fixed_midpoint h m hz hn r himage fg e.val e.property.1 d.val hc
      a ha (by omega) (by omega))


include h in
/-- Residual commutator idempotence on the actual two-group radius. -/
theorem moving_full_commutation (hb : 2 < replacementDistance h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅Vcirc r.radical a, Ltilde r.radical a⁆ = Vcirc r.radical a := by
  let S := stabilizer r.radical a
  let W := (V r.radical a).subgroupOf S
  let := finite_stabilizer r.radical a
  let : W.Normal := normal_subgroupOf_of_le_normalizer (V_normalized a)
  have hV : V r.radical a ≤ S := ((replacementGeometry h r).V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hid := commutator_isPPerfect_idempotent (pResidual 2 S) W
    (isPPerfect_pResidual 2) ((Q_isPGroup r.radical (replacement_radical_isPGroup h r)
      (replacement_core_le_radical h r) a ha).to_le
        ((replacementGeometry h r).V_le_Q hb a ha)).comap_subtype
    le_normalizer_of_normal
  have hh := congrArg (Subgroup.map S.subtype) hid
  have hW : W.map S.subtype = V r.radical a := map_subgroupOf_eq_of_le hV
  simpa only [map_commutator, hW, Ltilde, Vcirc] using hh


/-- Fixed derived radius and abelian moving radius force centrality. -/
theorem moving_central_of_commutative (hb : 2 < replacementDistance h r)
    (a : Vertex r.radical) (ha : color r.radical a = false)
    (hfixed : ⁅V r.radical a, V r.radical a⁆ ≤ fixedCore r.radical a)
    (hcomm : IsMulCommutative (Vcirc r.radical a)) :
    Vcirc r.radical a ≤ centralizer (V r.radical a : Set (FreeAmalgam r.radical)) := by
  have hm : Vcirc r.radical a ≤ V r.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hD : ⁅⁅V r.radical a, V r.radical a⁆, Ltilde r.radical a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hfixed.trans inf_le_right)
  have hone : ⁅⁅Ltilde r.radical a, V r.radical a⁆, Vcirc r.radical a⁆ = ⊥ := by
    rw [commutator_comm (Ltilde r.radical a) (V r.radical a)]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr hcomm)
  have htwo : ⁅⁅V r.radical a, Vcirc r.radical a⁆, Ltilde r.radical a⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hm) le_rfl).trans hD.le)
  have hh := commutator_commutator_eq_bot_of_rotate hone htwo
  rw [moving_full_commutation h r hb a ha] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh

/-- The abelian edge and central moving radius make the whole radius abelian. -/
theorem radius_commutative_of_moving_central (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h r) (a t : Vertex r.radical)
    (ha : color r.radical a = false) (hat : Adjacent r.radical a t)
    (hc : Vcirc r.radical a ≤ centralizer (V r.radical a : Set (FreeAmalgam r.radical))) :
    IsMulCommutative (V r.radical a) := by
  have hVt := edge_radius_le_radius ha hat
  have ht := le_centralizer_iff_isMulCommutative.mpr (edge_radius_commutative (replacementGeometry h r) hb a t ha hat)
  apply le_centralizer_iff_isMulCommutative.mp
  rw [radius_eq_moving_sup_edge h m hz hn r himage ha hat]
  apply sup_le
  · rw [← radius_eq_moving_sup_edge h m hz hn r himage ha hat]
    exact hc
  · apply le_centralizer_iff.mpr
    apply sup_le (hc.trans (centralizer_le hVt)) ht


/-- The moving radius centralizes the derived radius, with midpoint
fixedness discharged on every radius generator. -/
theorem moving_centralizes_derived
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅Vcirc r.radical a,⁅V r.radical a,V r.radical a⁆⁆ = ⊥ :=
  NaturalStructure.Exclusion.moving_centralizes_derived a
    (radius_derived_le_fixed h m hz hn r himage fg a ha)

/-- The source reductions force class at most two for the moving radius. -/
theorem moving_class_two
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅⁅Vcirc r.radical a,Vcirc r.radical a⁆,Vcirc r.radical a⁆ = ⊥ := by
  have hm : Vcirc r.radical a ≤ V r.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hzero := moving_centralizes_derived h m hz hn r himage fg a ha
  rw [commutator_comm] at hzero
  exact le_bot_iff.mp ((commutator_mono (commutator_mono hm hm) le_rfl).trans hzero.le)

/-- Critical noncommutation prevents an abelian radius at the midpoint. -/
theorem critical_midpoint_radius_not_commutative
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hac : (cosetGraph r.radical).dist a c = 2)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    ¬ IsMulCommutative (V r.radical c) := by
  intro hcomm
  have hZa : Z r.radical a ≤ V r.radical c := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hZa' : Z r.radical a' ≤ V r.radical c := le_iSup_of_le a' (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hca']) le_rfl)
  apply critical_noncommutation r.radical (replacementGeometry h r)
    (edgeCentralizerCondition h m hz hn r himage) a ha
      (by rw [(replacementGeometry h r).distance_constant a ha]; exact replacementDistance_pos h r) hc
  exact commutator_eq_bot_iff_le_centralizer.mpr (hZa.trans
    ((le_centralizer_iff_isMulCommutative.mpr hcomm).trans (centralizer_le hZa')))

/-- The source-(3.8) group argument reduces the A₆ exclusion to the genuinely
nonabelian moving radius; no whole-core or natural-subgroup identification is used. -/
theorem critical_midpoint_moving_not_commutative
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    ¬ IsMulCommutative (Vcirc r.radical c) := by
  intro hm
  have hb : 2 < replacementDistance h r := by rw [fg.distance]; decide
  have hcentral := moving_central_of_commutative h r hb c hcColor
    (radius_derived_le_fixed h m hz hn r himage fg c hcColor) hm
  obtain ⟨t,hct,_⟩ := exists_common_neighbor_of_dist_two r.radical c a (by
    rw [SimpleGraph.dist_comm,hac])
  exact critical_midpoint_radius_not_commutative h m hz hn r himage a ha a' hc c hac hca'
    (radius_commutative_of_moving_central h m hz hn r himage hb c t hcColor hct hcentral)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
