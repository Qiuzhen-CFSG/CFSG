module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Orientation

/-!
# The single dual higher section from the moving natural quotient

This proves the step (iv) -> (v) on p.899 for the actual path and layers.
Radius four centralizes radius two at critical distance eight. The preceding
centrality bounds all commutators of the third layer with the first one.
The critical window at indices 2 and 10 makes this commutator nontrivial;
commutator idempotence transfers nontriviality to the moving third layer.

The preceding natural section and (4.5.3)(i) bound the relative index by eight.
`Pairing` then constructs the surjective scalar-commutator coordinates with
kernel exactly Z and action dual to the SAME marking of CommonFacts.natural.
No extra pairing, nonzero-commutator, kernel, exponent, or dimension premise
is retained. The doubled natural model of (iv) is still an explicit premise.

The last two exports apply the orientation obstruction and the actual (4.5.5)
assembly. Their natural model is to be constructed in the remaining quotient
branch. The pairwise local estimates of (4.5.5) remain with OrbitGeometry.
The literal preceding equality (4.5.3)(i) belongs to the Early source owner;
the old bundled OrbitFacts normalizer transcription is not used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(v), printed p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

omit [Finite M] in
private theorem radius_commutator_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) : ⁅V R (alpha R), Q R (alpha R)⁆ ≤ Z R (alpha R) := by
  let := PathCentrality.V_elementary_of_four_lt R (a := alpha R) rfl
    (by rw [earlier.distance]; decide)
  have hVQ := PathCentrality.V_le_Q R (a := alpha R) rfl common.large_distance
  have hcommV : ⁅V R (alpha R), Q R (alpha R)⁆ ≤ V R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
        (DistanceEight.V_normalized R (alpha R)))
  rw [← common.X_eq_Z (alpha R) rfl]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  refine ⟨hVQ (hcommV hx), elemPow_eq_one_of_isElementaryAbelian x (hcommV hx), ?_⟩
  obtain ⟨z,hz,rfl⟩ := earlier.centrality (alpha R) rfl hx
  intro q hq
  exact congrArg Subtype.val ((mem_center_iff.mp hz)
    ⟨q, (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ h => h.1) hq⟩)

omit [Finite M] in
/-- The genuine preceding natural section bounds the first hat quotient.
Only the literal equality (4.5.3)(i) is an additional source input. -/
theorem hatV_relIndex_le_eight (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {c : Vertex R}
    (hVa : hatV R (alpha R) c = Vcirc R (alpha R) ⊔ Z R (alpha R)) :
    (Z R (alpha R)).relIndex (hatV R (alpha R) c) ≤ 8 := by
  obtain ⟨s⟩ := earlier.natural_section (alpha R) rfl
  let S := stabilizer R (alpha R)
  let H₀ := (V R (alpha R)).subgroupOf S
  let N₀ := (Z R (alpha R)).subgroupOf S
  let Q₀ := (Q R (alpha R)).subgroupOf S
  let D := Escape.radicalPreimage Q₀ H₀ N₀
  let F := Escape.movingPreimage Q₀ H₀ N₀
  have hZ : N₀.map S.subtype = Z R (alpha R) :=
    map_subgroupOf_eq_of_le (Z_le_stabilizer R (alpha R))
  have hH : H₀.map S.subtype = V R (alpha R) :=
    map_subgroupOf_eq_of_le s.local_group
  have hQ : Q₀.map S.subtype = Q R (alpha R) :=
    map_subgroupOf_eq_of_le (fun _ hx => hx.1)
  have hD : D.map S.subtype = Z R (alpha R) := by
    change (N₀ ⊔ ⁅H₀,Q₀⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hZ, hH, hQ]
    exact sup_eq_left.mpr (radius_commutator_le_Z common earlier)
  have hF : F.map S.subtype = Z R (alpha R) ⊔ ⁅V R (alpha R),S⁆ := by
    change (D ⊔ ⁅H₀,(⊤ : Subgroup S)⁆).map S.subtype = _
    rw [Subgroup.map_sup, map_commutator, hD, hH, ← MonoidHom.range_eq_map, S.range_subtype]
  have hsize : (Z R (alpha R)).relIndex (F.map S.subtype) = 8 := by
    rw [← hD, relIndex_map_map_of_injective _ _ S.subtype_injective]
    exact s.module_section.moving_quotient_card
  have hle : hatV R (alpha R) c ≤ F.map S.subtype := by
    rw [hVa,hF]
    exact sup_le ((commutator_mono le_rfl (Ltilde_le_stabilizer _)).trans le_sup_right)
      le_sup_left
  exact (relIndex_le_of_le_right hle (by rw [hsize]; decide)).trans hsize.le

omit [Finite M] in
private theorem moving_layer_le_Q (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
        Q R (alpha R) := by
  refine sup_le ?_ ?_
  · exact (commutator_mono (p.hatSix_le_Q earlier) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((Ltilde_le_stabilizer _).trans (Q_normalized R (alpha R))))
  · exact (hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4 (by rw [earlier.distance]; decide))

omit [Finite M] in
private theorem first_second_commute (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) :
    ⁅hatV R (alpha R) (p.walk.getVert 6),
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ = ⊥ := by
  have hball : V R (alpha R) ≤ centralizer (VBall R (alpha R) 4 : Set (FreeAmalgam R)) := by
    apply (PathCentrality.V_le_iff R rfl _).mpr
    intro v hv hd
    apply le_centralizer_iff.mpr
    have hshift : VBall R (alpha R) 4 ≤ VBall R v 6 :=
      Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le v (alpha R) 4 6
        (by rw [SimpleGraph.dist_comm]; omega)
    exact (hshift.trans (Escape.Propagation.RadiusFour.VBall_le_Q v hv 6
      (by rw [earlier.distance]; decide))).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes v hv)))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (hatV_le_radius R p.two_step_distances.1.le).trans
    (hball.trans (centralizer_le
      (hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le)))

private theorem Vcirc_idempotent (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ⁅Vcirc R (alpha R),Ltilde R (alpha R)⁆ = Vcirc R (alpha R) := by
  let P := stabilizer R (alpha R)
  let H₀ := (V R (alpha R)).subgroupOf P
  let := finite_stabilizer R (alpha R)
  let : H₀.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R (alpha R))
  let := PathCentrality.V_elementary_of_four_lt R (a := alpha R) rfl
    (by rw [earlier.distance]; decide)
  let : IsElementaryAbelian 2 H₀ := IsElementaryAbelian.subgroupOf
    (geometry.V_local (alpha R) rfl common.large_distance)
  have h := commutator_isPPerfect_idempotent (pResidual 2 P) H₀
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 H₀) le_normalizer_of_normal
  have hm := congrArg (fun K : Subgroup P => K.map P.subtype) h
  have hH : H₀.map P.subtype = V R (alpha R) :=
    map_subgroupOf_eq_of_le (geometry.V_local (alpha R) rfl common.large_distance)
  rw [map_commutator, map_commutator, hH] at hm
  exact hm

omit [Finite M] in
private theorem first_third_noncommute (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    ⁅hatV R (alpha R) (p.walk.getVert 6),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≠ ⊥ := by
  have hcolor : color R (p.walk.getVert 2) = false :=
    (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hp : CriticalPair R (p.walk.getVert 2) (p.walk.getVert 10)
      (geometry.exists_critical _ hcolor) := by
    refine ⟨?_,(p.critical 2 (by decide) (by decide)).2⟩
    rw [geometry.distance_constant _ hcolor]
    change _ = geometry.b R
    rw [earlier.distance]
    exact (p.critical 2 (by decide) (by decide)).1
  have hcrit := common.critical_noncommutation _ hcolor _ hp
  obtain ⟨g,hg,ht⟩ := p.turns 4 (by decide) (by decide) (by decide)
  simp only [p.center_eq] at hg
  have hleft : Z R (p.walk.getVert 2) ≤ hatV R (alpha R) (p.walk.getVert 6) := by
    have hh := le_iSup (fun k : stabilizer R (alpha R) =>
      Z R (act R k (p.walk.getVert 6))) ⟨g,hg⟩
    have ht' : act R g (p.walk.getVert 6) = p.walk.getVert 2 := ht
    rw [ht'] at hh
    exact hh
  have hmid : hatV R (p.walk.getVert 8) (p.walk.getVert 10) ≤
      hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
    intro x hx
    apply le_iSup (fun g : stabilizer R (p.walk.getVert 6) =>
      NormalizerTransfer.rightConjugate (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) g) 1
    exact ⟨x,hx,by simp⟩
  have hright := ((PathCentrality.Z_le_localZSpan R (p.walk.getVert 10) (p.walk.getVert 8)).trans
    hmid).trans (hatW_seed_le_hatSix (alpha R) _ _ _)
  intro hz
  exact hcrit (le_bot_iff.mp ((commutator_mono hleft hright).trans hz.le))

private theorem moving_commutator_nontrivial (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R)) :
    ⁅hatV R (alpha R) (p.walk.getVert 6),
      ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≠ ⊥ := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let S := hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)
  let J := Ltilde R (alpha R)
  have hmov : Vcirc R (alpha R) ≤ A := by
    change Vcirc R (alpha R) ≤ hatV R (alpha R) (p.walk.getVert 6)
    rw [hVa]
    exact le_sup_left
  have hcentral : ⁅S,Vcirc R (alpha R)⁆ ≤ centralizer (J : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    intro x hx j hj
    obtain ⟨z,hz,rfl⟩ := earlier.centrality (alpha R) rfl
      (commutator_mono (DistanceEight.Vcirc_le_V R _) (p.hatSix_le_Q earlier) hx)
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨j,Ltilde_le_stabilizer _ hj⟩)
  intro hzero
  have hASJ : ⁅⁅S,J⁆,Vcirc R (alpha R)⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp ((commutator_mono hmov le_sup_left).trans hzero.le)
  have hmoveS : ⁅⁅Vcirc R (alpha R),J⁆,S⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm J]
      exact hASJ
    · exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  rw [Vcirc_idempotent common earlier] at hmoveS
  have hZS : ⁅Z R (alpha R),S⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono le_rfl (p.hatSix_le_Q earlier)).trans
      (geometry.centralizes (alpha R) rfl).le)
  apply first_third_noncommute common earlier p
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [hVa]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hmoveS)
    (commutator_eq_bot_iff_le_centralizer.mp hZS)

/-- Conditional (4.5.4)(v), constructed from the literal central commutator
and the natural model in (iv). The preceding-source (4.5.3)(i) supplies the
index bound; neither a scalar character nor a dual model is assumed. -/
theorem dual_section_of_moving_section (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (n : MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false) :
    Nonempty (MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) := by
  have hlocal := (hatV_le_radius R p.two_step_distances.1.le).trans
    (geometry.V_local (alpha R) rfl common.large_distance)
  have hle : Z R (alpha R) ≤ hatV R (alpha R) (p.walk.getVert 6) := by
    rw [hVa]
    exact le_sup_right
  have hA : Mbar R ≤ normalizer (hatV R (alpha R) (p.walk.getVert 6)) := by
    simpa only [alpha, stabilizer_m_base] using hatV_normalized R (alpha R) (p.walk.getVert 6)
  have hN : Mbar R ≤ normalizer (Z R (alpha R)) := by
    simpa only [alpha, stabilizer_m_base] using Z_normalized R (alpha R)
  have hE := PathCentrality.localZSpan_elementary R (a := p.walk.getVert 6)
    (c := alpha R) rfl p.two_step_distances.1.le (by rw [earlier.distance]; decide)
  apply dualSection_of_commutator_bounds hlocal hle hA hN hE n ?_ (first_second_commute earlier p) ?_
    (moving_commutator_nontrivial common earlier p hVa)
    (hatV_relIndex_le_eight common earlier hVa)
  · intro x hx m hm
    obtain ⟨z,hz,rfl⟩ := earlier.centrality (alpha R) rfl
      (commutator_mono (hatV_le_radius R p.two_step_distances.1.le)
        (moving_layer_le_Q earlier p) hx)
    exact congrArg Subtype.val ((mem_center_iff.mp hz)
      ⟨m, by rw [alpha, stabilizer_m_base]; exact hm⟩)
  · apply le_bot_iff.mp
    exact (commutator_mono le_rfl (moving_layer_le_Q earlier p)).trans
      (geometry.centralizes (alpha R) rfl).le

/-- The supplied genuine natural model excludes the conflicting printed
dual reading of (iv), while the central commutator constructs (v). -/
theorem dual_section_and_orientation (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (n : MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false) :
    Nonempty (MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) ∧
    ¬ Nonempty (MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) true) :=
  ⟨dual_section_of_moving_section common earlier p hVa n,
    moving_quotient_not_dual n⟩

/-- The constructed (v) witness feeds the actual (4.5.5) saturation theorem.
The local estimates remain with the independent OrbitGeometry owner. -/
theorem commutator_layers_of_moving_section (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (n : MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
          Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false)
    (hpairs : ∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        NormalizerTransfer.rightConjugate
          (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
            hatV R (alpha R) (p.walk.getVert 6))
    (hQcomm : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6))
    (hnon : ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤ Z R (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) := by
  obtain ⟨sectionModel⟩ := dual_section_of_moving_section common earlier p hVa n
  exact commutator_layers_of_local_bounds source common earlier p.two_step_distances.1.le
    p.two_step_distances.2.1.le p.two_step_distances.2.2.le sectionModel hpairs hQcomm hnon

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients
