module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.CommutatorHom
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Carriers

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.LocalCentralizer

/-!
# Nontrivial residual action on the actual moving orbit quotient

The critical window at indices 2 and 10 gives [hat V_a,X] ≠ 1, whereas
hat W_a centralizes hat V_a. The earlier (4.4) centrality puts [X,Vcirc_a]
in Z(G_a). If [X,Ltilde_a] lay in hat W_a, the three-subgroup commutator
identity and [Vcirc_a,Ltilde_a]=Vcirc_a would force X to centralize
Vcirc_a. Literal (4.5.3)(i) and centrality of Z_a in Q_a would then make
X centralize hat V_a, a contradiction.

This rules out trivial residual action without any assertion ker Φ ≤ hat W.
Simplicity of the original marked SL3 quotient then puts the actual
commutator preimage C_Ga(X/hat W) inside Q_a. The reverse containment is
not proved: the action has not yet been descended through source.projection.
Its natural orientation and the second source-selected factor also remain
necessary for (4.5.4)(iv).

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), (4.5.3)(i), and the
faithfulness step in (4.5.4)(iv), printed pp.895--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The actual critical window (2,10) forces noncommutation of hat V with X. -/
theorem orbitMovingGroup_noncommutation (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    ⁅hatV R (alpha R) (p.walk.getVert 6), orbitMovingGroup p⁆ ≠ ⊥ := by
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
  have hright : Z R (p.walk.getVert 10) ≤ orbitMovingGroup p := by
    intro x hx
    apply (show NormalizerTransfer.conjugatesIn
      (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) (stabilizer R (alpha R)) ≤
        orbitMovingGroup p from le_sup_left)
    apply le_iSup (fun k : stabilizer R (alpha R) =>
      NormalizerTransfer.rightConjugate (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) k) 1
    exact ⟨x,PathCentrality.Z_le_localZSpan R (p.walk.getVert 10) (p.walk.getVert 8) hx,by simp⟩
  intro hzero
  exact hcrit (le_bot_iff.mp ((commutator_mono hleft hright).trans hzero.le))

/-- The critical window makes X strictly larger than the second layer. -/
theorem orbitMovingGroup_not_le_second (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    ¬ orbitMovingGroup p ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  intro hle
  apply orbitMovingGroup_noncommutation common earlier p
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((SecondLayer.Recognition.denominator_centralizes_second earlier p).trans (centralizer_le hle))

private theorem Vcirc_residual [Finite M] (common : CommonFacts R source geometry)
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

/-- A source substitute for the disputed pairing argument: the residual
acts nontrivially on the actual X / hat W. Only literal (4.5.3)(i) is extra. -/
theorem orbitMovingGroup_residual_not_le_second [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R)) :
    ¬ ⁅orbitMovingGroup p,Ltilde R (alpha R)⁆ ≤
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  let X := orbitMovingGroup p
  let J := Ltilde R (alpha R)
  have hcentral : ⁅X,Vcirc R (alpha R)⁆ ≤ centralizer (J : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    intro x hx j hj
    obtain ⟨z,hz,rfl⟩ := earlier.centrality (alpha R) rfl
      (commutator_mono (DistanceEight.Vcirc_le_V R _) (orbitMovingGroup_le_Q earlier p) hx)
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨j,Ltilde_le_stabilizer _ hj⟩)
  intro hfixed
  have hVXJ : ⁅⁅X,J⁆,Vcirc R (alpha R)⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hVle : Vcirc R (alpha R) ≤ hatV R (alpha R) (p.walk.getVert 6) := by
      rw [hVa]
      exact le_sup_left
    exact hVle.trans ((SecondLayer.Recognition.denominator_centralizes_second earlier p).trans
      (centralizer_le hfixed))
  have hmoveX : ⁅⁅Vcirc R (alpha R),J⁆,X⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm J]
      exact hVXJ
    · exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  rw [Vcirc_residual common earlier] at hmoveX
  have hZX : ⁅Z R (alpha R),X⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono le_rfl (orbitMovingGroup_le_Q earlier p)).trans
      (geometry.centralizes (alpha R) rfl).le)
  apply orbitMovingGroup_noncommutation common earlier p
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [hVa]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hmoveX)
    (commutator_eq_bot_iff_le_centralizer.mp hZX)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The ambient subgroup centralizing X modulo hat W, defined by its literal commutator preimage. -/
@[expose] noncomputable def orbitActionKernel (p : Higher.SourcePath (alpha R)) : Subgroup (FreeAmalgam R) :=
  commutatorPreimage (Mbar R) (orbitMovingGroup p)
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))

/-- Nontrivial residual action and simplicity put the whole action kernel inside Q_a.
The reverse containment, needed for descent through source.projection, is not assumed. -/
theorem orbitActionKernel_le_Q (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R)) :
    orbitActionKernel p ≤ Q R (alpha R) := by
  let C := orbitActionKernel p
  let A := C.comap (embedM R)
  have hW : Mbar R ≤ normalizer (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) := by
    simpa only [alpha,stabilizer_m_base] using hatW_normalized R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hCP : C ≤ Mbar R := commutatorPreimage_le _ _ _
  have hPC : Mbar R ≤ normalizer C := commutatorPreimage_normalized _ _ _ _ hW
    (Mbar R).le_normalizer (orbitMovingGroup_normalized p) hW
  let : A.Normal := by
    constructor
    intro a ha m
    change embedM R (m * a * m⁻¹) ∈ C
    simpa only [map_mul,map_inv] using le_normalizer_iff.mp hPC
      (embedM R m) ⟨m,rfl⟩ (embedM R a) ha
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : (A.map source.projection).Normal :=
    (inferInstance : A.Normal).map _ source.projection_surjective
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · have hA : A ≤ pCore 2 M := by
      rw [← source.projection_kernel]
      exact (Subgroup.map_eq_bot_iff _).mp hbot
    intro x hx
    obtain ⟨m,rfl⟩ := hCP hx
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ (hA hx)
  · have hLA := source.residual_le_of_image_top A htop
    have hLC : Ltilde R (alpha R) ≤ C := by
      rw [Ltilde_alpha,source.residual]
      rintro x ⟨l,hl,rfl⟩
      exact hLA hl
    apply False.elim
    apply orbitMovingGroup_residual_not_le_second common earlier p hVa
    rw [commutator_comm]
    exact (commutator_mono hLC le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hW)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
