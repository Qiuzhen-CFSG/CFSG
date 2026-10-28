module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# Equal image-eight movers at distance four

Equal actual edge movers control the full neighboring seeds and their central
omega. Paired trapping bounds the joined seed's derived subgroup by the starting
seed. The elementary action-image kernel estimate therefore bounds the full
reverse-kernel commutator without requiring the whole radius to be abelian.
The paired generating edge then supplies an overlapping backward critical path,
with the same seed transporter and both central covering possibilities retained.

Source: Meierfrankenfeld--Stellmacher (1993), (5.6)--(5.8), printed pp.918--920,
and the initial selection for (5.12), printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
open EightEdgeComparison

include e hz hn in
/-- The full relative-normalizer mover acts abelianly on the whole seed,
including its central attachment, and preserves every full seed fixer. -/
private theorem normalizer_mover_preserves_seed_fixer_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) N 4
    ⁅J,J⁆ ≤ Q d.radical a ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ J →
        J ≤ normalizer ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let N₀ := normalizer (d.radical : Set d.overgroup)
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N₀ 4
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) N 4
  obtain ⟨u,_,_,hJ,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb
  have him : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show J₀ = _ from hJ]
    exact himage
  have hbase : ⁅J₀,J₀⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator,him]
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    let helem : IsElementaryAbelian 2 ((D 6).map (MulAut.conj u).toMonoidHom) :=
      IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hiN : N₀.map i = N := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N₀ := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hi]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hiJ : J₀.map i = J := by
    rw [SmallMover.join_map i hi,hiU,hiQ,hiN]
  have hderived : ⁅J,J⁆ ≤ Q d.radical a := by
    have hh := map_mono (f := i) hbase
    rwa [map_commutator,hiJ,hiQ] at hh
  have hJG : J ≤ stabilizer d.radical a :=
    (SmallMover.join_le _ _ _ _).trans inf_le_right
  refine ⟨hderived,fun A hA => ?_⟩
  exact CubePairedKernel.abelian_action_preserves_fixed J (Z d.radical a) A
    (hJG.trans (Z_normalized d.radical a)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha))))


include e hz hn in
private theorem edgeMover_core_le
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) : Q d.radical a ≤ edgeMover (d := d) a t := by
  exact (EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat).2.2.1

omit [Finite G] in
private theorem edgeMover_le_stabilizer {a t : Vertex d.radical}
    (hat : Adjacent d.radical a t) :
    edgeMover (d := d) a t ≤ stabilizer d.radical a :=
  (SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))

include e hz hn in
/-- The actual edge mover preserves every full-seed fixer of its subactors. -/
private theorem edgeMover_preserves_seed_fixer_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ edgeMover (d := d) a t) :
    edgeMover (d := d) a t ≤ normalizer
      ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hE := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat
  have hEN : edgeMover (d := d) a t ≤ EightPairedNormalizer.relativeMover (d := d) a t :=
    hE.1.le.trans inf_le_right
  exact hEN.trans ((normalizer_mover_preserves_seed_fixer_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb ha hat).2 A (hA.trans hEN))

include e hz hn in
/-- Quadraticity holds on the entire seed, including the incident central attachment. -/
private theorem edgeMover_full_seed_quadratic_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅⁅Z d.radical a,edgeMover (d := d) a t⁆,edgeMover (d := d) a t⁆ = ⊥ := by
  let J := edgeMover (d := d) a t
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases ht : color d.radical t <;> simp_all
  have hJT : J ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hZt : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact fun y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hJT hy)
  have hZtn : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans
      (U_normalized a)
  rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat,
    commutator_sup_fixed _ _ _ hZtn hZt]
  exact (EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat).2.2.2.2.2.2.2.1

include e hz hn in
/-- Once the nonnormalizing trapped pair has supplied X = Z, equal neighboring
small movers put their entire neighbor-seed commutator in their central omega.
That omega is exactly the full starting-seed fixer, with all central elements. -/
private theorem equal_mover_omega_control_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (hXgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    let J := edgeMover (d := d) a t
    omegaCenter J = Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical c,J⁆ ≤ omegaCenter J := by
  have hX := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hXgen
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J := edgeMover (d := d) a t
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  have hQJ := edgeMover_core_le (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat
  have hQcJ : Q d.radical c ≤ J := by
    change Q d.radical c ≤ edgeMover (d := d) a t
    rw [←hequal]
    exact edgeMover_core_le (e := e) (hz := hz) (hn := hn) hne hcard hb hcol hct
  have hJG : J ≤ stabilizer d.radical a :=
    edgeMover_le_stabilizer (d := d) hat
  have hJGc : J ≤ stabilizer d.radical c := by
    change edgeMover (d := d) a t ≤ _
    rw [←hequal]
    exact edgeMover_le_stabilizer (d := d) hct
  have hZQ : Z d.radical a ≤ Q d.radical a := hX.ge.trans (omegaCenter_le _)
  have hZcX : Z d.radical c ≤ X d.radical c := by
    apply (replacementGeometry h d).omega_bound c hcol
    rw [(replacementGeometry h d).distance_constant c hcol]
    exact replacementDistance_pos h d
  have hOmegaZ : omegaCenter J ≤ Z d.radical a := by
    rw [←hX]
    intro x hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q d.radical a := by
      rw [←C_eq_Q s hc a ha]
      exact ⟨hJG hxJ,fun y hy => hxc y (hQJ (hZQ hy))⟩
    exact mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩
  have hquad : ⁅⁅Z d.radical c,J⁆,J⁆ = ⊥ := by
    have hh := edgeMover_full_seed_quadratic_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb hcol hct
    rwa [hequal] at hh
  have hcommZ : ⁅Z d.radical c,J⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hJGc.trans (Z_normalized d.radical c))
  have hcommJ : ⁅Z d.radical c,J⁆ ≤ J :=
    (hcommZ.trans hZcX).trans ((omegaCenter_le _).trans hQcJ)
  have hcommC : ⁅Z d.radical c,J⁆ ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp hquad
  refine ⟨le_antisymm (le_inf hOmegaZ ?_) ?_,?_⟩
  · intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hQJ (hZQ hx.1),
      (mem_omegaCenter_iff.mp (hX.ge hx.1)).2.1,hx.2⟩
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hcommJ hx,
      (mem_omegaCenter_iff.mp (hZcX (hcommZ hx))).2.1,hcommC hx⟩

include e hz hn in
/-- Both full commutators centralize their own mover; their intersection
centralizes the subgroup generated by the two literal transported movers. -/
private theorem equal_mover_pair_control_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (hXgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical a) :
    ⁅Z d.radical c,A⁆ ≤ Z d.radical a ∧
      ⁅Z d.radical c,A⁆ ⊓ ⁅Z d.radical (act d.radical x⁻¹ c),A⁆ ≤
        Z d.radical a ⊓ centralizer
          ((edgeMover (d := d) a t ⊔ (edgeMover (d := d) a t).map
            (MulAut.conj x).toMonoidHom : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let J := edgeMover (d := d) a t
  have hQJ := edgeMover_core_le (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat
  obtain ⟨hOmega,hcomm⟩ := equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat hct hequal hXgen
  have hcore : ⁅Z d.radical c,Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (commutator_mono le_rfl hQJ).trans (hcomm.trans_eq hOmega)
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hcore₂ : ⁅Z d.radical (act d.radical x⁻¹ c),Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer
        (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcore
    rw [map_commutator,←map_inf_centralizer_of_injective _ (MulAut.conj x).injective,hQa,hZa] at hh
    simpa only [Z_act,inv_inv] using hh
  have h₁ := (commutator_mono le_rfl hA).trans hcore
  have h₂ := (commutator_mono le_rfl hA).trans hcore₂
  refine ⟨h₁.trans inf_le_left,le_inf (inf_le_left.trans (h₁.trans inf_le_left)) ?_⟩
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (h₁.trans inf_le_right)))
    (le_centralizer_iff.mp (inf_le_right.trans (h₂.trans inf_le_right)))

include e hz hn in
/-- For paired trapped full seeds, the same actor controls both full reverse
kernels. The transporter only needs membership in the generated mover subgroup,
not generation of the whole stabilizer. This includes the zero second commutator. -/
private theorem paired_trapped_whole_seed_commutator_le_two_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hxpair : x ∈ edgeMover (d := d) a t ⊔
      (edgeMover (d := d) a t).map (MulAut.conj x).toMonoidHom)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    : Nat.card (⁅Z d.radical c,Z d.radical z ⊓ Q d.radical a ⊔
        Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆ :
          Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let F₂ := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let C₂ := Z d.radical (act d.radical x⁻¹ c)
  let P := Z d.radical a ⊔ Z d.radical c ⊔ C₂
  let K := ⁅P,F⁆
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hC₂ : C₂ = (Z d.radical c).map (MulAut.conj x).toMonoidHom := by
    simp only [C₂,Z_act,inv_inv]
  have hCV := neighbor_seed_le_radius hat hct
  have hC₂V : C₂ ≤ V d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hCV
    have he : (V d.radical a).map (MulAut.conj x).toMonoidHom = V d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical a hx)
    rwa [←hC₂,he] at hh
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVG := (replacementGeometry h d).V_local a p.start_color (by
    rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hC₂pre : C₂ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hq] at hh
    have he := Q_act d.radical x⁻¹ (act d.radical x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rwa [←hC₂,←he] at hh
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (sup_le hlast.2.2 (hpbad.trans hlast.2.1)) (hC₂pre.trans hlast.2.1)
  have hpreG : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ stabilizer d.radical z :=
    hlast.2.1.trans (fun _ hv => hv.2 _ (adjacent_symm d.radical hlast.1))
  have hXz := (SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hat hct hpbad hnorm).1
  have hXgen := X_central_generation_all p.end_color hXz a p.start_color
  have hcontrol := equal_mover_pair_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb p.start_color hat hct hequal hXgen x hx
    (Q d.radical a) le_rfl
  have hC₂Q : ⁅C₂,Q d.radical a⁆ ≤ Z d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcontrol.1
    rwa [map_commutator,←hC₂,hQa,hZa] at hh
  have hK : K ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ F (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) F (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl inf_le_right).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl inf_le_right).trans hcontrol.1
    · exact (commutator_mono le_rfl inf_le_right).trans hC₂Q
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  let : IsElementaryAbelian 2 C₂ := hC₂ ▸ IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hPQ : P ≤ Q d.radical a :=
    (sup_le (sup_le hAV hCV) hC₂V).trans (V_le_Q d.radical p.start_color hb2)
  have hder : ⁅P,P⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ P (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) P (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl hPQ).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl hPQ).trans hcontrol.1
    · exact (commutator_mono le_rfl hPQ).trans hC₂Q
  have hbound : Nat.card K ≤ 2 := SixteenEqual.combined_actor_kernel_card_le_two s hc hb2 p hsmall
    P (Z d.radical c) C₂ rfl inferInstance inferInstance hder
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hCV hPt hK hnorm
  have hne₁ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hCV
    (hpbad.trans hpreG) hnorm
  have h₁ : ⁅Z d.radical c,F⁆ ≤ K := commutator_mono (le_sup_right.trans le_sup_left) le_rfl
  have h₂ : ⁅C₂,F⁆ ≤ K := commutator_mono le_sup_right le_rfl
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  -- The source zero-commutator subcase: it would bound joint movement by K.
  by_cases hzero : ⁅C₂,F⁆ = ⊥
  · have hzero₂ : ⁅Z d.radical c,F₂⁆ = ⊥ := by
      have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hzero
      have hCback : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
        dsimp only [C₂]
        rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
      have hFback : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
        have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
          mem_normalizer_iff_map_conj_eq.mp
            (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
        dsimp only [F,F₂]
        rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
      rwa [map_commutator,hCback,hFback,Subgroup.map_bot] at hh
    have hNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))).trans
          (centralizer_le hK)).trans (Subgroup.centralizer_le_normalizer _)
    have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
      commutator_sup_le_of_relative_normal (Q d.radical a) F F₂ (Z d.radical c) K
        hNK inf_le_right inf_le_right
        (by rw [commutator_comm]; exact h₁)
        (by rw [commutator_comm,hzero₂]; exact bot_le)
    rw [commutator_comm] at hjoin
    exact (card_le_of_le hjoin).trans hbound

  let : Finite (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hpos₁ : 1 < Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₁
  have hpos₂ : 1 < Nat.card (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hzero
  have heq₁ : ⁅Z d.radical c,F⁆ = K := eq_of_le_of_card_ge h₁ (by omega)
  have heq₂ : ⁅C₂,F⁆ = K := eq_of_le_of_card_ge h₂ (by omega)
  let H := edgeMover (d := d) a t ⊔
    (edgeMover (d := d) a t).map (MulAut.conj x).toMonoidHom
  have hcentral : K ≤ centralizer (H : Set (FreeAmalgam d.radical)) := by
    have hh := (equal_mover_pair_control_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p.start_color hat hct hequal hXgen x hx F inf_le_right).2
    change ⁅Z d.radical c,F⁆ ⊓ ⁅C₂,F⁆ ≤ _ at hh
    rw [heq₁,heq₂,inf_idem] at hh
    exact hh.trans inf_le_right
  have hMK : H ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hmapK : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (hMK (H.inv_mem hxpair))
  have hmapC : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
    dsimp only [C₂]
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hmapF : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
    have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
    dsimp only [F,F₂]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
  have heq₃ : ⁅Z d.radical c,F₂⁆ = K := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₂
    rwa [map_commutator,hmapC,hmapF,hmapK] at hh
  have hQNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))).trans
        (centralizer_le hK)).trans (Subgroup.centralizer_le_normalizer _)
  have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
    commutator_sup_le_of_relative_normal (Q d.radical a) F F₂ (Z d.radical c) K
      hQNK inf_le_right inf_le_right
      (by rw [commutator_comm]; exact heq₁.le) (by rw [commutator_comm]; exact heq₃.le)
  rw [commutator_comm] at hjoin
  exact (card_le_of_le hjoin).trans hbound

include e hz hn in
/-- Residual generation by the actual edge mover and two endpoint seeds puts
the whole common fixer in the Baumann slice. Whole-stabilizer generation is unnecessary. -/
private theorem paired_trapped_fixer_le_slice_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (hgen : Ltilde d.radical a ≤ edgeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical w)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
    Z d.radical c ⊓ centralizer
      ((Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤
      B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  let F := Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical a
  let J := edgeMover (d := d) c t
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    have ht : color d.radical t = true := by
      cases he : color d.radical t
      · exact (h1 he.symm).elim
      · rfl
    cases he : color d.radical c
    · rfl
    · exact (h2 (he.trans ht.symm)).elim
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  have hZV : Z d.radical c ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hQJ : Q d.radical a ≤ J := by
    change Q d.radical a ≤ edgeMover (d := d) c t
    rw [hequal]
    exact edgeMover_core_le (e := e) (hz := hz) (hn := hn) hne hcard hb p.start_color hat
  have hFt : J ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (edgeMover_preserves_seed_fixer_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb hcol hct) A ((sup_le inf_le_right inf_le_right).trans hQJ)
  have hmove {v : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) a v)
      (hrs : (Q d.radical v).relIndex (Z d.radical a) < 4)
      (hrbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)))
      (hA : Z d.radical v ⊓ Q d.radical a ≤ A) :
      Z d.radical v ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    have hFmove : ⁅F,Z d.radical v⁆ ≤ Z d.radical a :=
      small_critical_predecessor_commutator s hc hb2 r hrs F (inf_le_left.trans hrbad)
        (inf_le_right.trans (centralizer_le hA))
    have hYmove : ⁅Y,Z d.radical v⁆ ≤ Z d.radical a :=
      commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        F (Z d.radical a) (Z d.radical v) (Z d.radical a)
        (Z_normalized d.radical a) ((inf_le_left.trans hZV).trans hVG)
        (Z_le_stabilizer d.radical a) hFmove
        (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical a))
    exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hJG : J ≤ stabilizer d.radical a := by
    change edgeMover (d := d) c t ≤ _
    rw [hequal]
    exact edgeMover_le_stabilizer hat
  have hYN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    apply hgen.trans
    refine sup_le (sup_le ?_ (hmove p hps hpbad le_sup_left)) (hmove q hqs hqbad le_sup_right)
    exact (le_inf hFt (hJG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYV : Y ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  have hYprod : Y ≤ Z d.radical c ⊔ Z d.radical a := sup_le_sup inf_le_left le_rfl
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective
      (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a))) (inclusion_injective _)
  have hindex : (Z d.radical a).relIndex Y ≤ 8 :=
    (relIndex_le_of_le_right hYprod index_ne_zero_of_finite).trans
      (DistanceFour.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
  exact le_sup_left.trans
    (residual_small_radius_le_slice_knownSimple (e := e) hb2 p.start_color Y hYV hYN hindex)

include e hz hn in
/-- A strict slice forces the simultaneous paired kernel commutator to have
order greater than two, with the same two kernels and the same selected seed. -/
private theorem paired_trapped_joint_movement_gt_two_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (hgen : Ltilde d.radical a ≤ edgeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical w)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    2 < Nat.card (⁅U d.radical c,Z d.radical z ⊓ Q d.radical a ⊔
      Z d.radical w ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
  by_contra! hbound
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t
    · exact (hh he.symm).elim
    · rfl
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c
    · rfl
    · exact (hh he).elim
  have hAG : A ≤ stabilizer d.radical c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hi := moving_small_commutator_fixed_index s hc hcol A hAG hbound
  have hFB := paired_trapped_fixer_le_slice_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb p q hps hqs hat hct hequal hgen hpbad hqbad
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
    (index_ne_zero_of_finite (H := (U d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hi)

include e hz hn in
/-- A strict trapped candidate is impossible under the literal edge-mover
comparison and residual generation, with the same transporter throughout. -/
private theorem paired_strict_trapping_false_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t =
      edgeMover (d := d) a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hxpair : x ∈ edgeMover (d := d) a t ⊔
      (edgeMover (d := d) a t).map (MulAut.conj x).toMonoidHom)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : Ltilde d.radical a ≤ edgeMover (d := d) c t ⊔
      Z d.radical z ⊔ Z d.radical (act d.radical x z))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  have hbound := paired_trapped_whole_seed_commutator_le_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hat hct hequal
      x hx q hq hxpair hpbad hqbad hnorm
  have hlarge := paired_trapped_joint_movement_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb p q hsmall hqs hat hct hequal
      hgen hpbad hqbad hstrict
  let := finite_Z d.radical c
  let H := ⁅Z d.radical c,Z d.radical z ⊓ Q d.radical a ⊔
    Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆
  have hHG : H ≤ Z d.radical c := by
    apply le_normalizer_iff_commutator_le_left.mp
    apply (le_trans _ (Z_normalized d.radical c))
    apply le_trans (sup_le inf_le_right inf_le_right)
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [p.start_color] at hh
      cases ht : color d.radical t <;> simp_all
    exact (Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hv => hv.2 _ (adjacent_symm d.radical hct))
  let : Finite H := Finite.of_injective (inclusion hHG) (inclusion_injective _)
  exact (Nat.not_le_of_gt hlarge) ((card_le_of_le
    (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl)).trans hbound)

include e hz hn in
/-- Equal actual edge movers exclude simultaneous trapping under paired
residual generation. Nonnormalization of a selected seed is derived. The proof also
handles a zero second commutator, and does not assume two nonnormalizing seeds. -/
theorem paired_traps_impossible_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover (d := d) c t = edgeMover (d := d) a t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : Ltilde d.radical a ≤ edgeMover (d := d) c t ⊔ Z d.radical z ⊔
      Z d.radical (act d.radical x z))
    (hxpair : x ∈ edgeMover (d := d) a t ⊔
      (edgeMover (d := d) a t).map (MulAut.conj x).toMonoidHom)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  by_cases hnorm : Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · have hnormq : ¬ Z d.radical (act d.radical x z) ≤ normalizer
        ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hnormal
      let Y := Z d.radical c ⊔ Z d.radical a
      have hJN : edgeMover (d := d) c t ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
        (le_inf ((edgeMover_le_stabilizer (d := d) hct).trans (Z_normalized d.radical c))
          ((hequal.le.trans (edgeMover_le_stabilizer (d := d) hat)).trans (Z_normalized d.radical a))).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
      have hYN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
        hgen.trans (sup_le (sup_le hJN hnorm) hnormal)
      have hYV : Y ≤ V d.radical a :=
        sup_le (neighbor_seed_le_radius hat hct) (Z_le_VBall d.radical a 2)
      have hUB : U d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
        (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
          (residual_small_radius_le_slice_knownSimple (e := e) (by omega : 2 < replacementDistance h d) p.start_color
            Y hYV hYN (DistanceFour.adjacent_seed_span_index_le_eight
              (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)))
      have hi := relIndex_eq_one.mpr hUB
      omega
    have hxa : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
    obtain ⟨r,hr⟩ : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        a (act d.radical x⁻¹ (act d.radical x z)),
        ∀ i, r.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
      have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ a) (act d.radical x⁻¹ (act d.radical x z)),
          ∀ i, r.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) :=
        ⟨q.act x⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
      rwa [hxa] at hh
    have hzx : act d.radical x⁻¹ (act d.radical x z) = z := by
      rw [←act_mul,mul_inv_cancel,act_one]
    have hrs : (Q d.radical (act d.radical x⁻¹ (act d.radical x z))).relIndex
        (Z d.radical a) < 4 := by rwa [hzx]
    have hbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)) := by
      have hrl : r.walk.length = p.walk.length := r.length_eq_b.trans p.length_eq_b.symm
      rw [hrl,hr,hq,←act_mul,mul_inv_cancel,act_one]
      exact hpbad
    have hgen' : Ltilde d.radical a ≤ edgeMover (d := d) c t ⊔
        Z d.radical (act d.radical x z) ⊔ Z d.radical (act d.radical x⁻¹ (act d.radical x z)) := by
      rw [hzx,sup_right_comm]
      exact hgen
    have hpair' : x⁻¹ ∈ edgeMover (d := d) a t ⊔
        (edgeMover (d := d) a t).map (MulAut.conj x⁻¹).toMonoidHom := by
      have hh := mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hxpair
      have hid : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro y
        change x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y
        group
      rw [Subgroup.map_sup,map_map,hid,map_id] at hh
      have hval : (MulAut.conj x⁻¹).toMonoidHom x = x := by simp
      rw [hval] at hh
      rw [sup_comm ((edgeMover (d := d) a t).map (MulAut.conj x⁻¹).toMonoidHom)
        (edgeMover (d := d) a t)] at hh
      exact (edgeMover (d := d) a t ⊔
        (edgeMover (d := d) a t).map (MulAut.conj x⁻¹).toMonoidHom).inv_mem hh
    exact paired_strict_trapping_false_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb q hqs hat hct hequal x⁻¹ ((stabilizer d.radical a).inv_mem hx)
      r hr hpair' hqbad hbad hnormq hrs hgen' hindex
  · exact paired_strict_trapping_false_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hat hct hequal x hx q hq hxpair hpbad hqbad hnorm hqs hgen hindex


include e hz hn in
/-- The equal-mover branch of (5.7) now has a constructed selection in both
three-duad cases. The resulting backward path overlaps the original path,
with the selected seed transported by the same starting-stabilizer element. -/
theorem equal_mover_generating_backward_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨g,hg,x,hxL,_,hat,hgen,hxpair,hleft,hright⟩ := EightGenerating.paired_generating_selection_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb hmodel p hsmall
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hEq : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    dsimp only [EightEdgeComparison.edgeMover] at hh ⊢
    rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hga] at hh
    exact hh
  have strict (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical y delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x z),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x z),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hqs : (Q d.radical (act d.radical x z)).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hLgen : Ltilde d.radical (alpha d.radical) ≤
      EightEdgeComparison.edgeMover (d := d) c t ⊔ Z d.radical z ⊔
        Z d.radical (act d.radical x z) := by
    rw [hEq,hgen]
    exact Ltilde_le_stabilizer _
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hdelta
    have hc : color d.radical delta = false := by
      change color d.radical delta ≠ true at hh
      cases hc : color d.radical delta <;> simp_all
    change color d.radical (act d.radical g delta) = false
    rw [action_preserves_color,hc]
  have backward {v : Vertex d.radical}
      (b : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) v)
      (hbad : ¬ Z d.radical c ≤ Q d.radical (b.walk.getVert (b.walk.length-2))) :
      ∃ r : CriticalPath d.radical (replacementGeometry h d)
          c (b.walk.getVert (b.walk.length-2)),
        r.walk.getVert 1 = t ∧
        ∀ i ≤ b.walk.length-2, r.walk.getVert (i+2) = b.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
      change 2 ≤ replacementDistance h d
      omega
    let r := b.prepend_two hb2 hcol w hw hbad
    refine ⟨r,?_,fun i hi => b.prepend_two_overlap _ _ _ _ _ hi⟩
    change (b.prepend_two _ hcol w hw hbad).walk.getVert 1 = t
    rw [CriticalPath.prepend_two_walk]
    simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,ite_true,
      w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · have hqbad : ¬ Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
      intro hqbad
      exact paired_traps_impossible_knownSimple
        (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hat hct hEq x hx q hq
          hqs hLgen hxpair hpbad hqbad (strict g hg)
    obtain ⟨r,hrt,hover⟩ := backward q hqbad
    let y := g*x⁻¹
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hx)
    have hstart : act d.radical x⁻¹ c = act d.radical y delta := by
      dsimp only [c,y]
      rw [act_mul]
    have hedge : act d.radical x⁻¹ t = act d.radical y (beta d.radical) := by
      dsimp only [t,y]
      rw [act_mul]
    have hxa' : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hx
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    refine ⟨y,hy,?_,?_,strict y hy,?_,?_⟩
    · have hh := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
      rwa [hxa',hedge] at hh
    · exact (adjacent_act_iff d.radical y _ _).mpr hdelta
    · have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hright
      rw [Subgroup.map_sup,←inv_inv x,←Q_act,←Z_act,←stabilizer_act,inv_inv,hxa',hedge,
        ←act_mul,mul_inv_cancel,act_one] at hh
      exact hh
    · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ c) (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1 = act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨r.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hrt]
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend,hedge] at hex
  · exact ⟨g,hg,hat,hct,strict g hg,hleft,backward p hpbad⟩


include e hz hn in
/-- Equal actual movers at the original first edge supply a generating backward
critical path, retaining the entire overlap and the strict transported seed. -/
theorem equal_backward_shift_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : edgeMover (d := d) delta (p.walk.getVert 1) =
      edgeMover (d := d) (alpha d.radical) (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨k,hk,hkt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
    hfirst (base_adjacent d.radical)
  change act d.radical k (p.walk.getVert 1) = beta d.radical at hkt
  have hka : act d.radical k (alpha d.radical) = alpha d.radical := hk
  have hdelta' : Adjacent d.radical (act d.radical k delta) (beta d.radical) := by
    rw [←hkt]
    exact (adjacent_act_iff d.radical k _ _).mpr hdelta
  have hequal' : edgeMover (d := d) (act d.radical k delta) (beta d.radical) =
      edgeMover (d := d) (alpha d.radical) (beta d.radical) := by
    have hh := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hequal
    dsimp only [edgeMover] at hh ⊢
    rwa [SmallMover.join_map _ (MulAut.conj k⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj k⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hka,hkt] at hh
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj k⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb _ rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hk))
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical k delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hstrict
  obtain ⟨g,hg,hat,hct,hi,hgen,q,hq,hover⟩ :=
    equal_mover_generating_backward_knownSimple hne hcard hb hmodel p hsmall
      hdelta' hequal' hstrict'
  have he : act d.radical g (act d.radical k delta) = act d.radical (k*g) delta :=
    (act_mul d.radical k g delta).symm
  refine ⟨act d.radical g (beta d.radical),hat,k*g,mul_mem hk hg,?_,?_,hgen,?_,?_⟩
  · rw [act_mul,hkt]
  · simpa only [he] using hct
  · simpa only [he] using hi
  · exact he ▸ ⟨q,hq,hover⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
