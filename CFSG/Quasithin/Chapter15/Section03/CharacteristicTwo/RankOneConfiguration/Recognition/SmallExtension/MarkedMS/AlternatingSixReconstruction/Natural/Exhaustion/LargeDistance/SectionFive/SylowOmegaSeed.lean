module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowReverseGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer

/-!
# The small mover's whole omega center and the terminal seed

A full omega vector fixed by the three-transposition small mover has even
six-letter displacement coordinates: each paired coordinate agrees, so the
augmentation is zero. It therefore belongs to the moved cover plus the full
central summand. The latter lies in every incident edge seed. Consequently
the small mover fixes no omega vector outside the full starting seed,
including in the permutation-extension case.

This identifies the entire omega center of the small mover with its fixer
in that seed. Equal neighboring movers then put their commutators with the
whole adjacent core in both full seeds and the common mover's center. The
proved mover equality above distance six applies this to the actual terminal
critical line: the line lies in the intermediate seed, has order two, and
remains noncentral in the whole intermediate stabilizer.

The original-radical application constructs its generating shift chain and
retains the literal radical restriction and transporter. Both moving covers
of orders sixteen and thirty-two and all central attachments remain. The
terminal radius contradiction, distance-six mover comparison, image-eight
branch and distance-four whole-core estimates remain with this owner.
The internal imports reuse the full-omega displacement coordinates and
whole-seed quadratic action within this source proof family.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.3), (5.6) and (5.10)--(5.11), printed pp.915,917--918,922--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowOmegaSeed
local notation "S" => Equiv.Perm (Fin 6)

private theorem cube_fixed_coordinates
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0)
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g : S, ρ g z-z = j (SeedCoordinates.displacement g w))
    (u : S) (hz : z ∈ fixedSpace ρ ((D 6).map (MulAut.conj u).toMonoidHom)) :
    z ∈ j.toLinearMap.range ⊔ ρ.invariants := by
  have he (a b : Fin 6) (hab : a ≠ b) (hs : Equiv.swap a b ∈ D 6) :
      w (u a) + w (u b) = 0 := by
    have hf := hz ⟨(MulAut.conj u) (Equiv.swap a b),mem_map_of_mem _ hs⟩
    change ρ ((MulAut.conj u) (Equiv.swap a b)) z = z at hf
    have hh := hw ((MulAut.conj u) (Equiv.swap a b))
    rw [hf,sub_self] at hh
    have hc : (MulAut.conj u) (Equiv.swap a b) = Equiv.swap (u a) (u b) := by
      exact (Equiv.swap_apply_apply u a b).symm
    rw [hc,SeedCoordinates.displacement_swap,map_smul] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_right (hj _ _ (u.injective.ne hab))
  have h01 := he 0 1 (by decide)
    ((mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨1,by decide +kernel⟩)
  have h23 := he 2 3 (by decide)
    ((mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨2,by decide +kernel⟩)
  have h45 := he 4 5 (by decide)
    ((mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨4,by decide +kernel⟩)
  have hzero : augmentation (Fin 6) w = 0 := by
    change ∑ i : Fin 6, w i = 0
    rw [←Equiv.sum_comp u w]
    simp only [Fin.sum_univ_succ]
    change w (u 0) + (w (u 1) + (w (u 2) + (w (u 3) + (w (u 4) + (w (u 5) + 0))))) = 0
    linear_combination h01 + h23 + h45
  let v : core (Fin 6) := ⟨w,hzero⟩
  have hf : z-j v ∈ ρ.invariants := by
    intro g
    have he : SeedCoordinates.displacement g w = coreRepresentation (Fin 6) g v-v := by
      apply Subtype.ext
      rfl
    have hh := hw g
    rw [he,map_sub,j.isIntertwining] at hh
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hh
  have hm := Submodule.add_mem_sup (LinearMap.mem_range_self j.toLinearMap v) hf
  change j v + (z-j v) ∈ _ at hm
  have hh : j v + (z-j v) = z := by abel
  rwa [hh] at hm

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem exists_small_base
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    ∃ z, ∃ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  obtain ⟨q,_⟩ := SylowShiftChain.backwardShift_with_edge
    (e := e) (hz := hz) (hn := hn) hb hcard p
  obtain ⟨r,_⟩ := SylowShiftChain.backwardShift_with_edge
    (e := e) (hz := hz) (hn := hn) hb hcard q.path
  have hs := (SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r).2.1
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical r.path.start_color
  have he : act d.radical g⁻¹ r.start = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hsmall : (Q d.radical (act d.radical g⁻¹
      (q.path.walk.getVert (q.path.walk.length-2)))).relIndex
      (Z d.radical (act d.radical g⁻¹ r.start)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,hs]
    decide
  have pp := r.path.act g⁻¹
  rw [he] at pp hsmall
  exact ⟨_,pp,hsmall⟩

include e hz hn in
private theorem fixed_omega_base
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    omegaCenterIn (pCore 2 d.overgroup) ⊓ centralizer (J : Set d.overgroup) ≤
      replacementMoved d ⊔ (omegaCenterIn (pCore 2 d.overgroup) ⊓ center d.overgroup) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let X₀ := omegaCenterIn (pCore 2 d.overgroup)
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨z,p,hsmall⟩ := exists_small_base (e := e) (hz := hz) (hn := hn) hb hcard
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨j,hjr,hj,hcoords⟩ := full_X_displacement_coordinates s hc p hsmall
  obtain ⟨u,_,_,hJ,hJi,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard
  have himage : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    dsimp only [J]
    rw [←hnormal,hJ]
    exact hJi
  change X₀ ⊓ centralizer (J : Set d.overgroup) ≤ replacementMoved d ⊔ (X₀ ⊓ center d.overgroup)
  rintro x ⟨hx,hxf⟩
  let v : Additive X₀ := Additive.ofMul ⟨x,hx⟩
  have hv : v ∈ fixedSpace (omegaAction s) (J.map s.projection) := by
    rintro ⟨g,hg⟩
    obtain ⟨m,hm,rfl⟩ := hg
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((omegaAction s (s.projection m) v).toMul : d.overgroup) = x
    rw [omegaAction_conjugate]
    exact mul_inv_eq_iff_eq_mul.mpr (hxf m hm)
  rw [himage] at hv
  obtain ⟨w,hw⟩ := hcoords v
  have hmem := cube_fixed_coordinates (omegaAction s) j hj v w hw u hv
  rw [hjr] at hmem
  obtain ⟨v',⟨v₀,rfl⟩,w',hw',he⟩ := Submodule.mem_sup.mp hmem
  have hwc : (w'.toMul : d.overgroup) ∈ center d.overgroup := by
    apply mem_center_iff.mpr
    intro m
    have hh := congrArg (fun z : Additive X₀ => (z.toMul : d.overgroup))
      (hw' (s.projection m))
    rw [omegaAction_conjugate] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hm : (v₀.toMul : d.overgroup) * (w'.toMul : d.overgroup) = x :=
    congrArg (fun z : Additive X₀ => (z.toMul : d.overgroup)) he
  rw [←hm]
  exact (replacementMoved d ⊔ (X₀ ⊓ center d.overgroup)).mul_mem
    (mem_sup_left v₀.toMul.property) (mem_sup_right ⟨w'.toMul.property,hwc⟩)

private theorem central_omega_le_seed {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ≤
      Z d.radical a := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases ht : color d.radical t <;> simp_all
  apply le_trans _ (adjacent_Z_le d.radical ha hat)
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx.1
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hat hxQ,hx2,
    fun y hy => hx.2 y (hy.2 a (adjacent_symm d.radical hat))⟩

include e hz hn in
private theorem fixed_omega_base_graph
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    let J := SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
      (Q d.radical (beta d.radical)) 4
    X d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ≤
      Z d.radical (alpha d.radical) := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  have hmap : J₀.map (embedM d.radical) =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (beta d.radical)) 4 := by
    rw [SmallMover.join_map _ (embedM_injective _),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←Q_beta]
  have hh := map_mono (f := embedM d.radical)
    (fixed_omega_base (e := e) (hz := hz) (hn := hn) hb hcard)
  change (omegaCenterIn (pCore 2 d.overgroup) ⊓ centralizer (J₀ : Set d.overgroup)).map _ ≤ _ at hh
  rw [←map_inf_centralizer_of_injective _ (embedM_injective _),omega_map (h := h),hmap,
    Subgroup.map_sup,←hc.U_eq_moved] at hh
  have he : center d.overgroup = centralizer ((⊤ : Subgroup d.overgroup) : Set d.overgroup) := by
    rw [coe_top,centralizer_univ]
  rw [he,←map_inf_centralizer_of_injective _ (embedM_injective _),omega_map (h := h),
    ←MonoidHom.range_eq_map] at hh
  have hir : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  rw [hir] at hh
  exact hh.trans (sup_le (DistanceEight.U_le_Z d.radical _)
    (central_omega_le_seed rfl (base_adjacent d.radical)))

include e hz hn in
/-- The maximum small mover fixes no extra omega vector outside the full seed.
This includes the permutation-extension case and both moving-cover orders. -/
theorem small_mover_fixed_omega_le_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    X d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ≤ Z d.radical a := by
  obtain ⟨g,⟨hga,hgt⟩ | ⟨hga,hgt⟩⟩ := (adjacent_iff_exists_common d.radical _ _).mp hat
  swap
  · rw [hga] at ha
    cases ha
  have ha' : act d.radical g (alpha d.radical) = a := by
    rw [hga,alpha,act_mVertex,one_mul]
  have ht' : act d.radical g (beta d.radical) = t := by
    rw [hgt,beta,act_hVertex,one_mul]
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (fixed_omega_base_graph (e := e) (hz := hz) (hn := hn) hb hcard)
  dsimp only at hh ⊢
  rw [←map_inf_centralizer_of_injective _ (MulAut.conj _).injective,
    SmallMover.join_map _ (MulAut.conj _).injective,←X_act,←U_act,←Q_act,←Q_act,←Z_act,ha',ht'] at hh
  exact hh

include e hz hn in
/-- The entire omega center of the small mover is exactly its fixer in the
full starting seed. No central-generation assumption on X is needed. -/
theorem small_mover_omega_eq_seed_fixed_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    omegaCenter J = Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨hQJ,hJT,_⟩ := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have hJG : J ≤ stabilizer d.radical a := hJT.trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hZX : Z d.radical a ≤ X d.radical a := by
    apply (replacementGeometry h d).omega_bound a ha
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  have hZQ : Z d.radical a ≤ Q d.radical a := hZX.trans (omegaCenter_le _)
  have hΩX : omegaCenter J ≤ X d.radical a := by
    intro x hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q d.radical a := by
      rw [←C_eq_Q s hc a ha]
      exact ⟨hJG hxJ,fun y hy => hxc y (hQJ (hZQ hy))⟩
    exact mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩
  have hΩC : omegaCenter J ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have hΩZ := (le_inf hΩX hΩC).trans
    (small_mover_fixed_omega_le_seed_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard ha hat)
  apply le_antisymm (le_inf hΩZ hΩC)
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hQJ (hZQ hx.1),
    (mem_omegaCenter_iff.mp (hZX hx.1)).2.1,hx.2⟩

include e hz hn in
/-- Equal neighboring movers control the commutator with the whole starting
core inside both full seeds and the common mover's center. -/
theorem equal_mover_whole_core_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    ⁅Z d.radical c,Q d.radical a⁆ ≤ (Z d.radical c ⊓ Z d.radical a) ⊓
      centralizer (J : Set (FreeAmalgam d.radical)) := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hc : color d.radical c = false := by
    have h₁ := adjacent_color_ne d.radical hat
    have h₂ := adjacent_color_ne d.radical hct
    rw [ha] at h₁
    cases hcc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have he := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  have hQcJ : Q d.radical c ≤ J := he.1.trans_eq hequal
  have hJGc : J ≤ stabilizer d.radical c := hj.2.1.trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hcommZ : ⁅Z d.radical c,J⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hJGc.trans (Z_normalized d.radical c))
  have hquad : ⁅⁅Z d.radical c,J⁆,J⁆ = ⊥ := by
    have hh := SylowPairedFixer.small_mover_full_seed_quadratic
      (e := e) (hz := hz) (hn := hn) hb hcard hc hct
    dsimp only at hh
    rwa [hequal] at hh
  have hZX : Z d.radical c ≤ X d.radical c := by
    apply (replacementGeometry h d).omega_bound c hc
    rw [(replacementGeometry h d).distance_constant c hc]
    exact replacementDistance_pos h d
  have hcommΩ : ⁅Z d.radical c,J⁆ ≤ omegaCenter J := by
    intro x hx
    have hxX := hZX (hcommZ hx)
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hxX
    exact mem_omegaCenter_iff.mpr ⟨hQcJ hxQ,hx2,
      commutator_eq_bot_iff_le_centralizer.mp hquad hx⟩
  have hΩ := small_mover_omega_eq_seed_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  change omegaCenter J = _ at hΩ
  have h₁ := (commutator_mono le_rfl hj.1).trans hcommZ
  have h₂ := (commutator_mono le_rfl hj.1).trans (hcommΩ.trans_eq hΩ)
  exact le_inf (le_inf h₁ (h₂.trans inf_le_left)) (h₂.trans inf_le_right)

include e hz hn in
/-- Above six, mover equality places the terminal critical line in the full
intermediate seed, strengthening its known whole-omega placement. The line
has order two and remains noncentral in the intermediate whole stabilizer. -/
theorem three_shift_terminal_line_in_seed_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let w := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start,Z d.radical w⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical t.start ⊓ Z d.radical r.start ⊓ Z d.radical w ∧
      ¬ H ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) := by
  have hb4 : 4 < replacementDistance h d := by omega
  have heq := SylowReverseGeneration.critical_mover_eq_gt_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path
  have ht2 : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  rw [t.first,ht2] at heq
  have hcomm := equal_mover_whole_core_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hcard r.path.start_color
    t.adjacent_start t.adjacent_shift heq
  let w := r.path.walk.getVert (r.path.walk.length-2)
  have hwQ : Z d.radical w ≤ Q d.radical r.start := by
    apply Z_le_Q_of_dist_lt d.radical w ((replacementGeometry h d).exists_critical w t.path.end_color)
    rw [(replacementGeometry h d).distance_constant w t.path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist r.start (r.path.walk.getVert (r.path.walk.length-2)) < _
    rw [r.path.dist_start (Nat.sub_le _ _)]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-2 < replacementDistance h d
    omega
  have hHW : ⁅Z d.radical t.start,Z d.radical w⁆ ≤ Z d.radical w :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical w)
  have hsmall := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 q.path r t
  exact ⟨hsmall.2.2.2.1,le_inf ((commutator_mono le_rfl hwQ).trans
    (hcomm.trans inf_le_left)) hHW,hsmall.1⟩

include e hz hn in
/-- The literal original radical supplies a generating shift chain whose
terminal line belongs to all three indicated whole seeds and remains
noncentral. Its original restriction, transporter and both covers are retained. -/
theorem original_radical_terminal_line_in_seed_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ p₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      SylowTerminalPath.ShiftChain (h := h) q₀.path p₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) p₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path),
      let w := r.path.walk.getVert (r.path.walk.length-2)
      let H := ⁅Z d.radical t.start,Z d.radical w⁆
      Nat.card H = 2 ∧ H ≤ Z d.radical t.start ⊓ Z d.radical r.start ⊓ Z d.radical w ∧
        ¬ H ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,_⟩ :=
    original_radical_orbit_terminal_normalization_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 4 < replacementDistance h d) hcard p hfirst
  exact ⟨q₀,hqe,hqT,hqgen,c,c',p₀,hchain,q,r,t,
    three_shift_terminal_line_in_seed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p₀ q r t⟩

end SylowOmegaSeed
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
