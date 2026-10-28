module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Eligible slices on the original cubic graph

A two-subgroup of the full vertex seed centralizer lies in the actual
two-core: transport puts it inside E, and the odd quotient E/Q removes its
image. This does not identify the full centralizer with Q. It supplies the
predecessor containment needed to prove that the forward-kernel commutator
vanishes exactly when the whole second cover lies in the starting Baumann
slice. The proof uses normal generation of the entire selected span and
the literal reverse critical kernel, retaining both central covers.

Nontrivial residual movement of the radius selects an eligible neighbor
at every oriented edge, and hence an actual shortest two-edge segment
through the first edge of each critical path. Independently, source forward
nonnormality shows that the starting cover escapes the second vertex's
Baumann slice. Both indices are therefore at least two.

In the small critical-image branch an eligible forward slice of index at
most two yields a noncentral line of order two, without assuming that the
selected span is nonabelian. The actual whole-core and C.1.32 applications
retain the contained, large and index-two slice alternatives, the cubic
kernel and both full covers. These results do not prove the stronger slice
inequality, identify R4/R6, or complete (5.11)--(5.12). Those exclusions,
the remaining edge-image choices and final reconstruction remain with
qt-e-ms-small-a6-reconstruction; independent natural exhaustion remains
with qt-e-ms-small-a6-exhaustion-large-distance.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(iv), pp.856--857;
the eligible-neighbor and forward-kernel arguments in (5.8)--(5.9),
pp.919--922. Adapts Natural.Exhaustion.LargeDistance.SectionFive.ForwardSlice
and ReciprocalSlice, replacing their full-centralizer equality by the
proved two-subgroup containment across E/Q.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "Rg" => edge L R
omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc


include h e hz in
/-- Two-subgroups of the full seed centralizer lie in Q, despite its cubic kernel. -/
theorem two_subgroup_seed_centralizer_le_core {a : Vertex Rg}
    (ha : color Rg a = false) (A : Subgroup (FreeAmalgam Rg))
    (hA : IsPGroup 2 A) (hAC : A ≤ C Rg a) : A ≤ Q Rg a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let i := f.comp (embedM Rg)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective Rg)
  have hC : C Rg (mVertex Rg g) = (C Rg (alpha Rg)).map f := by
    simpa only [alpha,act_mVertex,one_mul] using C_act g (alpha Rg)
  have hQ : Q Rg (mVertex Rg g) = (pCore 2 M).map i := by
    rw [←map_map,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using Q_act Rg g (alpha Rg)
  have hAE : A ≤ (extensionKernel h).map i := by
    apply hAC.trans
    rw [hC]
    exact (map_mono (f := f) (graph_C_le_extensionKernel h e)).trans_eq (map_map _ _ _)
  have hAm : (A.comap i).map i = A := map_comap_eq_self (hAE.trans (map_le_range _ _))
  have hEi : A.comap i ≤ extensionKernel h := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hAm]
  have hcore := two_subgroup_le_core_of_le_extensionKernel h hz (A.comap i)
    (hA.comap_of_injective i hi) hEi
  rw [hQ,←hAm]
  exact map_mono hcore

include h in
private theorem radius_le_predecessor_stabilizer (hb : 2 < sourceDistance h)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    V Rg (alpha Rg) ≤ stabilizer Rg (p.walk.getVert (p.walk.length-2)) := by
  apply (V_le_iff Rg rfl _).mpr
  intro v hd hdist
  apply Z_le_stabilizer_of_dist_le v ((sourceGeometry h).exists_critical v hd)
  rw [(sourceGeometry h).distance_constant v hd]
  change (cosetGraph Rg).dist v (p.walk.getVert (p.walk.length-2)) ≤ sourceDistance h
  have ht := (cosetGraph_connected Rg).dist_triangle (u:=v) (v:=alpha Rg)
    (w:=p.walk.getVert (p.walk.length-2))
  rw [p.dist_start (Nat.sub_le _ _)] at ht
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  omega

include h e hz hk in
/-- In the small critical branch the full forward kernel fixes the moving
cover exactly when that cover is in the starting Baumann slice. No
nonabelian orbit-span assumption is used. -/
theorem small_forward_kernel_eq_bot_iff_slice
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ = ⊥ ↔
      U Rg (p.walk.getVert 2) ≤
        B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hseed : Z Rg t ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  constructor
  · intro hzero
    have hZc : Z Rg c ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
      rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero) hseed
    have hNC : stabilizer Rg (alpha Rg) ≤ normalizer
        (centralizer (T : Set (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      hTN.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
    have hPC : P ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
      dsimp only [P]
      rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      rintro _ ⟨z,hz,rfl⟩
      exact (mem_normalizer_iff.mp
        (hNC ((stabilizer Rg (alpha Rg)).inv_mem g.property)) z).mp (hZc hz)
    have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
    have hinner := selected_forward_kernel_contains_inner_layers (h := h) hb p
    have hpre : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
      apply (p.vertex_color (Nat.sub_le _ _)).mpr
      have he := sourceDistance_even h
      rw [Nat.even_iff] at he ⊢
      have hh : p.walk.length = sourceDistance h := p.length_eq_b
      omega
    have hPpre : P ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
      apply two_subgroup_seed_centralizer_le_core h e hz hpre P
        ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
          (alpha Rg) rfl).to_le ((selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left))
      exact le_inf (hPV.trans (radius_le_predecessor_stabilizer (h := h) hb p))
        (hPC.trans (centralizer_le (show Z Rg (p.walk.getVert (p.walk.length-2)) ≤ T from le_sup_left.trans hinner)))
    have hcomm : ⁅P,Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
      small_critical_predecessor_commutator h e hz hk hb p hsmall P hPpre
        (hPC.trans (centralizer_le (show Z Rg a' ⊓ Q Rg (alpha Rg) ≤ T from le_sup_right.trans hinner)))
    exact (DistanceEight.U_le_Z Rg c).trans ((Z_le_localZSpan Rg _ _).trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p P hPV
        (localZSpan_normalized Rg _ _) hcomm))
  · intro hslice
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    change T ≤ centralizer (U Rg c : Set (FreeAmalgam Rg))
    intro x hx y hy
    exact hx.2 y ⟨hy,hslice hy⟩


include h e hz hk in
/-- Residual movement of every graph radius escapes the full seed. -/
theorem graph_radius_moving_not_le_seed (hb : 2 < sourceDistance h)
    (a : Vertex Rg) (ha : color Rg a = false) :
    ¬ ⁅V Rg a,Ltilde Rg a⁆ ≤ Z Rg a := by
  have hbase : ¬ ⁅V Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) := by
    intro hh
    apply radius_moving_not_le_seed h e hz hk hb
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    have hZ : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
      map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
    have hK : (L.subgroupOf (L ⊔ R)).map (embedM Rg) = Ltilde Rg (alpha Rg) := by
      rw [Ltilde_alpha,h.relative_residual]
    rwa [map_commutator,radius_comap_map (h := h) hb,hK,hZ]
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  have hV := V_act Rg g (alpha Rg)
  have hL := Ltilde_act Rg g (alpha Rg)
  have hZ := Z_act Rg g (alpha Rg)
  simp only [alpha,act_mVertex,one_mul] at hV hL hZ
  rw [hV,hL,hZ,←map_commutator,map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  exact hbase

include h e hz hk in
/-- Every source edge admits a neighboring moved cover outside the Baumann slice.
The whole radius cannot be fixed modulo its seed, and normal generation of
one edge radius reduces that noncontainment to a single neighbor. -/
theorem exists_eligible_neighbor_at_edge
    (hb : 2 < sourceDistance h)
    {a t : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) :
    ∃ c, Adjacent Rg c t ∧
      ¬ U Rg c ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hVB : ¬ V Rg a ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro hVB
    apply graph_radius_moving_not_le_seed h e hz hk hb a ha
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    exact ((mem_B_iff Rg a _
      ((sourceGeometry h).V_local a ha (by
        rw [(sourceGeometry h).distance_constant a ha]; exact hb)) v).mp (hVB hv)).2 l hl
  by_contra! hn
  apply hVB
  apply radius_le_of_normalized_edge ha hat _ _
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
  apply CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion.radius_le_of_h_neighbors ha hat
  intro c hct
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [ha] at h1
    cases he : color Rg c <;> cases ht : color Rg t <;> simp_all
  rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
  exact sup_le (hn c hct)
    ((adjacent_Z_le Rg ha hat).trans (Escape.EdgeTransfer.Z_le_B hb a ha))



private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K≤normalizer (N:Set G))
    (hcomm : ⁅K,H⁆≤N) : K≤normalizer ((N⊔H:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N⊔H).map (MulAut.conj k).toMonoidHom≤N⊔H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N⊔H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)


include h e hz in
/-- The starting moved cover escapes the Baumann subgroup at the second
vertex of every actual critical path. This is the forward nonnormality
argument of MS93 (2.2)(iv), with the original central cover retained. -/
theorem critical_start_not_le_second_slice (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ¬ U Rg a ≤ B Rg (p.walk.getVert 2)
      ((sourceGeometry h).Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hpos : 0 < criticalDistance Rg a ((sourceGeometry h).exists_critical a p.start_color) := by
    rw [(sourceGeometry h).distance_constant a p.start_color]
    exact sourceDistance_pos h
  have hac : (cosetGraph Rg).dist a c = 2 := p.dist_start (by omega)
  have hpath : (cosetGraph Rg).dist c a' + 2 = (cosetGraph Rg).dist a a' := by
    rw [p.dist_end,←p.shortest]
    omega
  have hn := (critical_nonnormal_forward Rg (sourceGeometry h)
    (sourceEdgeCentralizer h e) a p.start_color hpos a' p.critical c hac hpath).2
  intro hU
  have hZB : Z Rg a ≤ B Rg c ((sourceGeometry h).Z_normal _) := by
    rw [vertex_seed_eq_moving_sup_edge h e hz p.start_color hat]
    exact sup_le hU ((adjacent_Z_le Rg hcol hct).trans
      (Escape.EdgeTransfer.Z_le_B hb c hcol))
  have hZX : Z Rg c ≤ X Rg c :=
    Z_le_X_of_positive Rg c hcol ((sourceGeometry h).exists_critical c hcol)
      (by rw [(sourceGeometry h).distance_constant c hcol]; exact sourceDistance_pos h)
  apply hn
  apply normal_subgroupOf_of_le_normalizer
  have hgen : pResidual 2 M ⊔ Rg = ⊤ := by
    rw [h.relative_residual]
    exact (codisjoint_subgroupOf_sup L R).eq_top
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg hgen hcol hct,sup_comm (Z Rg a) (X Rg c)]
  apply sup_le
  · apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (X_normalized Rg c)
    · apply commutator_le.mpr
      intro l hl z hz
      exact hZX (((mem_B_iff Rg c _
        ((sourceGeometry h).V_local c hcol (by
          rw [(sourceGeometry h).distance_constant c hcol]; exact hb)) z).mp (hZB hz)).2 l hl)
  · have htG : Q Rg t ≤ stabilizer Rg a :=
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)
    have htC : Q Rg t ≤ stabilizer Rg c :=
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)
    exact (le_inf (htC.trans (X_normalized Rg c))
      (htG.trans (Z_normalized Rg a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include h e hz in
/-- The reciprocal slice on the literal critical path has index at least
two, without a backward-escape or natural-subgroup hypothesis. -/
theorem critical_start_slice_index_two_le (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    2 ≤ (B Rg (p.walk.getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  have hpos : 0 < (B Rg (p.walk.getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (B Rg (p.walk.getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) ≠ 1 :=
    fun he => critical_start_not_le_second_slice h e hz hb p (relIndex_eq_one.mp he)
  omega


include h e hz hk in
/-- An eligible small forward slice yields a noncentral line of order two,
without a nonabelian-span hypothesis. Both covering modules remain intact. -/
theorem small_forward_slice_noncentral_line
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    let H := ⁅U Rg (p.walk.getVert 2),T⁆
    Nat.card H = 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ∧
      ¬ H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hTG : T ≤ stabilizer Rg c :=
    hTQt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHne : H ≠ ⊥ := fun he => heligible
    ((small_forward_kernel_eq_bot_iff_slice h e hz hk hb p hsmall).mp he)
  have hline := selected_forward_kernel_line h e hz hk hb p hslice
  let := finite_Z Rg t
  let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hHne
  refine ⟨?_,hline.2,?_⟩
  · change Nat.card H = 2
    have hh := hline.1
    change Nat.card H ≤ 2 at hh
    omega
  · intro hcentral
    obtain ⟨i,hi,hir,hiQ,hiE,hiU,hiC⟩ := graph_cover h e hz hk c hcol
    let A := T.comap i
    have hmA : A.map i = T := map_comap_eq_self (hTG.trans_eq hir.symm)
    have hcA : ⁅W,A⁆ ≤ center M := by
      intro x hx
      apply mem_center_iff.mpr
      intro m
      apply hi
      simp only [map_mul]
      apply hcentral
      · have hh := mem_map_of_mem i hx
        rw [map_commutator,hmA,hiU] at hh
        exact hh
      · rw [←hir]
        exact ⟨m,rfl⟩
    have hle := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk A
      (((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        (alpha Rg) rfl).to_le (show T ≤ Q Rg (alpha Rg) from inf_le_left)).comap_of_injective i hi) hcA)
    rw [hmA,hiQ] at hle
    exact hHne (le_bot_iff.mp ((commutator_mono
      (DistanceEight.U_le_Z Rg c) hle).trans_eq (Z_centralizes_Q Rg c hcol)))
include h e hz hk in
/-- The original cubic graph supplies an eligible neighbor of its first
edge. Its index is at least two; the stronger bound needed for the backward
critical shift is not assumed or asserted here. -/
theorem exists_eligible_first_edge_path
    (hb : 2 < sourceDistance h)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ (c : Vertex Rg) (w : (cosetGraph Rg).Walk c a),
      color Rg c = false ∧ w.length = 2 ∧
      w.length = (cosetGraph Rg).dist c a ∧
      w.getVert 1 = p.walk.getVert 1 ∧
      2 ≤ (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb p.start_color hat
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hp : 0 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≠ 1 :=
    fun he => hel (relIndex_eq_one.mp he)
  have hi : 2 ≤ (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by omega
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases he : color Rg c <;> cases ht : color Rg (p.walk.getVert 1) <;> simp_all
  have hne : c ≠ a := by
    intro he
    apply hel
    rw [he]
    exact (DistanceEight.U_le_Z Rg a).trans
      (Escape.EdgeTransfer.Z_le_B hb a p.start_color)
  let w : (cosetGraph Rg).Walk c a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  have hdle : (cosetGraph Rg).dist c a ≤ 2 := hw ▸ SimpleGraph.dist_le w
  have hdgt : 1 < (cosetGraph Rg).dist c a :=
    (cosetGraph_connected Rg).one_lt_dist_of_ne_of_not_adj hne (by
      intro hadj
      exact adjacent_color_ne Rg ((cosetGraph_adj Rg _ _).mp hadj)
        (hcol.trans p.start_color.symm))
  exact ⟨c,w,hcol,hw,by omega,rfl,hi⟩
include h e hz hk in
/-- The actual forward slice is contained, large, or has the noncentral
order-two line. Nonabelianness of its selected span is no longer required. -/
theorem small_forward_slice_alternative (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    let c := p.walk.getVert 2
    let F := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∨
      (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
      Nat.card (⁅U Rg c,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅U Rg c,F⁆ ≤ Z Rg (p.walk.getVert 1) ∧
      ¬ ⁅U Rg c,F⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  dsimp only
  by_cases hel : U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)
  · exact Or.inl hel
  · right
    by_cases hi : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2))
    · exact Or.inl hi
    · right
      have hup : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 := by omega
      let := finite_Z Rg (p.walk.getVert 2)
      let : Finite (U Rg (p.walk.getVert 2)) := Finite.of_injective
        (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
      have hp : 0 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) := Nat.pos_of_ne_zero index_ne_zero_of_finite
      have hn : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
      exact ⟨by omega,small_forward_slice_noncentral_line h e hz hk hb p hup hsmall hel⟩

omit hk in
include h e hz in
/-- Whole-core application of the eligible-slice family. The original
cubic kernel and both full covers are retained. Strict index greater than
two, the remaining marked edge choices and terminal exclusions still belong
to this reconstruction owner. -/
theorem coreExhaustion_or_cubic_eligible_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ a a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a a',
        2 ≤ (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) ∧
        ∃ (c : Vertex Rg) (w : (cosetGraph Rg).Walk c a),
          color Rg c = false ∧ w.length = 2 ∧
          w.length = (cosetGraph Rg).dist c a ∧
          w.getVert 1 = p.walk.getVert 1 ∧
          2 ≤ (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        let c := p.walk.getVert 2
        let F := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
        U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∨
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
          Nat.card (⁅U Rg c,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅U Rg c,F⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          ¬ ⁅U Rg c,F⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun a a' p => ⟨critical_start_slice_index_two_le h e hz hb p,
        exists_eligible_first_edge_path h e hz hk hb p⟩,
      fun a' p hp => small_forward_slice_alternative h e hz hk hb p hp⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the same cubic slices and forward line,
with all additional source exclusions retained in the cubic branch. -/
theorem rankTwo_or_cubic_eligible_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ a a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a a',
        2 ≤ (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) ∧
        ∃ (c : Vertex Rg) (w : (cosetGraph Rg).Walk c a),
          color Rg c = false ∧ w.length = 2 ∧
          w.length = (cosetGraph Rg).dist c a ∧
          w.getVert 1 = p.walk.getVert 1 ∧
          2 ≤ (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        let c := p.walk.getVert 2
        let F := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
        U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∨
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
          Nat.card (⁅U Rg c,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅U Rg c,F⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          ¬ ⁅U Rg c,F⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) :=
  (coreExhaustion_or_cubic_eligible_slices h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
