module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPathExtension

/-!
# Forward slice kernels and large-image shifts in the cubic cover

The full forward-slice kernel fixes the moving cover exactly when that
cover lies in the starting Baumann slice, for either critical image size.
In the zero case its normal orbit span centralizes the predecessor seed
and the full reverse kernel. The predecessor core places that span in the
endpoint stabilizer, where the general critical-kernel theorem puts it in
the Baumann slice. Thus every eligible small slice has a noncentral line
of order two at the second vertex.

For a large critical image, the actual forward path and the marked cover
construct the shifted endpoint and residual conjugator used in MS93 (5.9).
This construction does not assume point-core equality. In the full
point-core branch, a small forward slice also yields a small critical
pair on the reverse extended prefix. Transporting that pair to the base
gives rank-one transpositions on the entire seed, even when the original
pair has large image. Above distance four the original pair must have
large image, by the already proved strict small-image bound.

The whole-core and literal C.1.32 consumers retain both covers and the
cubic kernel. This does not yet exclude the large-image shifted
configuration or establish centrality of its line at the shifted center.
Radical-image identification, the remaining strict slices, R4/R6,
exact-four and terminal exclusions, natural exhaustion and both final
reconstruction outcomes remain required.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the shifted-path construction in (5.9), pp.920--921.
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
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
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
/-- The full forward kernel has zero moving-cover commutator exactly for a
contained cover. The general critical-kernel theorem removes the former
small-critical-image premise. -/
theorem forward_kernel_eq_bot_iff_slice
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    :
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
    have hPendpoint : P ≤ stabilizer Rg a' := hPpre.trans
      (Q_le_stabilizer_of_dist_le_two _ _ hpre p.end_color (by
        rw [p.dist_end]
        have he : p.walk.length = sourceDistance h := p.length_eq_b
        change p.walk.length-(p.walk.length-2) ≤ 2
        omega))
    exact (DistanceEight.U_le_Z Rg c).trans ((Z_le_localZSpan Rg _ _).trans
      (critical_kernel_normal_radius_le_slice h e hz hk hb p P hPV
        (localZSpan_normalized Rg _ _) hPendpoint
        (hPC.trans (centralizer_le (show Z Rg a' ⊓ Q Rg (alpha Rg) ≤ T from
          le_sup_right.trans hinner)))))
  · intro hslice
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    change T ≤ centralizer (U Rg c : Set (FreeAmalgam Rg))
    intro x hx y hy
    exact hx.2 y ⟨hy,hslice hy⟩


include h e hz hk in
/-- Every eligible forward slice of index at most two has a nonzero line
in the common edge seed, noncentral at the second vertex. Both critical
image sizes and both full moving covers are allowed. -/
theorem forward_slice_noncentral_line
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
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
    ((forward_kernel_eq_bot_iff_slice h e hz hk hb p).mp he)
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
/-- A large critical image and an eligible small forward slice construct the
literal shifted endpoint and residual conjugator of MS93 (5.9), (**).
The full point-core image is not needed for this construction. -/
theorem large_image_small_slice_shift
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)))
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ∃ s : SmallSliceShift h p,
      Nat.card s.line = 2 ∧
      ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hlast : Adjacent Rg a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨d,hdt,k,hkG,q,hq,hover⟩ := large_critical_forward_path h e hz hk p hlast hlarge
  have hline := forward_slice_noncentral_line h e hz hk hb p hslice heligible
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator h e hz hk q
    (forwardSliceLine h (alpha Rg) c) hHU hline.1 hline.2.2
  let s : SmallSliceShift h p := ⟨act Rg k d,q,hover,g,hg,hgen,hmove⟩
  refine ⟨s,?_,?_⟩
  · exact (card_map_of_injective (MulAut.conj g).injective).trans hline.1
  · intro hc
    have he : Z Rg s.endpoint ≤ stabilizer Rg (p.walk.getVert 2) :=
      critical_Z_le_stabilizer Rg (sourceGeometry h) _ q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]
            exact sourceDistance_pos h) q.critical
    exact s.moves (hc.trans (centralizer_le he))

include h e hz hk in
/-- A small forward slice gives a small critical pair, even if its original
critical pair has large image. Reverse the extended prefix and use the
strict reciprocal bound, then transport that actual pair to the base. -/
theorem full_point_small_slice_critical_witness
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hslice : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ∃ b, ∃ _q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b,
      (Q Rg b).relIndex (Z Rg (alpha Rg)) = 2 := by
  obtain ⟨d,r,hr1,hr2⟩ := full_point_critical_reverse_prefix h e hz hk hb u hfull p
  have hsmall : (Q Rg d).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    by_contra! hlarge
    have hi := (large_critical_slices_gt_two h e hz hk hb r hlarge).2
    rw [hr2] at hi
    omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg r.start_color
  have hbase : act Rg g⁻¹ (p.walk.getVert 2) = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hex : Nonempty (CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (p.walk.getVert 2)) (act Rg g⁻¹ d)) := ⟨r.act g⁻¹⟩
  rw [hbase] at hex
  obtain ⟨q⟩ := hex
  have hsmall₀ : (Q Rg (act Rg g⁻¹ d)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  exact ⟨act Rg g⁻¹ d,q,(small_critical_indices h e hz hk q hsmall₀).1⟩

include h e hz hk in
/-- Every transposition has rank one on the entire seed whenever a forward
slice is small in the full point-core branch. The witness above supplies
the small critical pair; the original pair need not have small image. -/
theorem full_point_small_slice_seed_transvections
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hslice : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) (i j : Fin 6) (hij : i ≠ j) :
    letI := seed_elementary (h := h)
    Module.finrank (ZMod 2)
      (LinearMap.range (seedAction h e hz hk (Equiv.swap i j)-LinearMap.id)) = 1 := by
  let := seed_elementary (h := h)
  obtain ⟨b,q,hq⟩ := full_point_small_slice_critical_witness h e hz hk hb u hfull p hslice
  exact seed_transposition_rank_one h e hz hk q (by omega) i j hij

include h e hz hk in
/-- Above distance four, a small forward slice in the full point-core branch
forces a large critical image and has an actual shifted-path witness.
The small-image alternative is excluded by the strict-slice theorem. -/
theorem full_point_small_slice_large_shift
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) ∧
      ∃ s : SmallSliceShift h p,
        Nat.card s.line = 2 ∧
        ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) := by
    by_contra! hs
    exact (Nat.not_le_of_gt
      (full_point_small_forward_slice_strict h e hz hk hb u hfull p hs)) hslice
  exact ⟨hlarge,large_image_small_slice_shift h e hz hk (by omega) p hlarge hslice
    (full_point_critical_forward_eligible h e hz hk (by omega) u hfull p)⟩

include h e hz hk in
/-- The large-image slice cases on the actual graph: a strict slice, a
contained cover, or the shifted noncentral commutator line. -/
theorem large_image_forward_slice_alternative
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
      ∃ s : SmallSliceShift h p,
        Nat.card s.line = 2 ∧
        ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  by_cases hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))
  · exact Or.inl hs
  · by_cases hc : U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (large_image_small_slice_shift h e hz hk hb p hlarge
        (Nat.le_of_not_gt hs) hc))

omit hk in
include h e hz in
/-- Whole-core consumer of the new large-image shifted-line construction.
The literal point-core branch also excludes contained and small-image
slice failures, leaving the large shifted witness as the only obstruction
to a strict forward slice above distance four. -/
theorem coreExhaustion_or_cubic_large_slice_shifts :
    letI := seed_elementary (h := h)
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
        4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) →
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∨
          U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
          ∃ s : SmallSliceShift h p,
            Nat.card s.line = 2 ∧
            ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (∀ i j : Fin 6, i ≠ j → Module.finrank (ZMod 2)
            (LinearMap.range (seedAction h e hz hk (Equiv.swap i j)-LinearMap.id)) = 1) ∧
          4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) ∧
            ∃ s : SmallSliceShift h p,
              Nat.card s.line = 2 ∧
              ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) := by
  let := seed_elementary (h := h)
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun _ p hp => large_image_forward_slice_alternative h e hz hk hb p hp,
      fun u hu hb4 _ p hp =>
        ⟨full_point_small_slice_seed_transvections h e hz hk hb u hu p hp,
          full_point_small_slice_large_shift h e hz hk hb4 u hu p hp⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the large-image shifted line, retaining
radical-image identification, terminal exclusion and full reconstruction. -/
theorem rankTwo_or_cubic_large_slice_shifts :
    letI := seed_elementary (h := h)
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
        4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) →
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∨
          U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ∨
          ∃ s : SmallSliceShift h p,
            Nat.card s.line = 2 ∧
            ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (∀ i j : Fin 6, i ≠ j → Module.finrank (ZMod 2)
            (LinearMap.range (seedAction h e hz hk (Equiv.swap i j)-LinearMap.id)) = 1) ∧
          4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) ∧
            ∃ s : SmallSliceShift h p,
              Nat.card s.line = 2 ∧
              ¬ s.line ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :=
  (coreExhaustion_or_cubic_large_slice_shifts h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
