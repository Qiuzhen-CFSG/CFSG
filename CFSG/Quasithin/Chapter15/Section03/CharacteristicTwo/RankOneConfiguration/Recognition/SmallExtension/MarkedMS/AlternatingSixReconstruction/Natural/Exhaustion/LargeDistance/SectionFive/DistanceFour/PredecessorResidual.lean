module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PredecessorSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCoreSaturation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# Full midpoint-core commutators and residual transport at distance four

On a critical path a--c--z of length four, the midpoint two-core Q_c
fixes both endpoints. It therefore normalizes the moving critical kernel
F = U_z intersect Q_a. The endpoint's full moving cover has order at most
thirty-two, and F is proper because the last-edge central attachment lies
in Q_a. Thus |F| <= 16. A nontrivial normal subgroup of a finite two-group
strictly decreases under commutation, giving |[F,Q_c]| <= 8. The entire
critical kernel K = Z_z intersect Q_a has the same commutator: its extra
last-edge seed centralizes Q_c.

This bound holds on every critical path, for every radical image and both
moving covers, without a small-slice or small-image assumption. If the
predecessor moving slice has index at most two, it identifies K with
Z_z intersect B_c. The residual fixes K modulo Z_c, hence normalizes
[K,Q_c]. Its order at most eight and the original perfect A6 component
force residual fixedness. Consequently every element k of that residual
preserves [K,D] while replacing D by its conjugate, for arbitrary D <= Q_c.

The final application constructs the same residual element carrying the
last edge to the first edge, and retains its inverse-conjugation formula
on each full seed in Q_c, for both the full and moving critical kernels.
This supplies the residual-compatibility step
used in MS93 (5.8) on the literal natural replacement. The existence of
the required initial selected path and the small-slice alternative still
require proof; this is not the unconditional distance-four exclusion.
The independently owned selected terminal argument is not used here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.8), printed pp.919--920, and its use in (5.12), p.924.
Internal imports reuse the fixed-modulo-seed commutator identities and
the actual residual neighbor transporter without changing their APIs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u

private theorem small_normal_two_commutator
    {H : Type*} [Group H] [Finite H] (hp : IsPGroup 2 H)
    (F : Subgroup H) [F.Normal] (hcard : Nat.card F ≤ 16) :
    Nat.card (⁅F,(⊤ : Subgroup H)⁆ : Subgroup H) ≤ 8 := by
  by_cases hzero : F = ⊥
  · simp [hzero]
  have hlt : Nat.card (⁅F,(⊤ : Subgroup H)⁆ : Subgroup H) < Nat.card F := by
    by_contra! hge
    have heq := eq_of_le_of_card_ge (commutator_le_left F (⊤ : Subgroup H)) hge
    exact hzero (bot_unique (le_normal_of_quotient_isPGroup_of_eq_commutator
      F ⊤ ⊥ (hp.to_quotient ⊥) heq))
  obtain ⟨n,hn⟩ := (hp.to_subgroup (⁅F,(⊤ : Subgroup H)⁆ : Subgroup H)).exists_card_eq
  have hn4 : n < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by
    rw [←hn]
    exact lt_of_lt_of_le hlt hcard)
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 3)

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem moving_card_le_thirty_two
    (hc : DistanceTwo.CentralLayer d) {a : Vertex d.radical}
    (ha : color d.radical a = false) : Nat.card (U d.radical a) ≤ 32 := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have he : act d.radical g (alpha d.radical) = mVertex d.radical g := by
    simp only [alpha,act_mVertex,one_mul]
  rw [←he,U_act,card_map_of_injective (MulAut.conj g⁻¹).injective]
  rcases graph_U_card s hc with hh | hh <;> omega

include s in
/-- At distance four, the entire reverse critical kernel has commutator of
order at most eight with the whole midpoint two-core, for both covers and
all critical images. No slice or radical-image assumption is used. -/
theorem critical_midpoint_whole_core_card
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    Nat.card (⁅Z d.radical z ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let F := U d.radical z ⊓ Q d.radical a
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hcz : (cosetGraph d.radical).dist c z = 2 := by
    rw [p.dist_end,hl]
  have hzc : (cosetGraph d.radical).dist z c = 2 := by rw [SimpleGraph.dist_comm,hcz]
  have hac : (cosetGraph d.radical).dist a c = 2 := p.dist_start (by omega)
  have hct : Adjacent d.radical c t :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent d.radical z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hFQ : F ≤ Q d.radical c :=
    (inf_le_left.trans (DistanceEight.U_le_Z d.radical z)).trans
      (Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color) (by
        rw [(replacementGeometry h d).distance_constant z p.end_color]
        change (cosetGraph d.radical).dist z c < replacementDistance h d
        omega))
  have hQGz : Q d.radical c ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical c z hcol hcz
  have hQGa : Q d.radical c ≤ stabilizer d.radical a :=
    Q_le_stabilizer_of_dist_two d.radical c a hcol (by rw [SimpleGraph.dist_comm,hac])
  have hFN : Q d.radical c ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQGz.trans (U_normalized z))
      (hQGa.trans (Q_normalized d.radical a))).trans inf_normalizer_le_normalizer_inf
  have hZcQa : Z d.radical c ≤ Q d.radical a :=
    Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol) (by
      rw [(replacementGeometry h d).distance_constant c hcol,SimpleGraph.dist_comm,hac]
      exact show 2 < replacementDistance h d from hb2)
  have hZtQa : Z d.radical t ≤ Q d.radical a :=
    (adjacent_Z_le d.radical hcol hct).trans hZcQa
  have hUne : ¬ U d.radical z ≤ Q d.radical a := by
    intro hU
    apply (critical_reverse_pair s hc p).2
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color hzt]
    exact sup_le hU hZtQa
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U d.radical z from inf_le_left))
    (inclusion_injective _)
  have hidx : 2 ≤ F.relIndex (U d.radical z) := by
    have hp : 0 < F.relIndex (U d.radical z) := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : F.relIndex (U d.radical z) ≠ 1 := by
      intro he
      exact hUne ((relIndex_eq_one.mp he).trans inf_le_right)
    omega
  have hproduct := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) F
    (U d.radical z) bot_le inf_le_left
  simp only [relIndex_bot_left] at hproduct
  have hUcard := moving_card_le_thirty_two s hc p.end_color
  have hFcard : Nat.card F ≤ 16 := by nlinarith
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical c) := Finite.of_injective
    (inclusion (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1))
      (inclusion_injective _)
  let F₀ := F.subgroupOf (Q d.radical c)
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer hFN
  have hmF : F₀.map (Q d.radical c).subtype = F := map_subgroupOf_eq_of_le hFQ
  have hmQ : (⊤ : Subgroup (Q d.radical c)).map (Q d.radical c).subtype = Q d.radical c := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hpQ := Q_isPGroup d.radical (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) c hcol
  have hbound := small_normal_two_commutator hpQ F₀ (by
    rw [←card_map_of_injective (Q d.radical c).subtype_injective,hmF]
    exact hFcard)
  rw [←card_map_of_injective (Q d.radical c).subtype_injective,
    map_commutator,hmF,hmQ] at hbound
  have hsame := (critical_kernel_predecessor_moving s hc hb2 p).2.2
    (Q d.radical c) (by simp only [hl]; exact le_rfl)
  rw [hsame]
  exact hbound


include s in
/-- The actual small predecessor slice makes the whole-core commutator
fixed by the midpoint residual. Its order need not be two. -/
theorem small_predecessor_whole_core_fixed
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    ⁅Z d.radical z ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let K := Z d.radical z ⊓ Q d.radical a
  let N := ⁅K,Q d.radical c⁆
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  simp only [hl] at hs
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hs.1.ge.trans inf_le_right
  have hVG := (V_le_Q d.radical hcol hb2).trans
    (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hKQ : K ≤ Q d.radical c := by
    intro k hk
    exact V_le_Q d.radical hcol hb2 (((mem_B_iff d.radical c _ hVG k).mp (hKB hk)).1)
  have hNQ : N ≤ Q d.radical c := (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hLK : ⁅Ltilde d.radical c,K⁆ ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol))
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff d.radical c _ hVG k).mp (hKB hk)).2 l hl
  have hLN : Ltilde d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    fixed_mod_seed_normalizes_commutator K (Q d.radical c) (Ltilde d.radical c)
      (hKQ.trans (Q d.radical c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized d.radical c)) hLK
  exact small_core_residual_fixed_knownSimple (h := h) (e := e) hcol N hNQ hLN
    (critical_midpoint_whole_core_card s hc hb p)

include s in
/-- Every midpoint residual element preserves the full critical-kernel
commutator with an arbitrary subgroup of the whole midpoint core. -/
theorem small_predecessor_whole_core_transport
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2)
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ Q d.radical (p.walk.getVert 2))
    (k : FreeAmalgam d.radical) (hk : k ∈ Ltilde d.radical (p.walk.getVert 2)) :
    ⁅Z d.radical z ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical z ⊓ Q d.radical a,D⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  simp only [hl] at hs
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  exact slice_commutator_transport_of_fixed (h := h) hb2 hcol _
    (hs.1.ge.trans inf_le_right)
    ((small_predecessor_whole_core_fixed s hc hb p hslice).trans inf_le_right) D hD k hk

include e hz hn in
/-- The original natural replacement constructs the residual rotation and
the exact full-seed commutator transport required by source (5.8).
Only the predecessor slice bound remains explicit. -/
theorem small_predecessor_residual_shift_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hslice : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2) :
    let K := Z d.radical z ⊓ Q d.radical a
    let c := p.walk.getVert 2
    Z d.radical z ⊓ B d.radical c ((replacementGeometry h d).Z_normal _) = K ∧
      Nat.card (⁅K,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 8 ∧
      ⁅K,Q d.radical c⁆ ≤ fixedCore d.radical c ∧
      ∃ k ∈ Ltilde d.radical c,
        act d.radical k (p.walk.getVert 3) = p.walk.getVert 1 ∧
        (∀ delta : Vertex d.radical, Z d.radical delta ≤ Q d.radical c →
          ⁅K,Z d.radical (act d.radical k⁻¹ delta)⁆ = ⁅K,Z d.radical delta⁆ ∧
          ⁅U d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ delta)⁆ =
            ⁅U d.radical z ⊓ Q d.radical a,Z d.radical delta⁆) ∧
        (∀ i, (p.act k).walk.getVert i = act d.radical k (p.walk.getVert i)) := by
  dsimp only
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs := critical_predecessor_slice_eq_kernel s hc hb2 p (by simpa only [hl] using hslice)
  simp only [hl] at hs
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hcv : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct hcv
  refine ⟨hs.1,critical_midpoint_whole_core_card s hc hb p,
    small_predecessor_whole_core_fixed s hc hb p hslice,k,hk,hkt,?_,?_⟩
  · intro delta hD
    have hmove : ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ delta)⁆ =
        ⁅Z d.radical z ⊓ Q d.radical a,Z d.radical delta⁆ := by
      rw [Z_act,inv_inv]
      exact small_predecessor_whole_core_transport s hc hb p hslice _ hD k hk
    refine ⟨hmove,?_⟩
    have hDk : Z d.radical (act d.radical k⁻¹ delta) ≤ Q d.radical (p.walk.getVert 2) := by
      rw [Z_act,inv_inv]
      exact (map_mono hD).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized d.radical _) (Ltilde_le_stabilizer _ hk)))
    have hnew := (critical_kernel_predecessor_moving s hc hb2 p).2.2
      (Z d.radical (act d.radical k⁻¹ delta)) (by simpa only [hl] using hDk)
    have hold := (critical_kernel_predecessor_moving s hc hb2 p).2.2
      (Z d.radical delta) (by simpa only [hl] using hD)
    rwa [hnew,hold] at hmove
  · intro i
    exact actWalk_getVert d.radical k p.walk i

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
