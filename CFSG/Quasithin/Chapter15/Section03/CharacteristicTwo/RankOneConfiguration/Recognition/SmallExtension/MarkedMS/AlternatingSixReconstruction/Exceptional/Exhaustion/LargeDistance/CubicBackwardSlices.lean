module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardFixedCore

/-!
# Backward eligibility and uniform slices on the cubic graph

An eligible backward seed in the predecessor core has a nonzero reverse-
kernel commutator: vanishing would make its join with the starting seed
invariant under a generating edge and the critical actor, placing it in
the Baumann slice. A central commutator likewise forces a two-actor into
Q across the retained cubic kernel. The small critical-image bound and
point-core containment therefore make the backward commutator a noncentral
line of order two, and force the eligible slice index to be two.

Failure of radius escape excludes the large critical-image branch. In
the full point-core branch, the original cubic marking constructs the
generating edge. A larger slice could be transported to that edge and
would contradict the proved small-image backward step. Vertex transitivity
then bounds every two-edge slice by two. Eligibility constructs the
noncentral backward line without assuming nonvanishing. The full and moving
reverse kernels have the same predecessor-core commutator, so the source
moving-kernel slice premise supplies its residual transport while retaining
the entire cover and central attachment.

The whole-core and literal C.1.32 applications retain point-core equality,
the moving-kernel slice premise, both cover orders and E/Q of order three.
Strict slice selection, the other edge-image branches, R4/R6 and the
terminal exclusions (5.11)--(5.12) remain with
qt-e-ms-small-a6-reconstruction. Independent natural exhaustion remains
with qt-e-ms-small-a6-exhaustion-large-distance.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.9), pp.919--922.
Adapts the eligibility and uniform-slice arguments of
Natural.Exhaustion.LargeDistance.SectionFive.BackwardNonzero to the
original cubic graph and its larger seed centralizer.
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
include h e hz hk in
/-- An eligible backward seed cannot fix the full reverse kernel while
remaining in the predecessor core. This does not require point-core image
containment or a bound on the eligible slice. -/
theorem eligible_backward_kernel_ne_bot
    (hb : 2 < sourceDistance h)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
  intro hzero
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h1 : (cosetGraph Rg).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h2 : (cosetGraph Rg).dist t (alpha Rg) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
      (u := c) (v := t) (w := alpha Rg)
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  have hfix : Z Rg c ≤ centralizer
      (Z Rg a' ⊓ Q Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hmove := small_critical_predecessor_commutator h e hz hk hb p hsmall
    (Z Rg c) hbad hfix
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hYmove : ⁅Y,Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg a')
      (Z Rg (alpha Rg)) (Z_normalized Rg _)
      (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hmove
      (le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
          (sourceDistance_pos h) p.critical).trans (Z_normalized Rg _)))
  have hYn : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf
        ((show Q Rg t ≤ stabilizer Rg c from
          fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
        ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
          fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  exact hel ((DistanceEight.U_le_Z Rg c).trans
    (le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
      (sup_le hZV (Z_le_VBall Rg _ 2)) hYn hYmove)))

include h e hz hk in
/-- The backward-kernel commutator forced by eligibility is noncentral at
the selected backward vertex. The full moving cover detects any central
commutator, including in the order-32 case. -/
theorem eligible_backward_kernel_not_central
    (hb : 2 < sourceDistance h)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ¬ ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  intro hcentral
  let K := Z Rg a' ⊓ Q Rg (alpha Rg)
  have hne := eligible_backward_kernel_ne_bot h e hz hk hb p hsmall hat hct hgen hel hbad
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hcol : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hKG : K ≤ stabilizer Rg c :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk c hcol
  let A := K.comap i
  have hmA : A.map i = K := map_comap_eq_self (hKG.trans_eq hir.symm)
  have hcA : ⁅W,A⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmA,hiU,commutator_comm] at hh
      exact commutator_mono le_rfl (DistanceEight.U_le_Z Rg c) hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hKQ := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk A
    (((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha Rg) rfl).to_le (show K ≤ Q Rg (alpha Rg) from inf_le_right)).comap_of_injective i hi) hcA)
  rw [hmA,hiQ] at hKQ
  apply hne
  rw [commutator_comm]
  exact le_bot_iff.mp ((commutator_mono le_rfl hKQ).trans_eq
    (Z_centralizes_Q Rg c hcol))

include h e hz hk in
/-- Failure of an eligible backward escape forces index two and a nonzero
order-two reverse-kernel commutator. The order-32 cover is retained. -/
theorem small_eligible_backward_failure_line
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    (Q Rg a').relIndex (Z Rg (alpha Rg)) = 2 ∧
      (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg c) = 2 ∧
      Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ :
        Subgroup (FreeAmalgam Rg)) = 2 ∧
      ¬ ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  have hupper : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) ≤ 2 := by
    by_contra! hh
    exact small_image_backward_not_le h e hz hk hb u hR p hsmall hat hct hgen hh hbad
  have hne := eligible_backward_kernel_ne_bot h e hz hk hb p hsmall hat hct hgen hel hbad
  have hcard := small_critical_kernel_predecessor_card h e hz hk hb u hR p hsmall
  let K := Z Rg a' ⊓ Q Rg (alpha Rg)
  let H := ⁅K,Z Rg c⁆
  have hKQ : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < sourceDistance h
    omega
  let := finite_stabilizer Rg (p.walk.getVert (p.walk.length-2))
  let : Finite (⁅K,Q Rg (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKQ le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  have hle : H ≤ ⁅K,Q Rg (p.walk.getVert (p.walk.length-2))⁆ := commutator_mono le_rfl hbad
  let : Finite H := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hHupper : Nat.card H ≤ 2 := (card_le_of_le hle).trans hcard
  have hHlower : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hpos : 0 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hindexne : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
  refine ⟨(small_critical_indices h e hz hk p hsmall).1,by omega,by change Nat.card H = 2; omega,?_⟩
  exact eligible_backward_kernel_not_central h e hz hk hb p hsmall hat hct hgen hel hbad

include h e hz hk in
/-- Failure of radius escape bounds every two-edge Baumann slice by two.
A hypothetical larger slice can be moved to the generating edge, where
the proved backward step contradicts the original radius containment.
Vertex transitivity then gives the bound at every component vertex. -/
theorem radius_failure_all_slice_indices_le_two
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' t₀ : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hat₀ : Adjacent Rg (alpha Rg) t₀)
    (hgen : Q Rg t₀ ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
  have hbase {c t : Vertex Rg}
      (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t) :
      (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg c) ≤ 2 := by
    by_contra! hindex
    obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat hat₀
    have hcgt : Adjacent Rg (act Rg g c) t₀ := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g c t).mpr hct
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
    have hindexg : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (act Rg g c)) := by
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hindex
    have hdist : (cosetGraph Rg).dist (act Rg g c) (alpha Rg) ≤ 2 := by
      have h1 : (cosetGraph Rg).dist (act Rg g c) t₀ = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hcgt)
      have h2 : (cosetGraph Rg).dist t₀ (alpha Rg) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat₀))
      simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
        (u := act Rg g c) (v := t₀) (w := alpha Rg)
    have hcQ : Z Rg (act Rg g c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) :=
      ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)).trans hbad
    by_cases hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))
    · exact large_critical_radius_escape h e hz hk p hlarge hbad
    · exact small_image_backward_not_le h e hz hk hb u hR p (Nat.lt_of_not_ge hlarge)
        hat₀ hcgt hgen hindexg hcQ
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg ha
  have hga : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hgat : Adjacent Rg (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff Rg g⁻¹ a t).mpr hat
  have hh := hbase hgat ((adjacent_act_iff Rg g⁻¹ c t).mpr hct)
  rw [←hga,Escape.PairingControl.FirstPairing.B_act hb g⁻¹ a ha,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh


include h e hz hk in
/-- Failure of radius escape in the full point-core branch constructs a
noncentral backward line and bounds every two-edge slice. If the reverse
kernel is in the predecessor slice, its line is preserved by the same
residual transporter. That slice placement is not inferred from its index. -/
theorem radius_failure_backward_slices
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    (∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t → Adjacent Rg c t →
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
    ∃ t c, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      (Q Rg a').relIndex (Z Rg (alpha Rg)) = 2 ∧
      (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
      Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      (¬ ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) ∧
      (U Rg a' ⊓ Q Rg (alpha Rg) ≤
          B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) →
        ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
          ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
            ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆) := by
  have hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 := by
    by_contra! hlarge
    exact large_critical_radius_escape h e hz hk p hlarge hbad
  obtain ⟨t,hat,hgen⟩ := small_image_full_point_generating_neighbor h e hz hk u hfull p hsmall
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb rfl hat
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hcQ : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)).trans hbad
  have hline := small_eligible_backward_failure_line h e hz hk hb u hfull.le
    p hsmall hat hct hgen hel hcQ
  refine ⟨?_,t,c,hat,hct,hgen,hline.1,hline.2.1,hline.2.2.1,hline.2.2.2,?_⟩
  · intro a₁ c₁ t₁ ha₁ hat₁ hct₁
    exact radius_failure_all_slice_indices_le_two h e hz hk hb u hfull.le
      p hat hgen hbad ha₁ hat₁ hct₁
  · intro hslice k hkm
    have hfullslice := (critical_kernel_predecessor_moving h e hz hb p).2.1.mpr hslice
    have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
      apply (p.vertex_color (Nat.sub_le _ _)).mpr
      have he := sourceDistance_even h
      rw [Nat.even_iff] at he ⊢
      have hh : p.walk.length = sourceDistance h := p.length_eq_b
      omega
    rw [Z_act,inv_inv]
    exact small_slice_commutator_residual_transport (h := h) hb hcol _ hfullslice
      (small_critical_kernel_predecessor_card h e hz hk hb u hfull.le p hsmall)
      _ hcQ k hkm

omit hk in
include h e hz in
/-- Whole-core application: the full-point branch either has the required
radius escape or supplies uniform upper slices and an actual noncentral
backward line. The predecessor-slice premise is retained for its residual
transport, and its discharge remains with this reconstruction owner. -/
theorem coreExhaustion_or_cubic_backward_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∨
          (∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t → Adjacent Rg c t →
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∃ t c, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            (Q Rg a').relIndex (Z Rg (alpha Rg)) = 2 ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
            Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            (¬ ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
              centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) ∧
            (U Rg a' ⊓ Q Rg (alpha Rg) ≤
                B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) →
              ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
                ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
                  ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p
    by_cases hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))
    · exact Or.inr (radius_failure_backward_slices h e hz hk hb u hfull p hbad)
    · exact Or.inl hbad

omit hk in
include h e hz in
/-- The literal C.1.32 consumer retains the full-point radius alternative,
both full covers, and the original cubic quotient marking. -/
theorem rankTwo_or_cubic_backward_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∨
          (∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t → Adjacent Rg c t →
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∃ t c, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            (Q Rg a').relIndex (Z Rg (alpha Rg)) = 2 ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 2 ∧
            Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            (¬ ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
              centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) ∧
            (U Rg a' ⊓ Q Rg (alpha Rg) ≤
                B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) →
              ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
                ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
                  ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆)) :=
  (coreExhaustion_or_cubic_backward_slices h e hz).imp (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
