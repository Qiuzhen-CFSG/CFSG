module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardSlices

/-!
# The actual cubic residual-shifted critical path

An eligible backward seed in the predecessor core has a nonzero commutator
with the reverse critical kernel. When that kernel lies in the predecessor
Baumann slice, a residual element preserves this commutator while moving the
last edge to the preceding edge. This constructs a new critical walk with all
its overlap vertices identified. A small image would identify the full
endpoint displacement with the same nonzero line, contradicting backward
rigidity. The new image has order at least four, its radius index is at least
eight, and that radius escapes its own second predecessor core.

In the full point-core branch, failure of the original radius escape
constructs the eligible backward seed and generating edge. The actual
residual factorization selects the transporter. The whole-core and literal
C.1.32 applications retain the predecessor-slice alternative, both cover
orders and E/Q of order three.

This does not prove (5.8), (5.11), or (5.12) unconditionally. Predecessor-slice
placement, the other edge-image choices, strict slices, R4/R6, and both terminal
exclusions remain with qt-e-ms-small-a6-reconstruction. Independent natural
exhaustion remains with qt-e-ms-small-a6-exhaustion-large-distance.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), p.920.
Adapts Natural.Exhaustion.LargeDistance.SectionFive.BackwardNonzero to the
original cubic action and its full central covers.
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
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- The prescribed residual shift constructs an actual critical path.
The shifted image is large, and every overlapping vertex and the transported
nonzero line use that same element. -/
theorem eligible_backward_residual_critical_path
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hslice : U Rg a' ⊓ Q Rg (alpha Rg) ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _))
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hkt : act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k a'),
      4 ≤ (Q Rg (act Rg k a')).relIndex (Z Rg c) ∧
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
        ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
  have hline := small_eligible_backward_failure_line h e hz hk hb u hR p hsmall hat hct hgen hel hbad
  have hne := eligible_backward_kernel_ne_bot h e hz hk hb p hsmall hat hct hgen hel hbad
  have hfullslice := (critical_kernel_predecessor_moving h e hz hb p).2.1.mpr hslice
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have htransport :
      ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
        ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
    rw [Z_act,inv_inv]
    exact small_slice_commutator_residual_transport (h := h) hb hcol _ hfullslice
      (small_critical_kernel_predecessor_card h e hz hk hb u hR p hsmall) _ hbad k hkm
  have hescape : ¬ Z Rg c ≤ Q Rg (act Rg k a') := by
    intro hh
    have hm : Z Rg (act Rg k⁻¹ c) ≤ Q Rg a' := by
      calc
        _ = (Z Rg c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q Rg (act Rg k a')).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q Rg (act Rg k⁻¹ (act Rg k a')) := by
          simpa only [inv_inv] using (Q_act Rg k⁻¹ (act Rg k a')).symm
        _ = Q Rg a' := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q Rg a' p.end_color))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcfalse : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hlast : Adjacent Rg (p.walk.getVert (p.walk.length-1)) a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hend : (cosetGraph Rg).Adj (p.walk.getVert (p.walk.length-3)) (act Rg k a') := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr
      ((adjacent_act_iff Rg k _ _).mpr hlast)
  let w₀ : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le Rg c ((sourceGeometry h).exists_critical c hcfalse) hescape
  rw [(sourceGeometry h).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph Rg).dist c (act Rg k a') = sourceDistance h := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath Rg (sourceGeometry h) c (act Rg k a') :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(sourceGeometry h).distance_constant c hcfalse]
      exact hdist⟩
  have hlarge : 4 ≤ (Q Rg (act Rg k a')).relIndex (Z Rg c) := by
    by_contra! hqsmall
    let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        c q.start_color (by
          rw [(sourceGeometry h).distance_constant c q.start_color]
          exact sourceDistance_pos h)
        (act Rg k a') q.end_color q.critical)
    have hqrsmall : (Q Rg c).relIndex (Z Rg (act Rg k a')) < 4 := by
      rw [(small_critical_indices h e hz hk q hqsmall).2]
      decide
    let D := ⁅U Rg a',Z Rg (act Rg k⁻¹ c)⁆
    have hcardD : Nat.card D = 2 := by
      dsimp only [D]
      rw [←card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
        (MulAut.conj k⁻¹).injective,map_commutator]
      have hZ : (Z Rg (act Rg k⁻¹ c)).map (MulAut.conj k⁻¹).toMonoidHom =
          Z Rg c := by
        rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
      rw [←U_act,hZ,small_critical_moving_commutator_eq h e hz hk qr hqrsmall]
      exact small_critical_commutator_card h e hz hk qr hqrsmall
    let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; decide)
    have hkQ : (Q Rg (p.walk.getVert (p.walk.length-2))).map
        (MulAut.conj k).toMonoidHom = Q Rg (p.walk.getVert (p.walk.length-2)) :=
      mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg _)
        (Ltilde_le_stabilizer _ hkm))
    have hDk : Z Rg (act Rg k⁻¹ c) ≤
        Q Rg (p.walk.getVert (p.walk.length-2)) := by
      rw [Z_act,inv_inv]
      exact (map_mono hbad).trans_eq hkQ
    have hle : ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤ D := by
      rw [←htransport,(critical_kernel_predecessor_moving h e hz hb p).2.2 _ hDk]
      exact commutator_mono inf_le_left le_rfl
    have heq : ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ = D :=
      eq_of_le_of_card_ge hle (by rw [hline.2.2.1,hcardD])
    have hdisp := critical_kernel_residual_displacement_ne h e hz hk hb u hR p hsmall
      hfullslice (Z Rg c) hbad hne k hkm
    apply hdisp
    simpa only [D,Z_act,inv_inv] using heq.symm
  refine ⟨q,hlarge,?_,?_,htransport⟩
  · change (w₀.append w₁).getVert 1 = t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2) = p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i = p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]

include h in
private theorem residual_neighbor_transporter
    {c t v : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t) (hcv : Adjacent Rg c v) :
    ∃ k ∈ Ltilde Rg c, act Rg k t = v := by
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hcol
    · exact hct
  have hn : Q Rg t ≤ normalizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer Rg c :=
      (stabilizer Rg c).inv_mem (hx.2 _ (adjacent_symm Rg hct))
    have hh := Ltilde_act Rg x⁻¹ c
    rw [inv_inv,show act Rg x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg c hct hcv
  have hprod : g ∈ (Q Rg t : Set (FreeAmalgam Rg)) *
      (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q Rg t) (Ltilde Rg c),hgen]
    exact hg
  obtain ⟨q,hq,k,hkm,rfl⟩ := hprod
  refine ⟨k,hkm,?_⟩
  have hqt : act Rg q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

include h e hz hk in
/-- Failure of radius escape in the full point-core branch constructs an
actual residual-shifted critical walk with large image. The predecessor
slice is still an explicit premise, and both full covers are retained. -/
theorem radius_failure_residual_critical_shift
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hslice : U Rg a' ⊓ Q Rg (alpha Rg) ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)) :
    ∃ t c k, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) ∧
      act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k a'),
        4 ≤ (Q Rg (act Rg k a')).relIndex (Z Rg c) ∧
        8 ≤ (Q Rg (act Rg k a')).relIndex (V Rg c) ∧
        (¬ V Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) ∧
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
        ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
          ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
  have hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 := by
    by_contra! hh
    exact large_critical_radius_escape h e hz hk p hh hbad
  obtain ⟨t,hat,hgen⟩ := small_image_full_point_generating_neighbor h e hz hk u hfull p hsmall
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb rfl hat
  have hcQ : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))).trans hbad
  have hline := small_eligible_backward_failure_line h e hz hk hb u hfull.le
    p hsmall hat hct hgen hel hcQ
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct' : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcv : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct' hcv
  obtain ⟨q,hlarge,hfirst,hover,htransport⟩ := eligible_backward_residual_critical_path
    h e hz hk hb u hfull.le p hsmall hat hct hgen hel hcQ hslice k hkm hkt
  have hradius := critical_radius_index_two_mul_seed_le h e hz hk hb q
  exact ⟨t,c,k,hat,hct,hkm,hkt,q,hlarge,by omega,
    large_critical_radius_escape h e hz hk q hlarge,hfirst,hover,hline.2.2.1,htransport⟩
omit hk in
include h e hz in
/-- Whole-core application of the actual residual shift. The two remaining
alternatives distinguish radius escape from failure of predecessor-slice
placement; neither is asserted without proof. -/
theorem coreExhaustion_or_cubic_residual_shift :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∨
          (¬ U Rg a' ⊓ Q Rg (alpha Rg) ≤
            B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)) ∨
          ∃ t c k, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
            k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) ∧
            act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k a'),
              4 ≤ (Q Rg (act Rg k a')).relIndex (Z Rg c) ∧
              8 ≤ (Q Rg (act Rg k a')).relIndex (V Rg c) ∧
              (¬ V Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) ∧
              q.walk.getVert 1 = t ∧
              (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
              Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
                ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p
    by_cases hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))
    · by_cases hslice : U Rg a' ⊓ Q Rg (alpha Rg) ≤
          B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)
      · exact Or.inr (Or.inr (radius_failure_residual_critical_shift h e hz hk hb u hfull p hbad hslice))
      · exact Or.inr (Or.inl hslice)
    · exact Or.inl hbad

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the cubic kernel, both full covers
and every unresolved slice or edge-image branch. -/
theorem rankTwo_or_cubic_residual_shift :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∨
          (¬ U Rg a' ⊓ Q Rg (alpha Rg) ≤
            B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)) ∨
          ∃ t c k, Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
            k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) ∧
            act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k a'),
              4 ≤ (Q Rg (act Rg k a')).relIndex (Z Rg c) ∧
              8 ≤ (Q Rg (act Rg k a')).relIndex (V Rg c) ∧
              (¬ V Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) ∧
              q.walk.getVert 1 = t ∧
              (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
              Nat.card (⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
                ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Z Rg c⁆) :=
  (coreExhaustion_or_cubic_residual_shift h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
