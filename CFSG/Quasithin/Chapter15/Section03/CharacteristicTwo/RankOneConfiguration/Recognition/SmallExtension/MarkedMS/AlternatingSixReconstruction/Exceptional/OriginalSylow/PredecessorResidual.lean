module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Predecessor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicResidualShift

/-!
# Full predecessor-kernel transport without mover comparisons

For a critical path a--z, the endpoint two-core cannot lie in the core at
its second predecessor c. The two cores have equal order by conjugacy;
containment would make them equal, contradicting criticality because the
starting seed already lies in Q_c.

A small predecessor Baumann slice identifies the full reverse kernel
K = Z_z intersect Q_a with Z_z intersect B_c. Its commutator N = [K,Q_c]
is normalized by the whole predecessor stabilizer. Since N lies in Z_z,
the endpoint two-core centralizes N. The normal-over-core dichotomy and
two-perfectness now force the predecessor residual to centralize N.
Only a two-subgroup lying in the cubic kernel E is placed in Q; E/Q and
its odd order are retained. No equal-mover or small-order hypothesis is used.

Consequently residual conjugation preserves commutators with the full
kernel. A nonzero such commutator constructs a shifted critical path with
all overlapping vertices. Its image is large, or the same subgroup is the
noncentral order-two moving line at the original endpoint. The literal
OriginalSylowExceptional consumer applies both results on c.L,d.S.

These statements cover both moving covers and every original cubic radical
image, including the Borel case. The small predecessor slice and nonzero
commutator are explicit local premises. Central-generation escape, strict
forward estimates and the terminal contradiction still need to be proved;
whole-core exhaustion is not asserted here.

The private imports share the generic slice-commutator transport and path
construction within exceptional reconstruction, without importing a
plane-only conclusion into the Borel case.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), predecessor/residual comparison in (5.8), printed p.920;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R

omit hk in
include h e hz in
private theorem component_fixed_of_noncore_two_centralizer
    (N A : Subgroup M) [N.Normal] (hA : IsPGroup 2 A)
    (hAC : A ≤ centralizer (N : Set M)) (hne : ¬ A ≤ pCore 2 M) :
    N ≤ centralizer (L.subgroupOf M : Set M) := by
  let C := centralizer (N : Set M)
  have hLC : L.subgroupOf M ≤ C := by
    rcases normal_over_core_dichotomy h e (C ⊔ pCore 2 M) le_sup_right with hE | hL
    · exact (hne (two_subgroup_le_core_of_le_extensionKernel h hz A hA
        (hAC.trans (le_sup_left.trans hE)))).elim
    · apply le_normal_of_isPPerfect_of_le_sup_pGroup (L.subgroupOf M) C
        (pCore 2 M) _ pCore_isPGroup hL
      rw [←h.relative_residual]
      exact isPPerfect_pResidual 2
  exact le_centralizer_iff.mp hLC

omit hk in
include h e hz in
/-- A normal local subgroup centralized by a two-subgroup outside the local
two-core is centralized by the actual component residual. -/
theorem normal_subgroup_fixed_by_noncore_two_group
    {c : Vertex Rg} (hc : color Rg c = false)
    (N A : Subgroup (FreeAmalgam Rg)) (hNG : N ≤ stabilizer Rg c)
    (hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hAG : A ≤ stabilizer Rg c) (hA : IsPGroup 2 A)
    (hfix : N ≤ centralizer (A : Set (FreeAmalgam Rg)))
    (hne : ¬ A ≤ Q Rg c) :
    N ≤ centralizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg hc
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective Rg)
  have hact : act Rg g (alpha Rg) = c := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hir : i.range = stabilizer Rg c := by
    rw [←hact,stabilizer_act]
    change ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)).range = _
    rw [MonoidHom.range_comp]
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) (stabilizer_m_base Rg).symm
  have hiQ : (pCore 2 M).map i = Q Rg c := by
    rw [←hact,Q_act,Q_alpha Rg h.relative_radical.isPGroup
      h.relative_radical.twoCore_le,map_map]
  have hiL : (pResidual 2 M).map i = Ltilde Rg c := by
    rw [←hact,Ltilde_act,Ltilde_alpha,map_map]
  let N₀ := N.comap i
  let A₀ := A.comap i
  have hNm : N₀.map i = N := map_comap_eq_self (hNG.trans_eq hir.symm)
  have hAm : A₀.map i = A := map_comap_eq_self (hAG.trans_eq hir.symm)
  let : N₀.Normal := ⟨by
    intro z hz m
    change i (m*z*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNn (hir ▸ (show i m ∈ i.range from ⟨m,rfl⟩))) _).mp hz⟩
  have hA₀ : IsPGroup 2 A₀ := hA.comap_of_injective i hi
  have hfix₀ : A₀ ≤ centralizer (N₀ : Set M) := by
    intro a ha n hn
    apply hi
    simp only [map_mul]
    exact (hfix hn (i a) ha).symm
  have hne₀ : ¬ A₀ ≤ pCore 2 M := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hAm,hiQ] at hm
  have hfixed := component_fixed_of_noncore_two_centralizer h e hz N₀ A₀ hA₀ hfix₀ hne₀
  rw [←h.relative_residual] at hfixed
  have hh := congrArg (Subgroup.map i) (commutator_eq_bot_iff_le_centralizer.mpr hfixed)
  rw [map_commutator,hNm,hiL,Subgroup.map_bot] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh

include h in
/-- Criticality separates the endpoint two-core from its second predecessor
two-core. Equality of their orders rules out either containment. -/
theorem critical_endpoint_core_not_le_predecessor
    (hb : 2 < sourceDistance h) {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ Q Rg z ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  let c := p.walk.getVert (p.walk.length-2)
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have card_core (v : Vertex Rg) (hv : color Rg v = false) :
      Nat.card (Q Rg v) = Nat.card (pCore 2 M) := by
    obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg hv
    have hh := Q_act Rg g (alpha Rg)
    simp only [alpha,act_mVertex,one_mul] at hh
    rw [hh,card_map_of_injective (MulAut.conj g⁻¹).injective]
    change Nat.card (Q Rg (alpha Rg)) = _
    rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,
      card_map_of_injective (embedM_injective Rg)]
  let := finite_stabilizer Rg c
  let : Finite (Q Rg c) := Finite.of_injective
    (inclusion (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1))
    (inclusion_injective _)
  intro hle
  have heq : Q Rg z = Q Rg c := eq_of_le_of_card_ge hle
    ((card_core c hc).trans (card_core z p.end_color).symm).le
  apply p.critical.2
  rw [heq]
  apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
  rw [(sourceGeometry h).distance_constant a p.start_color,p.dist_start (Nat.sub_le _ _)]
  have hh : p.walk.length = sourceDistance h := p.length_eq_b
  change p.walk.length-2 < sourceDistance h
  omega

include h e hz hk in
/-- Every small predecessor slice makes the full reverse-kernel commutator
fixed by the predecessor residual, independently of the two movers. -/
theorem predecessor_kernel_residual_central
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2) :
    ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (Ltilde Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z Rg z ⊓ Q Rg a
  let N := ⁅K,Q Rg c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hslice := critical_predecessor_small_slice h e hz hk hb p hindex
  have hKB : K ≤ B Rg c ((sourceGeometry h).Z_normal _) := hslice.1.ge.trans inf_le_right
  have hVG := ((sourceGeometry h).V_le_Q hb c hc).trans
    (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hKQ : K ≤ Q Rg c := by
    intro x hx
    exact (sourceGeometry h).V_le_Q hb c hc (((mem_B_iff Rg c _ hVG x).mp (hKB hx)).1)
  have hfix : ⁅Ltilde Rg c,K⁆ ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff Rg c _ hVG x).mp (hKB hx)).2 l hl
  have hLn : Ltilde Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    fixed_mod_seed_normalizes_commutator K (Q Rg c) (Ltilde Rg c)
      (hKQ.trans (Q Rg c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized Rg c)) hfix
  have hTG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hTZ : Q Rg t ≤ normalizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg z from fun _ hx => hx.2 _ (adjacent_symm Rg hzt)).trans
      (Z_normalized Rg z)
  have hTB : Q Rg t ≤ normalizer (B Rg c ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :=
    hTG.trans (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb c hc)
  have hTK : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    have hKeq : K = Z Rg z ⊓ B Rg c ((sourceGeometry h).Z_normal _) := hslice.1.symm
    rw [hKeq]
    exact (le_inf hTZ hTB).trans inf_normalizer_le_normalizer_inf
  have hTn : Q Rg t ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hTK hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c (hTG hx))]
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hc
    · exact hct
  have hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hLn hTn
  have hQcT : Q Rg c ≤ Q Rg t := Q_le_adjacent_h Rg ht hct
  have hNZ : N ≤ Z Rg z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQcT.trans hTZ))
  have hNQ : N ≤ Q Rg c :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hQzG : Q Rg z ≤ stabilizer Rg c :=
    (Q_le_adjacent_h Rg ht hzt).trans hTG
  have hfix : N ≤ centralizer (Q Rg z : Set (FreeAmalgam Rg)) :=
    hNZ.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color))
  exact normal_subgroup_fixed_by_noncore_two_group h e hz hc N (Q Rg z)
    (hNQ.trans (fun _ hx => hx.1)) hNn hQzG
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le z p.end_color)
    hfix (critical_endpoint_core_not_le_predecessor h hb p)

include h e hz hk in
/-- Residual conjugation preserves the commutator with the entire reverse
kernel at every small predecessor slice; no mover comparison is assumed. -/
theorem predecessor_kernel_residual_transport
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ = ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
  have hb := distance_gt_two h e hz hk
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hs := critical_predecessor_small_slice h e hz hk hb p hindex
  have hn := predecessor_kernel_residual_central h e hz hk p hindex
  exact plane_slice_commutator_transport_of_fixed (h := h) hb hc _
    (hs.1.ge.trans inf_le_right) hn T hT k hkm

include h e hz hk in
private theorem nonzero_predecessor_residual_path
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hkt : act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k z),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ = ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
        centralizer (Ltilde Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
      (4 ≤ (Q Rg (act Rg k z)).relIndex (Z Rg c) ∨
        (Nat.card (⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ ∧
          ¬ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
            centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) := by
  have hb := distance_gt_two h e hz hk
  have htransport :
      ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ =
        ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [Z_act,inv_inv]
    exact predecessor_kernel_residual_transport h e hz hk p hindex _ hbad k hkm
  have hescape : ¬ Z Rg c ≤ Q Rg (act Rg k z) := by
    intro hh
    have hm : Z Rg (act Rg k⁻¹ c) ≤ Q Rg z := by
      calc
        _ = (Z Rg c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q Rg (act Rg k z)).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q Rg (act Rg k⁻¹ (act Rg k z)) := by
          simpa only [inv_inv] using (Q_act Rg k⁻¹ (act Rg k z)).symm
        _ = Q Rg z := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q Rg z p.end_color))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcfalse : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hlast : Adjacent Rg (p.walk.getVert (p.walk.length-1)) z := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hend : (cosetGraph Rg).Adj (p.walk.getVert (p.walk.length-3)) (act Rg k z) := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr
      ((adjacent_act_iff Rg k _ _).mpr hlast)
  let w₀ : (cosetGraph Rg).Walk c a :=
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
  have hdist : (cosetGraph Rg).dist c (act Rg k z) = sourceDistance h := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath Rg (sourceGeometry h) c (act Rg k z) :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(sourceGeometry h).distance_constant c hcfalse]
      exact hdist⟩
  have hcentral : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
      centralizer (Ltilde Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) :=
    (commutator_mono le_rfl hbad).trans (predecessor_kernel_residual_central h e hz hk p hindex)
  refine ⟨q,?_,?_,htransport,hcentral,?_⟩
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

  by_cases hlarge : 4 ≤ (Q Rg (act Rg k z)).relIndex (Z Rg c)
  · exact Or.inl hlarge
  apply Or.inr
  have hback : act Rg k⁻¹ (act Rg k z) = z := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant c q.start_color]
        exact sourceDistance_pos h) (act Rg k z) q.end_color q.critical)
  have hrex : Nonempty (CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ c)) := by
    rw [←hback]
    exact ⟨qr.act k⁻¹⟩
  obtain ⟨r⟩ := hrex
  have hrs : (Q Rg (act Rg k⁻¹ c)).relIndex (Z Rg z) < 4 := by
    rw [←hback,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      (small_critical_indices h e hz hk q (by omega)).2]
    decide
  let H := ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆
  let D₀ := ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆
  have hDcard : Nat.card D₀ = 2 := by
    dsimp only [D₀]
    rw [small_critical_moving_commutator_eq h e hz hk r hrs]
    exact small_critical_commutator_card h e hz hk r hrs
  let : Finite D₀ := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hkQ : (Q Rg (p.walk.getVert (p.walk.length-2))).map
      (MulAut.conj k).toMonoidHom = Q Rg (p.walk.getVert (p.walk.length-2)) :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg _)
      (Ltilde_le_stabilizer _ hkm))
  have hDk : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    exact (map_mono hbad).trans_eq hkQ
  have hle : H ≤ D₀ := by
    dsimp only [H,D₀]
    rw [←htransport,(critical_kernel_predecessor_moving h e hz hb p).2.2 _ hDk]
    exact commutator_mono inf_le_left le_rfl
  let : Finite H := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hlo := (one_lt_card_iff_ne_bot _).mpr hne
    have hhi := card_le_of_le hle
    rw [hDcard] at hhi
    change 1 < Nat.card H at hlo
    omega
  have heq : H = D₀ := eq_of_le_of_card_ge hle (by rw [hcard,hDcard])
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [heq]
    exact critical_moving_commutator_not_central h e hz hk r
  exact ⟨hcard,heq,hnon⟩

include h e hz hk in
/-- A nonzero full-kernel commutator at a small predecessor slice constructs
an actual residual-shifted critical path, with every overlap retained. Its
image is large, or the same commutator is the noncentral order-two moving
line at the old endpoint. This includes all mover comparisons and both covers. -/
theorem predecessor_nonzero_residual_shift
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
      act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k z),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ = ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
        centralizer (Ltilde Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
      (4 ≤ (Q Rg (act Rg k z)).relIndex (Z Rg c) ∨
        (Nat.card (⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ ∧
          ¬ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
            centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hlast : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hprev : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter h hc hlast hprev
  exact ⟨k,hkm,hkt,nonzero_predecessor_residual_path h e hz hk p hindex hat hct hbad hne k hkm hkt⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
