module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullSeed

/-!
# Forward-line closure on the original cubic graph

Take the normal closure of a controlled radius subgroup under the local
centralizer of its commutator line. Its commutators with both inner layers
vanish: a nonzero subgroup of the order-two line would centralize the
opposite critical seed, contrary to the chosen movement. The closure is a
two-group, so its containment in the predecessor seed centralizer puts it
inside Q despite the retained quotient E/Q of order three. The literal
critical-kernel calculation then forces the closure into the Baumann slice.

The full-seed generating conjugate supplies the contradiction for every
small forward line. Thus that line is central at the starting vertex,
without a moving-cover placement assumption. Normal generation identifies
the whole selected span's commutator with that same line. In the nonabelian
span case it is also the entire derived subgroup. The eligible-slice
application retains its order two and noncentrality at the second vertex.

Whole-core and literal C.1.32 consumers retain the cubic kernel and both
cover orders. Strict slice selection, the remaining edge-image choices,
R4/R6 and distance-four exclusions, and final reconstruction remain with
qt-e-ms-small-a6-reconstruction. Independent natural exhaustion remains
with qt-e-ms-small-a6-exhaustion-large-distance. These local closure results
do not establish source (5.11) or (5.12).

Source: MS93 (5.9), printed pp.920--922, and its use in (5.12), p.927.
Adapts the normal-closure proof in Natural.Exhaustion.LargeDistance.SectionFive.
ForwardClosure and FullSeed, using the actual cubic two-subgroup containment.
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
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
private theorem commutator_sup_centralized_left {G : Type*} [Group G]
    (N U A : Subgroup G) (hUN : U ≤ normalizer (N : Set G))
    (hNA : N ≤ centralizer (A : Set G)) (hUA : U ≤ normalizer (A : Set G)) :
    ⁅N ⊔ U,A⁆ = ⁅U,A⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx a ha
    have hprod : x ∈ (N : Set G) * (U : Set G) :=
      (coe_mul_of_right_le_normalizer_left N U hUN) ▸ hx
    obtain ⟨n,hn,u,hu,rfl⟩ := hprod
    have he : ⁅n,a⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hNA hn a ha).symm
    have hmem : ⁅u,a⁆ ∈ A :=
      le_normalizer_iff_commutator_le_right.mp hUA (commutator_mem_commutator hu ha)
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,←hNA hn _ hmem,mul_inv_cancel_right]
    exact commutator_mem_commutator hu ha
  · exact commutator_mono le_sup_right le_rfl

private theorem exists_normal_span_with_commutator {G : Type*} [Group G]
    (P A T D V : Subgroup G) (hAP : A ≤ P) (hAV : A ≤ V)
    (hTP : T ≤ P) (hDP : D ≤ P)
    (hPT : P ≤ normalizer (T : Set G)) (hPD : P ≤ normalizer (D : Set G))
    (hPV : P ≤ normalizer (V : Set G)) (hcomm : ⁅A,T⁆ ≤ D) :
    ∃ Y : Subgroup G, A ≤ Y ∧ Y ≤ V ∧ P ≤ normalizer (Y : Set G) ∧ ⁅Y,T⁆ ≤ D := by
  let Y₀ := normalClosure (A.subgroupOf P : Set P)
  let Y := Y₀.map P.subtype
  let : (T.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPT
  let : (D.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPD
  let : (V.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPV
  have hAY : A ≤ Y := by
    intro a ha
    exact ⟨⟨a,hAP ha⟩,subset_normalClosure ha,rfl⟩
  have hYV : Y ≤ V := by
    apply map_le_iff_le_comap.mpr
    change Y₀ ≤ V.subgroupOf P
    exact normalClosure_le_normal (fun a ha => hAV ha)
  have hPY : P ≤ normalizer (Y : Set G) := by
    have hh := Y₀.le_normalizer_map P.subtype
    intro p hp
    apply hh
    exact ⟨⟨p,hp⟩,by rw [normalizer_eq_top]; exact mem_top _,rfl⟩
  have hcomm₀ : ⁅T.subgroupOf P,A.subgroupOf P⁆ ≤ D.subgroupOf P := by
    apply commutator_le.mpr
    intro t ht a ha
    change ⁅(t:G),(a:G)⁆ ∈ D
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ht ha)
  have hm := map_mono (f := P.subtype) (commutator_normalClosure_le_of_normal
    (T.subgroupOf P) (A.subgroupOf P) (D.subgroupOf P) hcomm₀)
  rw [map_commutator,map_subgroupOf_eq_of_le hTP,map_subgroupOf_eq_of_le hDP,
    commutator_comm] at hm
  exact ⟨Y,hAY,hYV,hPY,hm⟩


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
/-- A generating centralizer and the original two inner layers exclude
a controlled line in the small critical branch, for both cover orders. -/
theorem small_critical_controlled_line_false
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (A T₀ H₁ : Subgroup (FreeAmalgam Rg))
    (hAV : A ≤ V Rg (alpha Rg)) (hAB : ¬ A ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hTQ : T₀ ≤ Q Rg (alpha Rg))
    (hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T₀ : Set (FreeAmalgam Rg)))
    (hHZ : H₁ ≤ Z Rg (alpha Rg)) (hcard : Nat.card H₁ ≤ 2)
    (hHe : ¬ H₁ ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)))
    (hgen : (stabilizer Rg (alpha Rg) ⊓ centralizer (H₁ : Set (FreeAmalgam Rg))) ⊔
      Z Rg a' = stabilizer Rg (alpha Rg))
    (hcomm : ⁅A,T₀⁆ ≤ H₁)
    (hinner : Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg (alpha Rg)) ≤ T₀) :
    False := by
  have hb2 : 2 < sourceDistance h := by omega
  let P := stabilizer Rg (alpha Rg) ⊓ centralizer (H₁ : Set (FreeAmalgam Rg))
  have hVQ := (sourceGeometry h).V_le_Q hb2 (alpha Rg) rfl
  have hVG := (sourceGeometry h).V_local (alpha Rg) rfl hb2
  have hZQ : Z Rg (alpha Rg) ≤ centralizer (Q Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg (alpha Rg) rfl)
  have hQH : Q Rg (alpha Rg) ≤ centralizer (H₁ : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hZQ).trans (centralizer_le hHZ)
  have hZaV : Z Rg (alpha Rg) ≤ V Rg (alpha Rg) := by
    exact le_iSup_of_le (alpha Rg) (le_iSup_of_le (by simp :
      (cosetGraph Rg).dist (alpha Rg) (alpha Rg) ≤ 2) le_rfl)
  have hAZ : ⁅Z Rg (alpha Rg) ⊔ A,T₀⁆ ≤ H₁ := by
    rw [commutator_sup_centralized_left (Z Rg (alpha Rg)) A T₀
      ((hAV.trans hVG).trans (Z_normalized Rg (alpha Rg)))
      (hZQ.trans (centralizer_le hTQ)) ((hAV.trans hVG).trans hTN)]
    exact hcomm
  have hAP : Z Rg (alpha Rg) ⊔ A ≤ P :=
    le_inf ((sup_le hZaV hAV).trans hVG)
      ((sup_le hZaV hAV).trans (hVQ.trans hQH))
  have hTP : T₀ ≤ P := le_inf (hTQ.trans (fun _ hx => hx.1)) (hTQ.trans hQH)
  have hHP : H₁ ≤ P := le_inf (hHZ.trans (Z_le_stabilizer Rg (alpha Rg)))
    (hHZ.trans (hZaV.trans (hVQ.trans hQH)))
  obtain ⟨Y,hAY,hYV,hPY,hYT⟩ := exists_normal_span_with_commutator
    P (Z Rg (alpha Rg) ⊔ A) T₀ H₁ (V Rg (alpha Rg)) hAP (sup_le hZaV hAV) hTP hHP
    (inf_le_left.trans hTN) (inf_le_right.trans (centralizer_le_normalizer H₁))
    (inf_le_left.trans (DistanceEight.V_normalized Rg (alpha Rg))) hAZ
  let F := Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg (alpha Rg))
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (sourceGeometry h).even (alpha Rg) rfl
    change Even (sourceDistance h) at he
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hQeC : Q Rg a' ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a' p.end_color))
  have hpreQe : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg a' := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,p.dist_end]
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < sourceDistance h
    omega
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hDH : D ≤ H₁)
      (hDe : D ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    let := finite_Z Rg (alpha Rg)
    let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
    let : Finite D := Finite.of_injective (inclusion hDH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = H₁ := eq_of_le_of_card_ge hDH (by omega)
    exact hHe (he ▸ hDe)
  have hYpre : ⁅Y,Z Rg (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hYT)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)).trans
        (Z_normalized Rg _))).trans (hpreQe.trans hQeC)
  have hYpreC := commutator_eq_bot_iff_le_centralizer.mp hYpre
  have hYpreQ : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply two_subgroup_seed_centralizer_le_core h e hz hc Y
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        (alpha Rg) rfl).to_le (hYV.trans hVQ))
    exact le_inf (hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)) hYpreC
  have hYeG : Y ≤ stabilizer Rg a' := by
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hat : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hct : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hYpreQ.trans (Q_le_adjacent_h Rg ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
  have hYK : ⁅Y,Z Rg a' ⊓ Q Rg (alpha Rg)⁆ = ⊥ := by
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
    apply hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans hYT)
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hYeG.trans (Z_normalized Rg a')))).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hYfix : Y ≤ centralizer (F : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hYpreC)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hYK))
  have hYe : ⁅Y,Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    small_critical_predecessor_commutator h e hz hk hb p hsmall Y hYpreQ
      (commutator_eq_bot_iff_le_centralizer.mp hYK)
  have hZeY : Z Rg a' ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    le_normalizer_iff_commutator_le_left.mpr (hYe.trans (le_sup_left.trans hAY))
  have hGY : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hPY hZeY
  exact hAB (le_sup_right.trans (hAY.trans
    (normalized_radius_le_slice_of_critical_commutator h e hz hb2 p Y hYV hGY hYe)))

include h e hz hk in
/-- In the small critical branch, the full forward commutator line
is centralized by the whole starting stabilizer. -/
theorem small_forward_line_central
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  change H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))
  by_contra hnon
  have hne : H ≠ ⊥ := by intro he; exact hnon (he ▸ bot_le)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hline := selected_forward_kernel_line h e hz hk hb p hslice
  have hHZ : H ≤ Z Rg (alpha Rg) :=
    hline.2.trans (adjacent_Z_le Rg rfl hat)
  let := finite_Z Rg (alpha Rg)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hp := (one_lt_card_iff_ne_bot H).mpr hne
    have hh : Nat.card H ≤ 2 := hline.1
    omega
  have hUB : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx y hy
    exact hx.2 y ⟨hy,hh hy⟩
  have hUV : U Rg c ≤ V Rg (alpha Rg) :=
    (DistanceEight.U_le_Z Rg c).trans
      (le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl))
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  obtain ⟨g,hg,hgen,hmove⟩ := exists_seed_line_generator h e hz hk p hsmall H hHZ hcard hnon
  have hgG := Ltilde_le_stabilizer (alpha Rg) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U Rg c).map f
  let J := H.map f
  have hVm : (V Rg (alpha Rg)).map f = V Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized Rg _ hgG)
  have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map f =
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hgG)
  have hTm : T.map f = T := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z Rg (alpha Rg)).map f = Z Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg _ hgG)
  have hAV : A ≤ V Rg (alpha Rg) := hVm ▸ map_mono hUV
  have hAB : ¬ A ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hUB
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hJZ : J ≤ Z Rg (alpha Rg) := hZm ▸ map_mono hHZ
  have hJcard : Nat.card J ≤ 2 := by
    rw [show Nat.card J = Nat.card H from card_map_of_injective (MulAut.conj g).injective,hcard]
  have hcomm : ⁅A,T⁆ ≤ J := by
    change ⁅(U Rg c).map f,T⁆ ≤ H.map f
    rw [show H = ⁅U Rg c,T⁆ from rfl,map_commutator,hTm]
  exact small_critical_controlled_line_false h e hz hk hb p hsmall A T J
    hAV hAB inf_le_left hTN hJZ hJcard hmove hgen hcomm
    (selected_forward_kernel_contains_inner_layers (h := h) hb p)

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


include h e hz hk in
/-- The entire selected span has the same commutator with the forward
kernel as the generating cover. This line is central at the start and
contains the span's derived subgroup. -/
theorem small_selected_span_forward_commutator
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
    ⁅P,T⁆ = H ∧ ⁅P,P⁆ ≤ H ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  let P := localZSpan Rg c (alpha Rg)
  have hfixed : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    small_forward_line_central h e hz hk hb p hsmall hslice
  have hHN : stabilizer Rg (alpha Rg) ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
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
  have hZcG : Z Rg c ≤ stabilizer Rg (alpha Rg) :=
    ((Z_le_localZSpan Rg c (alpha Rg)).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((sourceGeometry h).V_local _ rfl hb)
  have hZc : ⁅Z Rg c,T⁆ ≤ H := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      _ _ T _ hHN ((DistanceEight.U_le_Z Rg c).trans hZcG)
      ((adjacent_Z_le Rg rfl hat).trans (Z_le_stabilizer Rg _)) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hPT : ⁅P,T⁆ ≤ H := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg)) T _ _ hHN
    · intro g
      have hgmap : (stabilizer Rg (alpha Rg)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hHm : H.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      rwa [map_commutator,hTm,hHm] at hm
  have hPP : ⁅P,P⁆ ≤ H :=
    (commutator_mono le_rfl (selected_span_le_forward_kernel (h := h) hb p)).trans hPT
  exact ⟨le_antisymm hPT (commutator_mono
    ((DistanceEight.U_le_Z Rg c).trans (Z_le_localZSpan Rg _ _)) le_rfl),hPP,hfixed⟩

include h e hz hk in
/-- The nonabelian selected span has exactly the central forward line as
its derived subgroup, on the original cubic graph. -/
theorem small_selected_span_derived
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
    ⁅P,P⁆ = H ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
    (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
  have hbound := small_selected_span_forward_commutator h e hz hk hb p hsmall hslice
  have hline := selected_forward_kernel_noncentral_line h e hz hk hb p hslice hnonabelian
  let := finite_Z Rg (p.walk.getVert 1)
  let : Finite H := Finite.of_injective (inclusion hline.2.1) (inclusion_injective _)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hbound.2.1) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot (⁅P,P⁆ : Subgroup (FreeAmalgam Rg))).mpr hnonabelian
  have he : ⁅P,P⁆ = H := eq_of_le_of_card_ge hbound.2.1 (by
    have hh : Nat.card H = 2 := hline.1
    omega)
  exact ⟨he,he ▸ hline.1,hbound.2.1.trans hbound.2.2⟩

include h e hz hk in
/-- The eligible small forward slice is a line central at the original
start and noncentral at the second vertex, without a nonabelian-span
assumption or placement in the starting moving cover. -/
theorem small_forward_slice_central_line
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
    Nat.card H = 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ¬ H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hn := small_forward_slice_noncentral_line h e hz hk hb p hslice hsmall heligible
  exact ⟨hn.1,hn.2.1,small_forward_line_central h e hz hk hb p hsmall hslice,hn.2.2⟩

omit hk in
include h e hz in
/-- Whole-core application of the full-seed closure calculation. The
remaining index-two slice and terminal exclusions belong to this owner;
the entire cubic kernel and both covers remain in the alternative. -/
theorem coreExhaustion_or_cubic_forward_closure :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        let T := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
            ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
        let H := ⁅U Rg (p.walk.getVert 2),T⁆
        ⁅P,T⁆ = H ∧ ⁅P,P⁆ ≤ H ∧
          H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          (¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
            Nat.card H = 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ∧
            ¬ H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
          (⁅P,P⁆ ≠ ⊥ → ⁅P,P⁆ = H ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro a' p hsmall hslice
    have hbound := small_selected_span_forward_commutator h e hz hk hb p hsmall hslice
    refine ⟨hbound.1,hbound.2.1,hbound.2.2,?_,?_⟩
    · intro hel
      have hline := small_forward_slice_central_line h e hz hk hb p hsmall hslice hel
      exact ⟨hline.1,hline.2.1,hline.2.2.2⟩
    · intro hnon
      have hd := small_selected_span_derived h e hz hk hb p hsmall hslice hnon
      exact ⟨hd.1,hd.2.1⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of full-seed forward closure, with the
same cubic projection, complete covers, and unresolved source alternatives. -/
theorem rankTwo_or_cubic_forward_closure :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        let T := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
            ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
        let H := ⁅U Rg (p.walk.getVert 2),T⁆
        ⁅P,T⁆ = H ∧ ⁅P,P⁆ ≤ H ∧
          H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          (¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
            Nat.card H = 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ∧
            ¬ H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
          (⁅P,P⁆ ≠ ⊥ → ⁅P,P⁆ = H ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2) :=
  (coreExhaustion_or_cubic_forward_closure h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
