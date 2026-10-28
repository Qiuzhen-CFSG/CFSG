module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoordinatedLines
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Forward-line closure for the full small critical kernel

In the index-two critical branch, take the normal closure of a radius
subgroup under the relative centralizer of a controlled line. Its
commutators with the predecessor seed and the reverse critical kernel
vanish: a nonzero commutator would be the whole line and would centralize
the endpoint seed. The full-cover pointwise-fixer theorem then bounds the
endpoint commutator by the starting seed. The generating-centralizer
choice makes the closure invariant under the starting stabilizer, forcing
it into the Baumann slice and giving a contradiction.

If the actual forward line lies in the starting moved cover, the existing
cover orbit theorem supplies this simultaneous choice with one component
conjugator. Thus the line is central at the starting vertex. Relative
normal generation identifies it with the nonabelian selected span's entire
derived subgroup. The final application constructs the literal natural
quotient and derived transfer from the midpoint slices, discharging the
previous separate derived-fixedness premise in this moving-line case.

The line has order at most two, so the remaining noncentral case has zero
intersection with the starting moved cover. This is an explicit remaining
case, not an exclusion of it. No full point-radical image, natural subgroup
in place of a quotient, or splitting of the order-thirty-two cover is used.
Source-selected paths and slices, the general forward-line placement,
exact-four radius-index exclusion and intermediate R4/R6 noncentrality,
and both unconditional terminal contradictions remain with
qt-e-ms-small-a6-exhaustion-large-distance. The whole-core assembly remains
with qt-e-ms-small-a6-reconstruction.

Source: MS93 (5.9), pp.920--922, and the terminal argument of (5.12), p.927.
The closure proof adapts SymplecticSetup.ForwardClosure and ForwardLineAll;
SmallKernel and the full-cover orbit theorem replace their native
point-image and natural-subgroup assumptions in the small critical branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

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


include s in
/-- A normal radius subgroup fixed modulo the seed by a critical actor
is contained in the actual Baumann slice. -/
theorem normalized_radius_le_slice_of_critical_commutator
    (hlayer : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (D : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical (alpha d.radical))
    (hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hcomm : ⁅D,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let D₀ := D.comap (embedM d.radical)
  let Z₀ := (Z d.radical (alpha d.radical)).comap (embedM d.radical)
  let A₀ := (Z d.radical a').comap (embedM d.radical)
  have hDG : D ≤ (embedM d.radical).range :=
    (hDV.trans ((replacementGeometry h d).V_local (alpha d.radical) rfl hb)).trans_eq (stabilizer_m_base d.radical)
  have hDm : D₀.map (embedM d.radical) = D := map_comap_eq_self hDG
  have hZm : Z₀.map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical (alpha d.radical)).trans_eq (stabilizer_m_base d.radical))
  have hAm : A₀.map (embedM d.radical) = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
      (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical))
  have hg (m : d.overgroup) : embedM d.radical m ∈ stabilizer d.radical (alpha d.radical) := by
    change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM d.radical (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM d.radical z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change embedM d.radical (m*z*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (embedM d.radical z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 d.overgroup := by
    intro he
    have hh := map_mono (f := embedM d.radical) he
    rw [hAm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hh
    exact (critical_reverse_pair s hlayer p).2 hh
  have hDL := component_commutator_le_of_section_fixed s D₀ Z₀ A₀ hcomm₀ hne
  have hm := map_mono (f := embedM d.radical) hDL
  rw [map_commutator,hDm,hZm,show (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) by
    rw [Ltilde_alpha,replacement_residual h d]] at hm
  intro z hd
  apply (mem_B_iff d.radical (alpha d.radical) _ ((replacementGeometry h d).V_local (alpha d.radical) rfl hb) z).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)

include h in
private theorem radius_le_predecessor_stabilizer (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    V d.radical (alpha d.radical) ≤ stabilizer d.radical (p.walk.getVert (p.walk.length-2)) := by
  apply (V_le_iff d.radical rfl _).mpr
  intro v hd hdist
  apply Z_le_stabilizer_of_dist_le v ((replacementGeometry h d).exists_critical v hd)
  rw [(replacementGeometry h d).distance_constant v hd]
  change (cosetGraph d.radical).dist v (p.walk.getVert (p.walk.length-2)) ≤ replacementDistance h d
  have ht := (cosetGraph_connected d.radical).dist_triangle (u:=v) (v:=alpha d.radical)
    (w:=p.walk.getVert (p.walk.length-2))
  rw [p.dist_start (Nat.sub_le _ _)] at ht
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  omega


include s in
/-- A generating centralizer and the original two inner layers exclude
a controlled line in the small critical branch, for both cover orders. -/
theorem small_critical_controlled_line_false
    (hlayer : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (A T₀ H₁ : Subgroup (FreeAmalgam d.radical))
    (hAV : A ≤ V d.radical (alpha d.radical)) (hAB : ¬ A ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hTQ : T₀ ≤ Q d.radical (alpha d.radical))
    (hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T₀ : Set (FreeAmalgam d.radical)))
    (hHZ : H₁ ≤ Z d.radical (alpha d.radical)) (hcard : Nat.card H₁ ≤ 2)
    (hHe : ¬ H₁ ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)))
    (hgen : (stabilizer d.radical (alpha d.radical) ⊓ centralizer (H₁ : Set (FreeAmalgam d.radical))) ⊔
      Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hcomm : ⁅A,T₀⁆ ≤ H₁)
    (hinner : Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical a' ⊓ Q d.radical (alpha d.radical)) ≤ T₀) :
    False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let P := stabilizer d.radical (alpha d.radical) ⊓ centralizer (H₁ : Set (FreeAmalgam d.radical))
  have hVQ := (replacementGeometry h d).V_le_Q hb2 (alpha d.radical) rfl
  have hVG := (replacementGeometry h d).V_local (alpha d.radical) rfl hb2
  have hZQ : Z d.radical (alpha d.radical) ≤ centralizer (Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical (alpha d.radical) rfl)
  have hQH : Q d.radical (alpha d.radical) ≤ centralizer (H₁ : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hZQ).trans (centralizer_le hHZ)
  have hZaV : Z d.radical (alpha d.radical) ≤ V d.radical (alpha d.radical) := by
    exact le_iSup_of_le (alpha d.radical) (le_iSup_of_le (by simp :
      (cosetGraph d.radical).dist (alpha d.radical) (alpha d.radical) ≤ 2) le_rfl)
  have hAZ : ⁅Z d.radical (alpha d.radical) ⊔ A,T₀⁆ ≤ H₁ := by
    rw [commutator_sup_centralized_left (Z d.radical (alpha d.radical)) A T₀
      ((hAV.trans hVG).trans (Z_normalized d.radical (alpha d.radical)))
      (hZQ.trans (centralizer_le hTQ)) ((hAV.trans hVG).trans hTN)]
    exact hcomm
  have hAP : Z d.radical (alpha d.radical) ⊔ A ≤ P :=
    le_inf ((sup_le hZaV hAV).trans hVG)
      ((sup_le hZaV hAV).trans (hVQ.trans hQH))
  have hTP : T₀ ≤ P := le_inf (hTQ.trans (fun _ hx => hx.1)) (hTQ.trans hQH)
  have hHP : H₁ ≤ P := le_inf (hHZ.trans (Z_le_stabilizer d.radical (alpha d.radical)))
    (hHZ.trans (hZaV.trans (hVQ.trans hQH)))
  obtain ⟨Y,hAY,hYV,hPY,hYT⟩ := exists_normal_span_with_commutator
    P (Z d.radical (alpha d.radical) ⊔ A) T₀ H₁ (V d.radical (alpha d.radical)) hAP (sup_le hZaV hAV) hTP hHP
    (inf_le_left.trans hTN) (inf_le_right.trans (centralizer_le_normalizer H₁))
    (inf_le_left.trans (DistanceEight.V_normalized d.radical (alpha d.radical))) hAZ
  let F := Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical a' ⊓ Q d.radical (alpha d.radical))
  have hc : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (replacementGeometry h d).even (alpha d.radical) rfl
    change Even (replacementDistance h d) at he
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hQeC : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
  have hpreQe : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical a' := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hc)
    rw [(replacementGeometry h d).distance_constant _ hc,p.dist_end]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < replacementDistance h d
    omega
  have hkill (D : Subgroup (FreeAmalgam d.radical)) (hDH : D ≤ H₁)
      (hDe : D ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))) : D = ⊥ := by
    by_contra hn
    let := finite_Z d.radical (alpha d.radical)
    let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
    let : Finite D := Finite.of_injective (inclusion hDH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = H₁ := eq_of_le_of_card_ge hDH (by omega)
    exact hHe (he ▸ hDe)
  have hYpre : ⁅Y,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hYT)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)).trans
        (Z_normalized d.radical _))).trans (hpreQe.trans hQeC)
  have hYpreC := commutator_eq_bot_iff_le_centralizer.mp hYpre
  have hYpreQ : Y ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [←C_eq_Q s hlayer _ hc]
    exact le_inf (hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)) hYpreC
  have hYeG : Y ≤ stabilizer d.radical a' := by
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hat : Adjacent d.radical a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
    have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj d.radical _ _).mp hh
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [p.end_color] at hh
      cases he : color d.radical t <;> simp_all
    exact (hYpreQ.trans (Q_le_adjacent_h d.radical ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hYK : ⁅Y,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆ = ⊥ := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
    apply hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans hYT)
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hYeG.trans (Z_normalized d.radical a')))).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hYfix : Y ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hYpreC)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hYK))
  have hYe : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    small_critical_predecessor_commutator s hlayer hb p hsmall Y hYpreQ
      (commutator_eq_bot_iff_le_centralizer.mp hYK)
  have hZeY : Z d.radical a' ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hYe.trans (le_sup_left.trans hAY))
  have hGY : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hPY hZeY
  exact hAB (le_sup_right.trans (hAY.trans
    (normalized_radius_le_slice_of_critical_commutator s hlayer hb2 p Y hYV hGY hYe)))

include s in
/-- In the small critical branch, a forward commutator line lying in the
starting moved cover is centralized by the whole starting stabilizer. -/
theorem small_forward_line_central_of_moving
    (hlayer : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hHU : ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical (alpha d.radical)) :
    ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  change H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
  by_contra hnon
  have hne : H ≠ ⊥ := by intro he; exact hnon (he ▸ bot_le)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hline := selected_forward_kernel_line s hlayer hb p hslice
  have hHZ : H ≤ Z d.radical (alpha d.radical) :=
    hline.2.trans (adjacent_Z_le d.radical rfl hat)
  let := finite_Z d.radical (alpha d.radical)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hp := (one_lt_card_iff_ne_bot H).mpr hne
    have hh : Nat.card H ≤ 2 := hline.1
    omega
  have hUB : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx y hy
    exact hx.2 y ⟨hy,hh hy⟩
  have hUV : U d.radical c ≤ V d.radical (alpha d.radical) :=
    (DistanceEight.U_le_Z d.radical c).trans
      (le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl))
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator s hlayer p H hHU hcard hnon
  have hgG := Ltilde_le_stabilizer (alpha d.radical) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U d.radical c).map f
  let J := H.map f
  have hVm : (V d.radical (alpha d.radical)).map f = V d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _ hgG)
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map f =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hgG)
  have hTm : T.map f = T := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z d.radical (alpha d.radical)).map f = Z d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical _ hgG)
  have hAV : A ≤ V d.radical (alpha d.radical) := hVm ▸ map_mono hUV
  have hAB : ¬ A ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hUB
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hJZ : J ≤ Z d.radical (alpha d.radical) := hZm ▸ map_mono hHZ
  have hJcard : Nat.card J ≤ 2 := by
    rw [show Nat.card J = Nat.card H from card_map_of_injective (MulAut.conj g).injective,hcard]
  have hcomm : ⁅A,T⁆ ≤ J := by
    change ⁅(U d.radical c).map f,T⁆ ≤ H.map f
    rw [show H = ⁅U d.radical c,T⁆ from rfl,map_commutator,hTm]
  exact small_critical_controlled_line_false s hlayer hb p hsmall A T J
    hAV hAB inf_le_left hTN hJZ hJcard hmove hgen hcomm
    (selected_forward_kernel_contains_inner_layers (h := h) hb p)

include s in
/-- The remaining forward-line obstruction is literally outside the starting
moved cover: any nonzero intersection with that cover forces local centrality. -/
theorem small_forward_line_central_or_disjoint
    (hlayer : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let H := ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆
    H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∨
      H ⊓ U d.radical (alpha d.radical) = ⊥ := by
  dsimp only
  by_cases hbot : (⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ : Subgroup (FreeAmalgam d.radical)) ⊓
      U d.radical (alpha d.radical) = ⊥
  · exact Or.inr hbot
  · left
    apply small_forward_line_central_of_moving s hlayer hb p hsmall hslice
    let H := ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆
    have hline := selected_forward_kernel_line s hlayer hb p hslice
    let := finite_Z d.radical (p.walk.getVert 1)
    let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
    let : Finite (H ⊓ U d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot (H ⊓ U d.radical (alpha d.radical))).mpr hbot
    have he : H ⊓ U d.radical (alpha d.radical) = H :=
      eq_of_le_of_card_ge inf_le_left (by have hh : Nat.card H ≤ 2 := hline.1; omega)
    exact inf_eq_left.mp he

include e hz hn in
/-- The actual selected span has the forward line as its derived subgroup
when that line lies in the starting moved cover. This supplies the derived
fixedness premise of the terminal natural-quotient argument. -/
theorem small_selected_span_derived_of_moving_line_knownSimple
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hHU : ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical (alpha d.radical))
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let H := ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆
    ⁅P,P⁆ = H ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hlayer := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P := localZSpan d.radical c (alpha d.radical)
  have hfixed : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    small_forward_line_central_of_moving s hlayer hb p hsmall hslice hHU
  have hHN : stabilizer d.radical (alpha d.radical) ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTQt : T ≤ Q d.radical t := inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)
  have hseed : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    ((Z_le_localZSpan d.radical c (alpha d.radical)).trans (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  have hZc : ⁅Z d.radical c,T⁆ ≤ H := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      _ _ T _ hHN ((DistanceEight.U_le_Z d.radical c).trans hZcG)
      ((adjacent_Z_le d.radical rfl hat).trans (Z_le_stabilizer d.radical _)) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hPT : ⁅P,T⁆ ≤ H := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) T _ _ hHN
    · intro g
      have hgmap : (stabilizer d.radical (alpha d.radical)).map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer
          ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      have hHm : H.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      rwa [map_commutator,hTm,hHm] at hm
  have hPP : ⁅P,P⁆ ≤ H :=
    (commutator_mono le_rfl (selected_span_le_forward_kernel (h := h) hb p)).trans hPT
  have hline := selected_forward_kernel_noncentral_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice hnonabelian
  let := finite_Z d.radical t
  let : Finite H := Finite.of_injective (inclusion hline.2.1) (inclusion_injective _)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hPP) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical))).mpr hnonabelian
  have he : ⁅P,P⁆ = H := eq_of_le_of_card_ge hPP (by have hh : Nat.card H = 2 := hline.1; omega)
  exact ⟨he,he ▸ hline.1,hPP.trans hfixed⟩

/-- On the original midpoint orbit, placement of the forward line in the
whole moved cover supplies the selected derived-fixedness premise. The
natural quotient, its literal action, and transfer to index-two subgroups
retain both cover orders and the same endpoint conjugator. -/
theorem selected_natural_quotient_of_midpoint_moving_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hHU : ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical (alpha d.radical))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      (∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd) ∧
      (center (forwardMovedSpan d.radical (p.walk.getVert 2))).index = 16 ∧
      Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
        A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
        ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (midpoint_slice_eq_reverse_kernel s hc hb p g hg he hopposite).2.2.1
  have hfixed := (small_selected_span_derived_of_moving_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p (by omega) hslice hHU hnonabelian).2.2
  exact selected_natural_quotient_and_transfer_of_midpoint_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hnonabelian
    (hfixed.trans (centralizer_le (Ltilde_le_stabilizer _))) hslice g hg he hopposite

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
