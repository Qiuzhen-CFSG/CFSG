module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeForwardLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaControl

/-!
# The full source kernel in the nonsylow small-slice configuration

The shifted span D lies in the starting radius and the endpoint stabilizer,
while its generating centralizer P satisfies P Z_z = G_c. Its escape from the
Baumann subgroup excludes the permutation extension of X_z: that extension
would control [D,X_z] by the critical commutator and [D,X_z intersect Q_c].
Both lie in Z_c, the latter by the proved radius-core estimate. Normal-section
control would then put D in the Baumann subgroup.

Consequently X_z = U_z C_{X_z}(G_z). The whole central summand is retained in
A_0 = X_z intersect Q_c; it centralizes every endpoint-local actor. Thus the
literal source R_3 = [D,A_0] equals the previously proved seed-kernel line J,
and full-X displacement equals full-seed displacement. The three-pair
alignment/control theorem places R_3 in the critical commutator times the
endpoint center. Its other alternative is excluded by the same Baumann
escape. No identification of X with Z or U is made.

The actual nonsylow application preserves the original characteristic
replacement, overlapping paths, component conjugator, selected span and both
centralizer spans. It transports central generation to every component
vertex, places R_3 in D intersect A_0, and realizes R_3 using one conjugated
shifted seed under the same centralizer. Both moved covers of orders sixteen
and thirty-two and all central attachments remain present.

Centrality of this line under the whole starting stabilizer, the comparison
of the two shifted spans and source (5.9)'s strict slice bound remain open.
The terminal, original Sylow and distance-four branches, and the unconditional
large-distance exclusion, remain with the original assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.2) and (5.9), printed pp.866--867,913--915,920--922,
especially the definitions of A_0 and R_3 and the central-generation clause
on p.921. This uses the natural minimum-replacement graph and kernels.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
private theorem span_control_false
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (D P A : Subgroup (FreeAmalgam d.radical))
    (hDV : D ≤ V d.radical a) (hPG : P ≤ stabilizer d.radical a)
    (hAG : A ≤ stabilizer d.radical a) (hne : ¬ A ≤ Q d.radical a)
    (hPN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ A = stabilizer d.radical a)
    (hDB : ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (hcomm : ⁅D,A⁆ ≤ Z d.radical a) : False := by
  let N := D ⊔ Z d.radical a
  have hNV : N ≤ V d.radical a := sup_le hDV (Z_le_VBall d.radical a 2)
  have hNG : N ≤ stabilizer d.radical a := hNV.trans
    ((replacementGeometry h d).V_local a ha (by
      rw [(replacementGeometry h d).distance_constant a ha]; exact hb))
  have hNA : ⁅N,A⁆ ≤ Z d.radical a :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) D (Z d.radical a)
      A (Z d.radical a) (Z_normalized d.radical a) (le_sup_left.trans hNG)
      (Z_le_stabilizer d.radical a) hcomm
      (le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a)))
  have hGN : stabilizer d.radical a ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr (hNA.trans le_sup_right))
    exact (le_inf hPN (hPG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hDB (le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb ha N A
    hNV hGN hAG hne hNA))

include s in
/-- Baumann escape of the selected span excludes the permutation extension
of the full endpoint omega layer. The entire central summand is retained. -/
theorem cube_generated_span_X_central_generation
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (D P : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDz : D ≤ stabilizer d.radical z)
    (hPG : P ≤ stabilizer d.radical a)
    (hDN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical a)
    (hDB : ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  let rev : CriticalPath d.radical (replacementGeometry h d) z a :=
    CriticalPath.ofPair q.end_color (critical_reverse_pair s hc q)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc q hsmall).2]
    decide
  rcases full_X_generation_or_control_at s hc rev hs with hgenX | hcontrol
  · exact hgenX
  exfalso
  have hZX (v : Vertex d.radical) (hv : color d.radical v = false) :
      Z d.radical v ≤ X d.radical v := by
    apply (replacementGeometry h d).omega_bound v hv
    rw [(replacementGeometry h d).distance_constant v hv]
    exact replacementDistance_pos h d
  have hXG : X d.radical z ≤ stabilizer d.radical a :=
    CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
      (edgeCentralizerCondition s hc) (replacementDistance_pos h d) z q.end_color a
      (critical_reverse_pair s hc q)
  have hRZ : ⁅X d.radical z,Z d.radical a⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_right.mp (hXG.trans (Z_normalized d.radical a))
  have hDQ : D ≤ Q d.radical a :=
    hDV.trans ((replacementGeometry h d).V_le_Q hb a q.start_color)
  have hDR : D ≤ centralizer ((⁅X d.radical z,Z d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    (hDQ.trans (Q_le_centralizer_X d.radical a)).trans
      (centralizer_le (hRZ.trans (hZX a q.start_color)))
  have hkernel : ⁅D,X d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical a :=
    (commutator_mono hDV inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb u hR a q.start_color)
  have hfull : ⁅D,X d.radical z⁆ ≤ Z d.radical a :=
    (hcontrol D hDz hDR).trans (sup_le hRZ hkernel)
  exact span_control_false s hb q.start_color D P (Z d.radical z) hDV hPG
    ((hZX z q.end_color).trans hXG) (critical_reverse_pair s hc q).2 hDN hgen hDB
    ((commutator_mono le_rfl (hZX z q.end_color)).trans hfull)

private theorem commutator_sup_fixed {F : Type*} [Group F]
    (A E P : Subgroup F) (hEA : E ≤ normalizer (A : Set F))
    (hEP : E ≤ centralizer (P : Set F)) : ⁅A ⊔ E,P⁆ = ⁅A,P⁆ := by
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx p hp
  have hh : x ∈ (A : Set F) * (E : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left A E hEA]
    exact hx
  obtain ⟨a,ha,e,he,rfl⟩ := hh
  have hz : ⁅e,p⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hEP he p hp).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hz,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator ha hp

include s in
/-- Central generation preserves both full endpoint and full kernel
displacements for every actor in the literal endpoint stabilizer. -/
theorem critical_X_displacements_of_central_generation
    (hc : DistanceTwo.CentralLayer d) {a z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hgen : X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ stabilizer d.radical z) :
    ⁅Y,X d.radical z⁆ = ⁅Y,Z d.radical z⁆ ∧
      ⁅Y,X d.radical z ⊓ Q d.radical a⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical a⁆ := by
  let F := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hZX : Z d.radical z ≤ X d.radical z := by
    apply (replacementGeometry h d).omega_bound z q.end_color
    rw [(replacementGeometry h d).distance_constant z q.end_color]
    exact replacementDistance_pos h d
  have hXZ : X d.radical z = Z d.radical z ⊔ F :=
    le_antisymm (hgen.le.trans (sup_le_sup_right (DistanceEight.U_le_Z d.radical z) _))
      (sup_le hZX inf_le_left)
  have hFC : F ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le (Z_le_stabilizer d.radical z))
  have hFY : F ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hY)
  constructor
  · rw [hXZ,commutator_comm Y,commutator_comm Y]
    exact commutator_sup_fixed _ F Y
      (hFC.trans (Subgroup.centralizer_le_normalizer _)) hFY
  · rw [critical_X_kernel_of_central_generation s hc q hgen,
      commutator_comm Y,commutator_comm Y]
    exact commutator_sup_fixed _ F Y
      ((hFC.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)) hFY
include h in
private theorem critical_last_edge_inputs (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) ∧
      Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) ∧
      Z d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hct : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    have hi : p.walk.length-1+1 = p.walk.length := by omega
    rw [hi,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases hc : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    have hi : p.walk.length-2+1 = p.walk.length-1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  refine ⟨hct,Q_le_adjacent_h d.radical ht het,?_⟩
  apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
  rw [p.dist_start (Nat.sub_le _ _),(replacementGeometry h d).distance_constant a p.start_color]
  change p.walk.length-1 < replacementDistance h d
  have he : p.walk.length = replacementDistance h d := p.length_eq_b
  omega


include s in
/-- The source full kernel has exactly the seed-kernel line. The full endpoint
commutator escapes the product of that line and the critical commutator, while
the kernel line lies in the critical commutator times the endpoint center. -/
theorem cube_generated_span_full_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (D P : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hPG : P ≤ stabilizer d.radical a)
    (hDN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical a)
    (hDB : ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    let A₀ := X d.radical z ⊓ Q d.radical a
    let J := ⁅D,Z d.radical z ⊓ Q d.radical a⁆
    let R₃ := ⁅D,A₀⁆
    X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    A₀ = (Z d.radical z ⊓ Q d.radical a) ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    R₃ = J ∧ Nat.card R₃ = 2 ∧ R₃ ≤ Z d.radical a ⊓ Z d.radical z ∧
    R₃ ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧
    ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
    ¬ ⁅D,X d.radical z⁆ ≤ R₃ ⊔ ⁅Z d.radical a,Z d.radical z⁆ ∧
    R₃ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
      (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hedge := critical_last_edge_inputs (h := h) hb q
  have hDedge := hDpre.trans hedge.2.1
  have hDz : D ≤ stabilizer d.radical z :=
    hDedge.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hXgen := cube_generated_span_X_central_generation s hc hb u hR q hsmall
    D P hDV hDz hPG hDN hgen hDB
  have hdisp := critical_X_displacements_of_central_generation s hc q hXgen D hDz
  have hline := cube_generated_span_kernel_line s hc hb u hR q hsmall D P hDV
    hDpre hPG hDN hgen hDB
  let K := Z d.radical z ⊓ Q d.radical a
  let J := ⁅D,K⁆
  have hZG : Z d.radical z ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color (by
      rw [(replacementGeometry h d).distance_constant a q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized d.radical a))
  have hneg : ¬ ⁅D,Z d.radical z⁆ ≤ J ⊔ ⁅Z d.radical a,Z d.radical z⁆ := by
    intro hh
    exact span_control_false s hb q.start_color D P (Z d.radical z) hDV hPG hZG
      (critical_reverse_pair s hc q).2 hDN hgen hDB
      (hh.trans (sup_le (hline.2.1.trans inf_le_left) hcrit))
  refine ⟨hXgen,critical_X_kernel_of_central_generation s hc q hXgen,hdisp.2,
    by simpa only [hdisp.2] using hline.1,
    by simpa only [hdisp.2] using hline.2.1,
    by simpa only [hdisp.2] using hline.2.2,hdisp.1,?_,?_⟩
  · rw [hdisp.1,hdisp.2]
    exact hneg
  · rw [hdisp.2]
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hfixed : K = Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
      dsimp only [K]
      rw [←C_eq_Q s hc a q.start_color]
      apply le_antisymm (inf_le_inf_left _ inf_le_right)
      exact le_inf inf_le_left (le_inf (inf_le_left.trans hZG) inf_le_right)
    have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≤ 2 := by
      have hC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical a q.start_color))
      exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
        (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
          (small_critical_indices s hc q hsmall).2
    rcases cube_edge_alignment_or_control s hc u hR q.end_color hedge.1
      (Z d.radical a) D hedge.2.2 hDedge q.critical.2 hindex with halign | hcontrol
    · simpa only [←hfixed,commutator_comm K D,commutator_comm (Z d.radical z) (Z d.radical a)] using halign
    · exfalso
      apply hneg
      simpa only [←hfixed,commutator_comm (Z d.radical z) D,commutator_comm K D,
        commutator_comm (Z d.radical z) (Z d.radical a)] using hcontrol

omit [Finite G] in
private theorem X_central_generation_act {a : Vertex d.radical}
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (g : FreeAmalgam d.radical) :
    X d.radical (act d.radical g a) = U d.radical (act d.radical g a) ⊔
      (X d.radical (act d.radical g a) ⊓ centralizer
        (stabilizer d.radical (act d.radical g a) : Set (FreeAmalgam d.radical))) := by
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hm := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup,←map_inf_centralizer_of_injective f (MulAut.conj g⁻¹).injective] at hm
  simpa only [f,X_act,U_act,stabilizer_act] using hm

omit [Finite G] in
private theorem X_central_generation_all {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hgenBase := X_central_generation_act hgen g⁻¹
  rw [hbase] at hgenBase
  intro v hv
  obtain ⟨k,rfl⟩ := exists_mVertex_of_color d.radical hv
  simpa only [alpha,act_mVertex,one_mul] using X_central_generation_act hgenBase k

private theorem exists_span_line_generator {F : Type*} [Group F]
    (H P K : Subgroup F)
    (hcard : Nat.card (⁅conjugateSpanBy H P,K⁆ : Subgroup F) = 2) :
    ∃ x : P, ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ = ⁅conjugateSpanBy H P,K⁆ := by
  let J := ⁅conjugateSpanBy H P,K⁆
  let : Finite J := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hne : J ≠ ⊥ := by
    intro he
    have hc : Nat.card J = 2 := hcard
    rw [he,card_bot] at hc
    omega
  have hex : ∃ x : P, ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ ≠ ⊥ := by
    by_contra! hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => commutator_eq_bot_iff_le_centralizer.mp (hh x))
  obtain ⟨x,hx⟩ := hex
  have hsub : ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ ≤ J :=
    commutator_mono (show H.map (MulAut.conj (x : F)).toMonoidHom ≤ conjugateSpanBy H P by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun y : P => H.map (MulAut.conj (y : F)).toMonoidHom) x) le_rfl
  let : Finite (⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ : Subgroup F) :=
    Finite.of_injective (inclusion hsub) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot _).mpr hx
  have he : ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ = J :=
    eq_of_le_of_card_ge hsub (by rw [hcard]; omega)
  exact ⟨x,he⟩

/-- The same nonsylow small-slice witnesses now discharge central generation
at every original component vertex and identify the source R₃ with J. Both
centralizer spans, the selected span and the original component conjugator
remain in the statement. No centrality under the starting stabilizer is assumed. -/
theorem nonsylow_small_shifted_full_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let T₂ := T.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        T₂ = Q d.radical a ⊓ centralizer
          (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) ∧
        Z d.radical c ≤ Y ∧ Y ≤ V d.radical a ∧
        stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) ∧
        ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ Z d.radical a ∧ Nat.card H₂ = 2 ∧
        H₂ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Y,T₂⁆ ≤ H₂ ∧ Z d.radical a ≤ Q d.radical a' ∧ Y ≤ Q d.radical a' ∧
        conjugateSpanBy (Z d.radical a) P ≤ Q d.radical a' ∧
        conjugateSpanBy Y P ≤ Q d.radical a' ∧
        Z d.radical a ≤ V d.radical c ∧
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) ∧
        let J := ⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z ⊓ Q d.radical c⁆
        Nat.card J = 2 ∧ J ≤ Z d.radical c ⊓ Z d.radical z ∧
        J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧ J ≠ H₂ ∧
        let D := conjugateSpanBy (Z d.radical a) P
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        (∀ v : Vertex d.radical, color d.radical v = false →
          X d.radical v = U d.radical v ⊔
            (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)))) ∧
        A₀ = (Z d.radical z ⊓ Q d.radical c) ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        R₃ = J ∧ R₃ ≤ D ⊓ A₀ ∧
        (∃ x ∈ P, ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,A₀⁆ = R₃) ∧
        ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
        ¬ ⁅D,X d.radical z⁆ ≤ R₃ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        R₃ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
          (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne⟩ :=
    nonsylow_small_shifted_kernel_line_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hslice hsmall
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le hZaV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  obtain ⟨hXgen,hA₀,hR₃,hRcard,hRseed,hRedge,hfull,hnot,hcontrol⟩ :=
    cube_generated_span_full_kernel s hc hb2 u hR q (by rw [hi]; decide)
      D P hDV hDpre inf_le_left (le_normalizer_conjugateSpanBy _ _) hgen
      (fun hh => hZaB ((le_conjugateSpanBy _ _).trans hh))
  have hTG : T ≤ stabilizer d.radical c :=
    inf_le_left.trans (Q_le_stabilizer_of_dist_le_two (alpha d.radical) c rfl q.start_color
      (by
        have hl : p.walk.length = replacementDistance h d := p.length_eq_b
        exact (p.dist_start (by omega : 2 ≤ p.walk.length)).le))
  have hHU : ⁅U d.radical c,T⁆ ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hHc : H₂ ≤ Z d.radical c :=
    ((map_mono hHU).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized c (Ltilde_le_stabilizer c hy)))).trans (DistanceEight.U_le_Z d.radical c)
  have hQcP : Q d.radical c ≤ P :=
    le_inf (fun _ hx => hx.1)
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))).trans (centralizer_le hHc))
  have hR₃D : ⁅D,X d.radical z ⊓ Q d.radical c⁆ ≤ D :=
    le_normalizer_iff_commutator_le_left.mp
      ((inf_le_right.trans hQcP).trans (le_normalizer_conjugateSpanBy _ _))
  have hZX : Z d.radical z ≤ X d.radical z := by
    apply (replacementGeometry h d).omega_bound z q.end_color
    rw [(replacementGeometry h d).distance_constant z q.end_color]
    exact replacementDistance_pos h d
  have hR₃A : ⁅D,X d.radical z ⊓ Q d.radical c⁆ ≤ X d.radical z ⊓ Q d.radical c :=
    le_inf ((hRseed.trans inf_le_right).trans hZX)
      ((hRseed.trans inf_le_left).trans ((Z_le_VBall d.radical c 2).trans
        ((replacementGeometry h d).V_le_Q hb2 c q.start_color)))
  obtain ⟨x,hx⟩ := exists_span_line_generator (Z d.radical a) P
    (X d.radical z ⊓ Q d.radical c) hRcard
  exact ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    X_central_generation_all q.end_color hXgen,hA₀,hR₃,le_inf hR₃D hR₃A,
    ⟨x,x.property,hx⟩,hfull,hnot,hcontrol⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
