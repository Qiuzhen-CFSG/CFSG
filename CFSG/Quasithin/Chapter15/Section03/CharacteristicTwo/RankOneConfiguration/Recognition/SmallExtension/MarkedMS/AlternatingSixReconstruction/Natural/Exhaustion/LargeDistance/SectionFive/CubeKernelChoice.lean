module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallMovers

/-!
# Independence of the aligned full-kernel line

Two nonzero reverse-kernel commutators in the same three-pair edge radical
agree if both lie in the critical commutator times the endpoint center.
Indeed that product centralizes the edge radical, so it also contains the
kernel commutator with the join of the two actors. If this latter commutator
had order greater than two, the large-kernel comparison would control full
seed displacement by the same aligned product. The aligned-actor theorem
would then make the kernel commutator trivial. Thus both nonzero subgroups
are the same line. This uses the checked two-cover structural comparisons;
no finite enumeration or splitting of a central attachment is needed.

Apply uniqueness to two escaping centralizer spans on the same forward
critical path. The full-X theorem supplies each span's nonzero aligned line
and identifies its full kernel with its seed kernel. Literal shifted-path
placement then proves independence from every admissible component choice,
including choices with different centralizing supplements. The original
nonsylow consumer retains all prior witnesses and also establishes the full-X
and full-kernel displacement identities for its actual selected Y and W.

This discharges the choice-independence step in (5.9). Centrality under the
whole starting stabilizer, the remaining Y/W comparison and the strict
forward-slice contradiction are still required. The original small-critical-
image restriction, terminal, Sylow and distance-four branches remain explicit;
no unconditional distance bound is asserted here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3) and (5.9), printed pp.866--867,920--922. All kernels and
embeddings are those of the natural minimum characteristic replacement.
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
/-- Two nonzero aligned reverse-kernel commutators in the same literal edge
radical agree, including the central attachment of either moved cover. -/
theorem cube_aligned_kernel_line_unique
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a z t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hzt : Adjacent d.radical z t) (hAt : Z d.radical a ≤ Q d.radical t)
    (P₁ P₂ : Subgroup (FreeAmalgam d.radical))
    (hP₁ : P₁ ≤ Q d.radical t) (hP₂ : P₂ ≤ Q d.radical t)
    (hn₁ : ⁅Z d.radical z ⊓ Q d.radical a,P₁⁆ ≠ ⊥)
    (hn₂ : ⁅Z d.radical z ⊓ Q d.radical a,P₂⁆ ≠ ⊥)
    (ha₁ : ⁅Z d.radical z ⊓ Q d.radical a,P₁⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (ha₂ : ⁅Z d.radical z ⊓ Q d.radical a,P₂⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) :
    ⁅Z d.radical z ⊓ Q d.radical a,P₁⁆ = ⁅Z d.radical z ⊓ Q d.radical a,P₂⁆ := by
  let F := Z d.radical z ⊓ Q d.radical a
  let C := stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  let T := ⁅Z d.radical a,Z d.radical z⁆ ⊔ C
  let P := P₁ ⊔ P₂
  let K := ⁅F,P⁆
  have hPt : P ≤ Q d.radical t := sup_le hP₁ hP₂
  have htG : Q d.radical t ≤ stabilizer d.radical z :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hzt)
  have hPG : P ≤ stabilizer d.radical z := hPt.trans htG
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hzt
    rw [q.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have heC : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro v hv
    rw [Z,if_neg (by simp [ht])] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2
  have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hAt).trans
      (cube_edge_seed_commutator_le s hc u hR q.end_color hzt)
  have hTC : T ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    sup_le (hcrit.trans heC) (inf_le_right.trans (centralizer_le htG))
  have hTN : Q d.radical t ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hTC).trans (Subgroup.centralizer_le_normalizer _)
  have hKT : K ≤ T := by
    change ⁅F,P₁ ⊔ P₂⁆ ≤ T
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (Q d.radical t) P₁ P₂ F T hTN hP₁ hP₂
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  have hTG : T ≤ stabilizer d.radical z :=
    sup_le (hcrit.trans ((adjacent_Z_le d.radical q.end_color hzt).trans
      (Z_le_stabilizer d.radical z))) inf_le_left
  let := finite_stabilizer d.radical z
  let : Finite K := Finite.of_injective (inclusion (hKT.trans hTG)) (inclusion_injective _)
  have hZG : Z d.radical z ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color (by
      rw [(replacementGeometry h d).distance_constant a q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hfixed : F = Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    dsimp only [F]
    rw [←C_eq_Q s hc a q.start_color]
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hZG) inf_le_right)
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a q.start_color))
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc q hsmall).2
  have hcard : Nat.card K ≤ 2 := by
    by_contra! hlarge
    have hlarge' : 2 < Nat.card (⁅Z d.radical z ⊓ centralizer
        (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ : Subgroup (FreeAmalgam d.radical)) := by
      simpa only [K,hfixed] using hlarge
    have hcontrol := cube_edge_large_fixed_commutator s hc u hR q.end_color hzt
      (Z d.radical a) P hAt hPt q.critical.2 hindex hlarge'
    have hwhole : ⁅U d.radical z,P⁆ ≤ T :=
      (commutator_mono (DistanceEight.U_le_Z d.radical z) le_rfl).trans
        (hcontrol.trans (sup_le (hfixed ▸ hKT)
          (by rw [commutator_comm]; exact le_sup_left)))
    have hbot := small_critical_aligned_kernel_commutator_eq_bot s hc q hsmall P hPG hwhole
    change K = ⊥ at hbot
    rw [hbot,card_bot] at hlarge
    omega
  have h₁ : ⁅F,P₁⁆ ≤ K := commutator_mono le_rfl le_sup_left
  have h₂ : ⁅F,P₂⁆ ≤ K := commutator_mono le_rfl le_sup_right
  let : Finite (⁅F,P₁⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅F,P₂⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hc₁ := (one_lt_card_iff_ne_bot ⁅F,P₁⁆).mpr hn₁
  have hc₂ := (one_lt_card_iff_ne_bot ⁅F,P₂⁆).mpr hn₂
  exact (eq_of_le_of_card_ge h₁ (by omega)).trans (eq_of_le_of_card_ge h₂ (by omega)).symm

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
/-- Two escaping spans on the same forward critical path have the same
full reverse-kernel commutator. Their normalizing supplements may differ. -/
theorem cube_generated_spans_full_kernel_eq
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (D₁ P₁ D₂ P₂ : Subgroup (FreeAmalgam d.radical))
    (hDV₁ : D₁ ≤ V d.radical a) (hDV₂ : D₂ ≤ V d.radical a)
    (hDpre₁ : D₁ ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hDpre₂ : D₂ ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hPG₁ : P₁ ≤ stabilizer d.radical a) (hPG₂ : P₂ ≤ stabilizer d.radical a)
    (hDN₁ : P₁ ≤ normalizer (D₁ : Set (FreeAmalgam d.radical)))
    (hDN₂ : P₂ ≤ normalizer (D₂ : Set (FreeAmalgam d.radical)))
    (hgen₁ : P₁ ⊔ Z d.radical z = stabilizer d.radical a)
    (hgen₂ : P₂ ⊔ Z d.radical z = stabilizer d.radical a)
    (hDB₁ : ¬ D₁ ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (hDB₂ : ¬ D₂ ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    ⁅D₁,X d.radical z ⊓ Q d.radical a⁆ = ⁅D₂,X d.radical z ⊓ Q d.radical a⁆ := by
  obtain ⟨_,_,he₁,hcard₁,_,_,_,_,halign₁⟩ :=
    cube_generated_span_full_kernel s hc hb u hR q hsmall D₁ P₁ hDV₁ hDpre₁
      hPG₁ hDN₁ hgen₁ hDB₁
  obtain ⟨_,_,he₂,hcard₂,_,_,_,_,halign₂⟩ :=
    cube_generated_span_full_kernel s hc hb u hR q hsmall D₂ P₂ hDV₂ hDpre₂
      hPG₂ hDN₂ hgen₂ hDB₂
  have hn₁ : ⁅Z d.radical z ⊓ Q d.radical a,D₁⁆ ≠ ⊥ := by
    intro hz
    rw [he₁,commutator_comm,hz,card_bot] at hcard₁
    omega
  have hn₂ : ⁅Z d.radical z ⊓ Q d.radical a,D₂⁆ ≠ ⊥ := by
    intro hz
    rw [he₂,commutator_comm,hz,card_bot] at hcard₂
    omega
  have hedge := critical_last_edge_inputs (h := h) hb q
  have hline := cube_aligned_kernel_line_unique s hc u hR q hsmall hedge.1 hedge.2.2
    D₁ D₂ (hDpre₁.trans hedge.2.1) (hDpre₂.trans hedge.2.1) hn₁ hn₂
    (by rwa [he₁,commutator_comm] at halign₁)
    (by rwa [he₂,commutator_comm] at halign₂)
  rw [he₁,he₂,commutator_comm D₁,commutator_comm D₂]
  exact hline

include s in
/-- Source (5.9)'s R₃ is independent of every admissible component choice
on this same overlapping forward path. The original small-image premise,
actual shifted seed and centralizer span remain literal. -/
theorem cube_shifted_full_kernel_choice_independent
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) = 2)
    (q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z)
    (hdist : (cosetGraph d.radical).dist a' z = 2)
    (hpre : q.walk.getVert (q.walk.length-2) = a')
    (hqsmall : (Q d.radical z).relIndex (Z d.radical (p.walk.getVert 2)) < 4)
    (y₁ y₂ : FreeAmalgam d.radical)
    (hy₁ : y₁ ∈ stabilizer d.radical (p.walk.getVert 2))
    (hy₂ : y₂ ∈ stabilizer d.radical (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    let H₁ := H.map (MulAut.conj y₁).toMonoidHom
    let H₂ := H.map (MulAut.conj y₂).toMonoidHom
    let P₁ := stabilizer d.radical c ⊓ centralizer (H₁ : Set (FreeAmalgam d.radical))
    let P₂ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let D₁ := conjugateSpanBy (Z d.radical (act d.radical y₁⁻¹ (alpha d.radical))) P₁
    let D₂ := conjugateSpanBy (Z d.radical (act d.radical y₂⁻¹ (alpha d.radical))) P₂
    P₁ ⊔ Z d.radical z = stabilizer d.radical c →
    P₂ ⊔ Z d.radical z = stabilizer d.radical c →
    (¬ H₁ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
    (¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
    ⁅D₁,X d.radical z ⊓ Q d.radical c⁆ = ⁅D₂,X d.radical z ⊓ Q d.radical c⁆ := by
  dsimp only
  intro hgen₁ hgen₂ hmove₁ hmove₂
  let c := p.walk.getVert 2
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P (y : FreeAmalgam d.radical) := stabilizer d.radical c ⊓
    centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))
  let D (y : FreeAmalgam d.radical) :=
    conjugateSpanBy (Z d.radical (act d.radical y⁻¹ (alpha d.radical))) (P y)
  have hseed (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical c) :
      Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤ V d.radical c ∧
      ¬ Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤
        B d.radical c ((replacementGeometry h d).Z_normal _) := by
    constructor
    · have hl : p.walk.length = replacementDistance h d := p.length_eq_b
      have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
        le_iSup_of_le (alpha d.radical) (le_iSup_of_le
          (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
            (p.dist_start (by omega)).le) le_rfl)
      rw [Z_act,inv_inv]
      exact (map_mono hZV).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical c hy))
    · have hBm := mem_normalizer_iff_map_conj_eq.mp
        (Escape.Propagation.Rigidity.B_normalized (show 2 < replacementDistance h d by omega)
          _ q.start_color hy)
      intro hbad
      rw [Z_act,inv_inv,←hBm] at hbad
      have hstart := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hbad
      exact critical_start_not_le_second_slice s hc (by omega) p
        ((DistanceEight.U_le_Z d.radical _).trans hstart)
  have hDpre (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical c)
      (hgen : P y ⊔ Z d.radical z = stabilizer d.radical c)
      (hmove : ¬ H.map (MulAut.conj y).toMonoidHom ≤
        centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) :
      D y ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hD,_⟩ :=
      cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hindex
        z q.end_color hdist y hy hgen hmove
    rw [hpre]
    exact hD
  exact cube_generated_spans_full_kernel_eq s hc (by omega) u hR q hqsmall
    (D y₁) (P y₁) (D y₂) (P y₂)
    (conjugateSpanBy_le (hseed y₁ hy₁).1
      (inf_le_left.trans (DistanceEight.V_normalized d.radical c)))
    (conjugateSpanBy_le (hseed y₂ hy₂).1
      (inf_le_left.trans (DistanceEight.V_normalized d.radical c)))
    (hDpre y₁ hy₁ hgen₁ hmove₁) (hDpre y₂ hy₂ hgen₂ hmove₂)
    inf_le_left inf_le_left (le_normalizer_conjugateSpanBy _ _) (le_normalizer_conjugateSpanBy _ _)
    hgen₁ hgen₂
    (fun hh => (hseed y₁ hy₁).2 ((le_conjugateSpanBy _ _).trans hh))
    (fun hh => (hseed y₂ hy₂).2 ((le_conjugateSpanBy _ _).trans hh))

/-- The literal nonsylow small-slice configuration now has a kernel line
independent of every admissible shifted component choice. The same selected
Y and W lie in the actual endpoint stabilizer, so their full-X and full-kernel
displacements equal the corresponding seed displacements. All previously
selected paths, spans, small-mover joins and central attachments are retained.
This does not assert whole-starting-stabilizer centrality or the strict bound. -/
theorem nonsylow_small_shifted_kernel_independence_knownSimple
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
        (∃ x ∈ P,
          let w := act d.radical x⁻¹ a
          let t := act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))
          ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,A₀⁆ = R₃ ∧
          Adjacent d.radical w t ∧ Adjacent d.radical c t ∧
          SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 = Q d.radical t ∧
          SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = Q d.radical t ∧
          A₀ ≤ SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ∧
          R₃ ≤ Z d.radical t ∧
          R₃ ≤ centralizer
            ((SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ⊔
              SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
        ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
        ¬ ⁅D,X d.radical z⁆ ≤ R₃ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        R₃ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
          (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        ⁅Y,X d.radical z⁆ = ⁅Y,Z d.radical z⁆ ∧
        ⁅Y,A₀⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical c⁆ ∧
        ⁅conjugateSpanBy Y P,X d.radical z⁆ = ⁅conjugateSpanBy Y P,Z d.radical z⁆ ∧
        ⁅conjugateSpanBy Y P,A₀⁆ = ⁅conjugateSpanBy Y P,Z d.radical z ⊓ Q d.radical c⁆ ∧
        ∀ y' ∈ stabilizer d.radical c,
          let H' := H.map (MulAut.conj y').toMonoidHom
          let P' := stabilizer d.radical c ⊓ centralizer (H' : Set (FreeAmalgam d.radical))
          P' ⊔ Z d.radical z = stabilizer d.radical c →
          (¬ H' ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
          ⁅conjugateSpanBy (Z d.radical (act d.radical y'⁻¹ (alpha d.radical))) P',A₀⁆ = R₃ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,hselected,hfull,hnot,halign⟩ :=
    nonsylow_small_shifted_source_movers_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hslice hsmall
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hedge := critical_last_edge_inputs (h := h) hb2 q
  have hpreG : Q d.radical a' ≤ stabilizer d.radical z := by
    rw [←hpre]
    exact hedge.2.1.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hYdisp := critical_X_displacements_of_central_generation s hc q
    (hXall z q.end_color) _ (hYQ.trans hpreG)
  have hWdisp := critical_X_displacements_of_central_generation s hc q
    (hXall z q.end_color) _ (hWQ.trans hpreG)
  have hline := small_forward_slice_line_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 p hslice hsmall (critical_forward_not_le_slice_of_escape s hc hb2
      (nonsylow_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb hns) p)
  refine ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,hselected,hfull,hnot,halign,
    hYdisp.1,hYdisp.2,hWdisp.1,hWdisp.2,?_⟩
  intro y' hy'
  dsimp only
  intro hgen' hmove'
  exact cube_shifted_full_kernel_choice_independent s hc hb u hR p hsmall hline.1
    q hd hpre (by rw [hi]; decide) y' y hy' (Ltilde_le_stabilizer _ hy)
    hgen' hgen hmove' hmove

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
