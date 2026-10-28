module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeForwardLine

/-!
# Strict small-image forward slices for the mixed-plane replacement

Above critical distance four, a small critical pair in the mixed-plane
branch has forward Baumann index greater than two. The established radius
escape extends the actual critical walk. If its forward slice had index
two, the full-cover forward line would choose one component conjugator
that supplies both local generation and noncentrality. The cover-aware
shifted-span theorem then traps both centralizer orbit spans in the old
endpoint core and makes the extended critical image small.

The seed orbit span has a nonzero commutator with the full reverse seed
kernel: otherwise its generating centralizer and endpoint would put it
in the Baumann subgroup. Hence one conjugate seed has a nonzero
commutator. The established bound on the whole predecessor core gives
that commutator order two. The same conjugate of the shifted normal span
has displacement inside that line. Normal-section control therefore
places the reverse actor in the starting core, contradicting the seed
witness. This uses point-core containment only; no equality with that
point core or identification of the whole core with a selected span is
made.

Transport gives the strict inequality at every original component vertex.
Its application discharges the strict-slice premise of the actual
mixed-plane backward construction, retaining the relative-normalizer
join, both transporters, the slice index and every overlapping vertex.
The original radical, minimum characteristic replacement, natural graph,
quotient maps, central attachments and both covers of orders sixteen and
thirty-two are unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.7)--(5.9), printed pp.866--867 and 919--922. The proof
uses the seed-kernel witness route to the strict inequality. Large critical
images, the terminal exclusions, larger Sylow images and distance four
remain obligations of the large-distance source assembly.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement Pointwise
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedStrict
local notation "S" => Equiv.Perm (Fin 6)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem generated_radius_le_slice
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (D P A : Subgroup (FreeAmalgam d.radical))
    (hDV : D ≤ V d.radical a) (hPG : P ≤ stabilizer d.radical a)
    (hAG : A ≤ stabilizer d.radical a) (hne : ¬ A ≤ Q d.radical a)
    (hPN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ A = stabilizer d.radical a) (hcomm : ⁅D,A⁆ ≤ Z d.radical a) :
    D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
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
  exact le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb ha N A
    hNV hGN hAG hne hNA)

include s in
private theorem point_contained_small_forward_strict
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < replacementDistance h d := by omega
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hel := critical_forward_not_le_slice_of_escape s hc hb2 hesc p
  have hline := small_forward_slice_line_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 p hslice hsmall hel
  obtain ⟨z,q,hd,hover,hpre⟩ := critical_forward_extension_of_escape s hc hb2 hesc p
  have hi := small_slice_forward_extension_index_two s hc hb p hsmall hslice hel q hd hpre
  have hqsmall : (Q d.radical z).relIndex (Z d.radical c) < 4 := by rw [hi]; decide
  obtain ⟨y,hy,hgen,hmove⟩ := exists_cover_line_generator s hc q H hHU
    hline.2.1 hline.2.2.2.2
  obtain ⟨_,_,_,_,hYV,hYN,hYB,_,_,_,_,_,_,hDQ,hWQ⟩ :=
    cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hline.1
      z q.end_color hd y (Ltilde_le_stabilizer _ hy) hgen hmove
  let a := act d.radical y⁻¹ (alpha d.radical)
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let K := Z d.radical z ⊓ Q d.radical c
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c :=
      (stabilizer d.radical c).inv_mem (Ltilde_le_stabilizer c hy)
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  have hZaV : Z d.radical a ≤ V d.radical c := by
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ (Ltilde_le_stabilizer _ hy)))
  have hZaB : ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) := by
    have hBm := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized hb2 c q.start_color (Ltilde_le_stabilizer _ hy))
    intro he
    rw [Z_act,inv_inv,←hBm] at he
    exact critical_start_not_le_second_slice s hc hb2 p
      ((DistanceEight.U_le_Z d.radical _).trans
        ((map_le_map_iff_of_injective (MulAut.conj y).injective).mp he))
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le hZaV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  have hJne : ⁅D,K⁆ ≠ ⊥ := by
    intro he
    have hcomm := small_critical_predecessor_commutator s hc hb2 q hqsmall D hDpre
      (commutator_eq_bot_iff_le_centralizer.mp he)
    have hDB := generated_radius_le_slice s hb2 q.start_color D P (Z d.radical z)
      hDV inf_le_left
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
        rw [(replacementGeometry h d).distance_constant c q.start_color]
        exact replacementDistance_pos h d) q.critical)
      (critical_reverse_pair s hc q).2 (le_normalizer_conjugateSpanBy _ _) hgen hcomm
    exact hZaB ((le_conjugateSpanBy _ _).trans hDB)
  have hex : ∃ x : P, ⁅(Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom,K⁆ ≠ ⊥ := by
    by_contra! hzero
    apply hJne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [show D = conjugateSpanBy (Z d.radical a) P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => commutator_eq_bot_iff_le_centralizer.mp (hzero x))
  obtain ⟨x,hx⟩ := hex
  have hZxD : (Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom ≤ D := by
    rw [show D = conjugateSpanBy (Z d.radical a) P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z d.radical a).map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hYxW : Y.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hvcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    rw [hpre]
    exact p.end_color
  have hvz : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) z ≤ 2 := by
    rw [hpre,hd]
  have hNZ : ⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆ ≤ Z d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_stabilizer_of_dist_le_two _ _ hvcol q.end_color hvz).trans (Z_normalized d.radical z)))
  have hsub : ⁅(Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom,K⁆ ≤
      ⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆ := by
    rw [commutator_comm ((Z d.radical a).map _)]
    exact commutator_mono le_rfl (hZxD.trans hDpre)
  let := finite_Z d.radical z
  let : Finite (⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  let : Finite (⁅(Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom,K⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hsub.trans hNZ)) (inclusion_injective _)
  have hcard : Nat.card (⁅(Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    have hbound := (card_le_of_le hsub).trans (small_critical_kernel_predecessor_card s hc hb2 u hR q hqsmall)
    have hpos := (one_lt_card_iff_ne_bot _).mpr hx
    omega
  apply predecessor_seed_witness_false s hc hb2 u hR q hqsmall ha hca.le
    Y hYV hYN hYB x x.property.1 (hZxD.trans hDpre)
  · rw [hpre]
    exact hYxW.trans hWQ
  · exact hcard

/-- The mixed-plane small-critical-image forward slice is strict above
critical distance four, on either full moving cover. -/
theorem mixed_small_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  exact point_contained_small_forward_strict s hc hb u hR
    (MixedEscape.mixed_criticalEscape_knownSimple (by omega) u him) p hsmall

/-- Vertex-transitive transport of the strict forward slice uses the same
critical walk, second vertex and Baumann subgroup. -/
theorem mixed_small_forward_slice_strict_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := mixed_small_forward_slice_strict_knownSimple hb u him p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

/-- The actual mixed-plane backward construction has its strict-slice
premise discharged for a small critical pair. Both original transporters,
the slice index and all shared path vertices are retained. -/
theorem mixed_small_backward_path_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x (p.walk.getVert 2)))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) =
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (p.walk.getVert 2)) ∧
            2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
  have hstrict := mixed_small_forward_slice_strict_knownSimple hb u him p hsmall
  obtain ⟨t,hat,hgen,x,hx,hxt,k,hk,q,hq1,hover,hidx⟩ :=
    MixedEscape.mixed_strict_backward_path_knownSimple (by omega) u him p
      (adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by
          have hl : p.walk.length = replacementDistance h d := p.length_eq_b
          omega)))) hstrict
  exact ⟨t,hat,hgen,x,hx,hxt,k,hk,q,hq1,hover,hidx,hidx ▸ hstrict⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedStrict
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
