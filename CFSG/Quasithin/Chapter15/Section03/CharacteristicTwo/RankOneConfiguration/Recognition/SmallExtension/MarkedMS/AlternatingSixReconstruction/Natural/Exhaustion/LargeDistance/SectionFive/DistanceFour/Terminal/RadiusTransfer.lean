module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusDerived
public import Theory.SpecificGroups.SymmetricSix.NormalGeneration
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.PResidual.NormalSubgroup


/-!
# Residual fixedness of the full radius-core commutator

A fixed-core bound on [V_alpha^circ,Q_alpha] extends to [V_alpha,Q_alpha]
in the actual symmetric-six replacement. For each radius-two seed Z_c,
its common edge kernel and the starting residual generate the local group.
The first bound makes [Z_c,Q_alpha] D_alpha normal there. If Q_c escapes
Q_alpha, its normal closure contains the actual residual by normal generation
in S6; otherwise equal kernel orders make its seed movement trivial.
Residual commutator idempotence removes the central error. Taking the join
over the radius generators gives the full-radius conclusion.

The natural-cover application discharges the moving-radius premise using
the same large critical path. It retains every radical image and does not
assume a chosen Sylow. The order-thirty-two moving-cover premise and the
subsequent reciprocal-span, FF and Thompson arguments remain separate.
In particular this module does not assert the large-slice contradiction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.2)(ii), printed p.882, and the first reduction of (5.12)(2),
printed p.925. The local argument adapts SectionThree.NormalizationTransfer,
using the incident edge kernel for generation in place of the SL3 quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
namespace RadiusTransfer
variable {G : Type*} [Group G]

private theorem commutator_normalized_of_triple_eq_bot
    (A V Y L : Subgroup G) [Y.Normal] (hAV : A ≤ V)
    (htriple : ⁅⁅V,L⁆,Y⁆ = ⊥) : L ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a, ha, y, hy, rfl⟩
  have hy' : l * y * l⁻¹ ∈ Y := (inferInstance : Y.Normal).conj_mem y hy l
  have hc : ⁅l,a⁆ ∈ ⁅V,L⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl (hAV ha)
  have hcy : Commute ⁅l,a⁆ (l * y * l⁻¹) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _ hy').symm
  have hck : Commute ⁅l,a⁆ ⁅a,l * y * l⁻¹⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _
      (commutator_le_right A Y (commutator_mem_commutator ha hy'))).symm
  rw [conjugate_commutatorElement, show l * a * l⁻¹ = ⁅l,a⁆ * a by
    simp [commutatorElement_def, mul_assoc]]
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq,
    hck.eq, mul_inv_cancel_right, mul_one]
  exact commutator_mem_commutator ha hy'

private theorem normalizes_commutator (B A Y : Subgroup G)
    (hBA : B ≤ normalizer A) (hBY : B ≤ normalizer Y) :
    B ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hBA hb),
    mem_normalizer_iff_map_conj_eq.mp (hBY hb)]

/-- The quotient argument used on one radius-two generator. -/
private theorem generator_transfer [Finite G]
    (Q L V Y A J T : Subgroup G) [Q.Normal] [L.Normal] [Y.Normal]
    (hpQ : IsPGroup 2 Q) (hpL : IsPPerfect 2 L)
    (hcover : T ⊔ L = ⊤) (hVQ : V ≤ Q) (hYQ : Y ≤ Q) (hAV : A ≤ V)
    (hQA : Q ≤ normalizer A) (hTA : T ≤ normalizer A)
    (htriple : ⁅⁅V,L⁆,Y⁆ ≤ Q ⊓ centralizer (L : Set G))
    (hAJ : ⁅A,J⁆ = ⊥) (hclosure : L ≤ normalClosure (J : Set G)) :
    ⁅A,Y⁆ ≤ Q ⊓ centralizer (L : Set G) := by
  let D := Q ⊓ centralizer (L : Set G)
  have hDcentral : ⁅D,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hYA : Y ≤ normalizer A := hYQ.trans hQA
  let K := ⁅A,Y⁆
  let N := K ⊔ D
  let q := QuotientGroup.mk' D
  have hKQ : K ≤ Q :=
    (le_normalizer_iff_commutator_le_left.mp hYA).trans (hAV.trans hVQ)
  have hNQ : N ≤ Q := sup_le hKQ inf_le_left
  have hNmap : N.map q = K.map q := by
    simp [N, Subgroup.map_sup, q]
  have hpreimage : (K.map q).comap q = N := by
    simp [comap_map_eq, q, N]
  have hLnorm : L ≤ normalizer N := by
    have hzero : ⁅⁅V.map q,L.map q⁆,Y.map q⁆ = ⊥ := by
      rw [← map_commutator, ← map_commutator, Subgroup.map_eq_bot_iff]
      simpa only [q, QuotientGroup.ker_mk'] using htriple
    let : (Y.map q).Normal := (inferInstance : Y.Normal).map q
      (QuotientGroup.mk'_surjective D)
    have hn := commutator_normalized_of_triple_eq_bot (A.map q) (V.map q)
      (Y.map q) (L.map q) (map_mono hAV) hzero
    rw [← map_commutator] at hn
    have hh := (map_le_iff_le_comap.mp hn).trans
      (le_normalizer_comap q)
    rwa [hpreimage] at hh
  have hTnorm : T ≤ normalizer N := by
    apply (le_inf (normalizes_commutator T A Y hTA le_normalizer_of_normal)
      (le_normalizer_of_normal (H := D))).trans
    exact normalizer_inf_normalizer_le_normalizer_sup K D
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique
    (hcover ▸ sup_le hTnorm hLnorm))
  have hNJ : ⁅N,J⁆ ≤ D := by
    have hc : ⁅K,J⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (commutator_mono
        (le_normalizer_iff_commutator_le_left.mp hYA)
        le_rfl).trans hAJ.le
    have hm : (⁅N,J⁆).map q = ⊥ := by
      rw [map_commutator, hNmap, ← map_commutator, hc, Subgroup.map_bot]
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
  have hNL : ⁅N,L⁆ ≤ D := (commutator_mono le_rfl hclosure).trans
    (commutator_normalClosure_le_of_normal N J D hNJ)
  have hNLzero : ⁅N,L⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent L N hpL (hpQ.to_le hNQ) hLnorm]
    exact le_bot_iff.mp ((commutator_mono hNL le_rfl).trans hDcentral.le)
  exact le_inf hKQ (le_sup_left.trans (commutator_eq_bot_iff_le_centralizer.mp hNLzero))

private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer D) (hc : ∀ i, ⁅A i,Y⁆ ≤ D) :
    ⁅⨆ i, A i,Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)

end RadiusTransfer

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem transfer_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include h in
private theorem fixedCore_comap_base :
    (fixedCore d.radical (alpha d.radical)).comap (embedM d.radical) =
      pCore 2 d.overgroup ⊓ centralizer (pResidual 2 d.overgroup : Set d.overgroup) := by
  ext x
  constructor
  · intro hx
    refine ⟨?_,?_⟩
    · have hh : x ∈ (Q d.radical (alpha d.radical)).comap (embedM d.radical) := hx.1
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    · intro l hl
      apply embedM_injective d.radical
      simpa only [map_mul] using hx.2 (embedM d.radical l)
        (by rw [Ltilde_alpha]; exact mem_map_of_mem _ hl)
  · rintro ⟨hx,hc⟩
    refine ⟨?_,?_⟩
    · rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)]
      exact mem_map_of_mem _ hx
    · intro l hl
      rw [Ltilde_alpha] at hl
      obtain ⟨l,hl,rfl⟩ := hl
      simpa only [map_mul] using congrArg (embedM d.radical) (hc l hl)

include s in
private theorem radius_generator_core_fixed
    (hb : 2 < replacementDistance h d)
    (hmove : ⁅Vcirc d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (c : Vertex d.radical) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) :
    ⁅Z d.radical c,Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let a := alpha d.radical
  let f := embedM d.radical
  have hQa : Q d.radical a ≤ stabilizer d.radical a := fun _ hx => hx.1
  have hQc : Q d.radical c ≤ stabilizer d.radical a :=
    Q_le_stabilizer_of_dist_le_two c a hc rfl hd
  have hQac : Q d.radical a ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_le_two a c rfl hc (by rwa [SimpleGraph.dist_comm])
  have hAV : Z d.radical c ≤ V d.radical a := le_iSup_of_le c (le_iSup_of_le hd le_rfl)
  have hVQ := (replacementGeometry h d).V_le_Q hb a rfl
  have hAS := hAV.trans (hVQ.trans hQa)
  have hQm : (pCore 2 d.overgroup).map f = Q d.radical a :=
    (Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)).symm
  have hLm : (pResidual 2 d.overgroup).map f = Ltilde d.radical a := (Ltilde_alpha d.radical).symm
  have hr : f.range = stabilizer d.radical a := (stabilizer_m_base d.radical).symm
  let A := (Z d.radical c).comap f
  let J := (Q d.radical c).comap f
  let V₀ := (V d.radical a).comap f
  let D := pCore 2 d.overgroup ⊓ centralizer (pResidual 2 d.overgroup : Set d.overgroup)
  have hAm : A.map f = Z d.radical c := map_comap_eq_self (hAS.trans_eq hr.symm)
  have hJm : J.map f = Q d.radical c := map_comap_eq_self (hQc.trans_eq hr.symm)
  have hDm : D.map f = fixedCore d.radical a := by
    dsimp only [D]
    rw [←fixedCore_comap_base (h := h) (d := d)]
    exact map_comap_eq_self ((inf_le_left.trans hQa).trans_eq hr.symm)
  by_cases hle : Q d.radical c ≤ Q d.radical a
  · let := finite_stabilizer d.radical a
    let : Finite (Q d.radical a) := Finite.of_injective (inclusion hQa) (inclusion_injective hQa)
    have he : Q d.radical c = Q d.radical a := eq_of_le_of_card_ge hle (by
      rw [SourceReduction.Radius.Q_card h d c hc,SourceReduction.Radius.Q_card h d a rfl])
    rw [←he,Z_centralizes_Q d.radical c hc]
    exact bot_le
  have hne : c ≠ a := by
    intro he
    exact hle (he ▸ le_rfl)
  have htwo : (cosetGraph d.radical).dist a c = 2 := by
    obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a c
    have hev : Even w.length := (walk_even_iff_color_eq d.radical w).mpr hc.symm
    have hn : (cosetGraph d.radical).dist a c ≠ 0 := fun hh =>
      hne ((cosetGraph_connected d.radical).dist_eq_zero_iff.mp hh).symm
    rw [hw,Nat.even_iff] at hev
    change (cosetGraph d.radical).dist c a ≤ 2 at hd
    rw [SimpleGraph.dist_comm] at hd
    omega
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two d.radical a c htwo
  let T := (Q d.radical t).comap f
  have hTa : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hTc : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hTm : T.map f = Q d.radical t := map_comap_eq_self (hTa.trans_eq hr.symm)
  have hgen : T ⊔ pResidual 2 d.overgroup = ⊤ := by
    apply (map_injective (embedM_injective d.radical))
    rw [Subgroup.map_sup,hTm,hLm,←MonoidHom.range_eq_map,hr]
    exact (sup_comm _ _).trans (transfer_residual_edge_generation (h := h) rfl hat)
  have hQA : pCore 2 d.overgroup ≤ normalizer A := by
    have hh := (comap_mono (f := f) (hQac.trans (Z_normalized d.radical c))).trans
      (le_normalizer_comap f)
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hTA : T ≤ normalizer A :=
    (comap_mono (hTc.trans (Z_normalized d.radical c))).trans (le_normalizer_comap f)
  have hVP : V₀ ≤ pCore 2 d.overgroup := by
    have hh := comap_mono (f := f) hVQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have htriple : ⁅⁅V₀,pResidual 2 d.overgroup⁆,pCore 2 d.overgroup⁆ ≤ D := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [map_commutator,map_commutator,radius_comap_map (h := h) hb,hLm,hQm,hDm]
    exact hmove
  have hAJ : ⁅A,J⁆ = ⊥ := by
    apply (map_injective (embedM_injective d.radical))
    rw [map_commutator,hAm,hJm,Z_centralizes_Q d.radical c hc,Subgroup.map_bot]
  have hJ : J.map s.projection ≠ ⊥ := by
    intro hzJ
    have hj := (map_eq_bot_iff J).mp hzJ
    rw [s.projection_kernel] at hj
    have hh := map_mono (f := f) hj
    exact hle (by rwa [hJm,hQm] at hh)
  have hclosure : pResidual 2 d.overgroup ≤ normalClosure (J : Set d.overgroup) :=
    Theory.SpecificGroups.SymmetricSix.perfect_le_normalClosure_of_nontrivial_image
      s.projection (by rw [s.projection_kernel]; exact pCore_isPGroup)
      (by rw [MonoidHom.range_eq_top.mpr s.surjective]; exact le_top)
      (pResidual 2 d.overgroup) J (isPPerfect_pResidual 2)
      (by rw [replacement_residual h d,s.component_image]) hJ
  have hh := RadiusTransfer.generator_transfer
    (pCore 2 d.overgroup) (pResidual 2 d.overgroup) V₀ (pCore 2 d.overgroup) A J T
    pCore_isPGroup (isPPerfect_pResidual 2) hgen hVP le_rfl (comap_mono hAV)
    hQA hTA htriple hAJ hclosure
  have hm := map_mono (f := f) hh
  rwa [map_commutator,hAm,hQm,hDm] at hm

include s in
/-- Transfer fixedness from the moving radius to the whole radius through
the actual symmetric-six quotient and the incident edge groups. -/
theorem radius_core_fixed_of_moving_core_fixed
    (hb : 2 < replacementDistance h d)
    (hmove : ⁅Vcirc d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let D := fixedCore d.radical (alpha d.radical)
  have hn : V d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((replacementGeometry h d).V_local _ rfl hb).trans (fixedCore_normalized d.radical _)
  apply RadiusTransfer.commutator_iSup_le_of_normalizes _ _ _ hn
  intro c
  apply RadiusTransfer.commutator_iSup_le_of_normalizes
  · apply iSup_le
    intro hd
    exact (le_iSup_of_le c (le_iSup_of_le hd le_rfl) :
      Z d.radical c ≤ V d.radical (alpha d.radical)).trans hn
  · intro hd
    by_cases hc : color d.radical c = false
    · exact radius_generator_core_fixed s hb hmove c hc hd
    · have hc' : color d.radical c = true := Bool.eq_true_of_not_eq_false hc
      obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c (alpha d.radical)
      have hev : ¬ Even w.length := by
        rw [walk_even_iff_color_eq,hc']
        change ¬ true = false
        decide
      have hlen : w.length = 1 := by
        have hh := hw.trans_le hd
        rw [Nat.even_iff] at hev
        omega
      have hac := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp (w.adj_of_length_eq_one hlen))
      have hZ : Z d.radical c ≤ Z d.radical (alpha d.radical) := adjacent_Z_le d.radical rfl hac
      exact (commutator_mono hZ le_rfl).trans
        ((Z_centralizes_Q d.radical (alpha d.radical) rfl).le.trans bot_le)


include e hz hn in
/-- For the natural cover and a large critical image, the full radius-core
commutator is fixed by the actual starting residual. -/
theorem natural_large_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  exact radius_core_fixed_of_moving_core_fixed
    (fullSymmetricAction_knownSimple h e hz hn d (by omega)) (by omega)
    (natural_large_moving_radius_core_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hnat p hlarge)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
