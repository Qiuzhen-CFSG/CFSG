module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection.Sections

/-!
# The actual element and flag for the first MS93 quotient pairing

The earlier nontrivial H gives a radius-two Z-layer outside B. Choose an
actual element there. The full natural section selects a flag fixing that
element modulo Z[V,Q], which lies in B by the section's triple commutator
bound. The inner relative marking carries the same flag's nonzero fixed
vector to the actual Z-image in G_alpha/D_alpha. Both assertions hold for
the full parabolic, hence for its untilded local residual.

The moving-neighbor existence argument is adapted from
Escape/Propagation/Rigidity/Moving.lean, but uses only (4.3.1)(vi).
No later propagation or pairing conclusion enters this proof.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem moving_element (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (initial : InitialFacts p) :
    ∃ (d : Vertex R) (x : stabilizer R p.a),
      d ∈ movingNeighbors geometry p.a ∧
      (x : FreeAmalgam R) ∈ Z R d ∧
      (x : FreeAmalgam R) ∉ B R p.a (geometry.Z_normal p.a) := by
  have hV : V R p.a ≤ stabilizer R p.a :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hnot : ¬ V R p.a ≤ B R p.a (geometry.Z_normal p.a) := by
    intro h
    have hcirc : Vcirc R p.a ≤ Z R p.a := by
      rw [Vcirc, commutator_comm]
      apply commutator_le.mpr
      intro l hl v hv
      exact ((mem_B_iff R p.a (geometry.Z_normal p.a) hV v).mp (h hv)).2 l hl
    have hbot : H R p.a = ⊥ := le_bot_iff.mp (by
      rw [← Z_centralizes_Q R p.a p.color_a]
      exact commutator_mono hcirc le_rfl)
    have hc := initial.H_card
    rw [hbot, card_bot] at hc
    omega
  have hd : ∃ d, d ∈ movingNeighbors geometry p.a := by
    by_contra! h
    apply hnot
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    have hdist : (cosetGraph R).dist p.a d ≤ 2 := by rwa [SimpleGraph.dist_comm]
    by_cases h0 : (cosetGraph R).dist p.a d = 0
    · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp h0
      subst d
      exact EdgeTransfer.Z_le_B hb p.a p.color_a
    by_cases h1 : (cosetGraph R).dist p.a d = 1
    · have hadj : Adjacent R p.a d := (cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact (EdgeTransfer.edge_Z_le p.a d p.color_a hadj).trans
        (EdgeTransfer.Z_le_B hb p.a p.color_a)
    · have h2 : (cosetGraph R).dist p.a d = 2 := by omega
      exact of_not_not (fun hn => h d ⟨h2, hn⟩)
  obtain ⟨d, hd⟩ := hd
  obtain ⟨x, hx, hxb⟩ := Set.not_subset.mp hd.2
  exact ⟨d, ⟨x, hV (moving_Z_le_V hd hx)⟩, hd, hx, hxb⟩

/-- The original radical Z[V,Q] lies in the literal fixed preimage B.
This uses the full section's triple clause and relative normality. -/
theorem radical_le_B (hb : 2 < geometry.b R) {a : Vertex R}
    (ha : color R a = false) (f : FrameAt a) :
    radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
      ((V R a).subgroupOf (stabilizer R a))
      ((Z R a).subgroupOf (stabilizer R a)) ≤
      (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a) := by
  let := f.natural_section.normal_group
  let := geometry.Z_normal a
  apply sup_le
  · exact fun _ hx => EdgeTransfer.Z_le_B hb a ha hx
  · intro x hx
    change (x : FreeAmalgam R) ∈ B R a (geometry.Z_normal a)
    apply mem_map_of_mem (stabilizer R a).subtype
    apply mem_centralizerModulo_iff.mpr
    refine ⟨commutator_le_left _ _ hx, ?_⟩
    intro l hl
    apply f.natural_section.triple_le
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx

omit [Finite M] in
private theorem parabolic_quotient_image {a : Vertex R} (f : FrameAt a)
    (flag : SL) (side : Bool) :
    (parabolic f.projection flag side).map (quotientMap a) =
      parabolic (projection f) flag side := by
  have hpre : parabolic f.projection flag side =
      (parabolic (projection f) flag side).comap (quotientMap a) := rfl
  rw [hpre]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- The element-and-flag selection of original MS93 (4.3.2)(2), with the
actual Z-image, full radical denominator and untilded local residual. -/
theorem selectedSeed_nonempty (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (_transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (p : Counterexample geometry) (_bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (f : FrameAt p.a) (same : f.SameOrientation) :
    Nonempty (SelectedSeed geometry p.a f) := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨d, x, hd, hx, hxb⟩ := moving_element hb p hi
  obtain ⟨flag, side, w, hw, hfixed, hcomm⟩ :=
    section_fixed_flag f.natural_section x (moving_Z_le_V hd hx)
  let P := parabolic (projection f) flag side
  have hLP : localResidual P ≤ P := map_subtype_le _
  have hfixedZ : quotientImage p.a (Z R p.a) ⊓
      centralizer (P : Set (LocalQuotient p.a)) ≠ ⊥ := by
    apply fixed_subgroup_of_inner (naturalZ modules p.a p.color_a f)
      f.natural_section.natural.marking same w hw
    intro a ha
    exact hfixed ((projection f) a) ha
  have hc : ⁅zpowers (quotientMap p.a x), P⁆ ≤
      quotientImage p.a (B R p.a (geometry.Z_normal p.a)) := by
    have hm := map_mono (f := quotientMap p.a)
      (hcomm.trans (radical_le_B hb p.color_a f))
    rw [map_commutator, MonoidHom.map_zpowers, parabolic_quotient_image] at hm
    exact hm
  refine ⟨{
    neighbor := d
    moving := hd
    element := x
    element_mem := hx
    outside := hxb
    flag := flag
    weakBN := binaryWeakBN flag
    side := side
    fixed_Z := ?_
    fixes_seed := (commutator_mono le_rfl hLP).trans hc }⟩
  intro hbot
  apply hfixedZ
  exact le_bot_iff.mp ((inf_le_inf_left _ (centralizer_le hLP)).trans hbot.le)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
