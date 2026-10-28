module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Triple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Source

/-!
# Forward normality from selected residual spans

A moving pair has an actual common incident edge. Transport a selected
critical configuration to its starting vertex, then use the stabilizer to
move one of its escaping edges onto this common edge. Transport the whole
configuration and its centralizer equality by the same element. The prescribed
moving neighbor is now a genuine backward choice, including escape from the
new far kernel, so the residual-span theorem proves its normal product.

On the original critical geodesic, alpha belongs to nu(alpha+2): otherwise
the fixed-preimage condition would make Z_alpha Z_(alpha+2) normal, contrary
to (2.2)(iv). This gives the forward normal product. This deduction needs
only the residual spans, so the backward commutator bound used for the
preceding Z-containment is unnecessary here. The spans remain explicit
premises to be discharged by the source-theorem assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the last sentence of printed p.885, continued on p.886, in (4.3.2).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Reposition an actual escaping edge, retaining the selected configuration. -/
theorem moving_product_normal_of_spans (source : LocalSource L R)
    (p : Counterexample geometry) (selected : CentralizerChoice p)
    (spans : ∀ r : Counterexample geometry, CentralizerChoice r → ResidualSpanFacts r)
    {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) :
    ((Vcirc R a ⊔ Vcirc R d).subgroupOf (stabilizer R a)).Normal := by
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R a d hd.1
  obtain ⟨r, hra, ⟨sel⟩⟩ := exists_selected_at p selected a ha
  obtain ⟨old⟩ := (spans r sel).backward
  have hrt : Adjacent R r.a t := hra.symm ▸ hat
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R r.a old.adjacent_start hrt
  let q := translate r g
  have hqa : q.a = a := (show act R g r.a = r.a from hg).trans hra
  have hedge : ¬ edgeDisplacement q.a t ≤ Q R q.a' := by
    change ¬ edgeDisplacement (act R g r.a) t ≤ Q R (act R g r.a')
    rw [← hgt, edgeDisplacement, Q_act, Z_act, Q_act, ← map_commutator,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
    exact old.escapes
  let choice : BackwardChoice q := {
    edge := t
    back := d
    adjacent_start := hqa.symm ▸ hat
    adjacent_back := hdt
    moving := hqa.symm ▸ hd
    escapes := hedge }
  have hn := backward_product_normal source choice
    ((spans q (translateChoice sel g)).residual choice)
  change ((Vcirc R q.a ⊔ Vcirc R d).subgroupOf (stabilizer R q.a)).Normal at hn
  rw [hqa] at hn
  exact hn

/-- The printed assertion alpha belongs to nu(alpha+2), on the original path. -/
theorem start_moving_at_second (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) {s : Vertex R} (hs : Before p.a' p.a s 2) :
    p.a ∈ movingNeighbors geometry s := by
  have hsc : color R s = false := (hs.color (by decide)).trans p.color_a
  have has : (cosetGraph R).dist p.a s = 2 := by rw [SimpleGraph.dist_comm]; exact hs.1
  refine ⟨hs.1, ?_⟩
  intro hfixed
  have hnon := (critical_nonnormal_forward R geometry
    (source.adjacent_centralizer geometry.radical_ne_bot) p.a p.color_a
    (by rw [geometry.distance_constant p.a p.color_a]; exact lt_trans (by decide : 0 < 2) hb)
    p.a' p.critical s has (by
      simpa only [SimpleGraph.dist_comm] using hs.2)).2
  rw [modules.X_eq_Z s hsc] at hnon
  apply hnon
  have hV : V R s ≤ stabilizer R s :=
    (geometry.V_le_Q hb s hsc).trans (fun _ hx => hx.1)
  have hc : ⁅Z R p.a, Ltilde R s⁆ ≤ Z R s := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    exact ((mem_B_iff R s _ hV z).mp (hfixed hz)).2 l hl
  apply normal_subgroupOf_of_le_normalizer
  rw [sup_comm, ← source.local_generation s hsc]
  apply sup_le
  · exact normalizes_sup_of_commutator_le _ _ _
      ((Ltilde_le_stabilizer s).trans (Z_normalized R s)) hc
  · exact (le_inf
      ((show Q R s ≤ stabilizer R s from fun _ hx => hx.1).trans (Z_normalized R s))
      ((Q_le_stabilizer_of_dist_two R s p.a hsc hs.1).trans (Z_normalized R p.a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The forward product is normal; the residual spans already suffice. -/
theorem forward_product_normal_of_backward_bound (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) (selected : CentralizerChoice p)
    (spans : ∀ r : Counterexample geometry, CentralizerChoice r → ResidualSpanFacts r) :
    ∃ s, Before p.a' p.a s 2 ∧
      ((Vcirc R p.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal := by
  obtain ⟨s, hs⟩ := p.exists_before (Nat.sub_le (geometry.b R) 2)
  have hs' : Before p.a' p.a s 2 := by
    have hh := before_reverse hs
    simpa only [p.distance_eq_b, Nat.sub_sub_self (show 2 ≤ geometry.b R by omega)] using hh
  refine ⟨s, hs', ?_⟩
  rw [sup_comm]
  exact moving_product_normal_of_spans source p selected spans
    ((hs'.color (by decide)).trans p.color_a)
    (start_moving_at_second source hb modules p hs')

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
