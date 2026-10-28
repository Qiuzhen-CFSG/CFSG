module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Forward.Products

/-!
# Forward normality using an actual separating edge

Transport a selected critical configuration to the prescribed start and
construct a separating backward choice there. Stabilizer transitivity
moves its incident edge to the common edge of the prescribed moving pair.
The same element transports the complete counterexample, centralizer
choice, critical commutator and displacement. Replace only the backward
neighbor; the separation condition still holds since it depends on the edge.

The separating residual bound therefore proves normality for the prescribed
pair. On the original path, alpha lies in nu(alpha+2). Transport of the
contrary hypothesis supplies all source packages used along the way.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), the end of printed
p.885 and beginning of p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R}

omit [Finite M] in
/-- Both the critical line and displacement move by the same inverse conjugation. -/
theorem critical_avoidance_act_iff (g : FreeAmalgam R) (a a' t : Vertex R) :
    (¬ criticalCommutator (act R g a) (act R g a') ≤
      edgeDisplacement (act R g a) (act R g t)) ↔
    ¬ criticalCommutator a a' ≤ edgeDisplacement a t := by
  rw [FirstPairing.edgeDisplacement_act, criticalCommutator, Z_act, Z_act,
    ← map_commutator, map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  rfl

/-- Move both backward vertices and the whole counterexample together. -/
private def translateBackwardChoice (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (choice : BackwardChoice p) (g : FreeAmalgam R) :
    BackwardChoice (Continuation.translate p g) where
  edge := act R g choice.edge
  back := act R g choice.back
  adjacent_start := (adjacent_act_iff R g p.a choice.edge).mpr choice.adjacent_start
  adjacent_back := (adjacent_act_iff R g choice.back choice.edge).mpr choice.adjacent_back
  moving := (FirstPairing.movingNeighbors_act_iff hb g p.a choice.back p.color_a).mpr
    choice.moving
  escapes := by
    change ¬ edgeDisplacement (act R g p.a) (act R g choice.edge) ≤ Q R (act R g p.a')
    rw [FirstPairing.edgeDisplacement_act, Q_act,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
    exact choice.escapes

/-- Reposition a separating edge, then replace only its backward moving neighbor. -/
theorem moving_product_normal_of_residualFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry) (selected : CentralizerChoice p)
    (spans : ∀ r : Counterexample geometry, CentralizerChoice r → ResidualFacts r)
    {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) :
    ((Vcirc R a ⊔ Vcirc R d).subgroupOf (stabilizer R a)).Normal := by
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R a d hd.1
  obtain ⟨r, hra, ⟨sel⟩⟩ := Continuation.exists_selected_at p selected a ha
  obtain ⟨old, hsep⟩ := (spans r sel).backward
  have hrt : Adjacent R r.a t := hra.symm ▸ hat
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R r.a old.adjacent_start hrt
  let q := Continuation.translate r g
  have hqa : q.a = a := (show act R g r.a = r.a from hg).trans hra
  let moved : BackwardChoice q := translateBackwardChoice hb old g
  have hme : moved.edge = t := hgt
  have hmsep : ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a moved.edge :=
    (critical_avoidance_act_iff g r.a r.a' old.edge).mpr hsep
  let choice : BackwardChoice q := {
    moved with
    back := d
    adjacent_back := hme.symm ▸ hdt
    moving := hqa.symm ▸ hd }
  have hn := backward_product_normal source choice
    ((spans q (Continuation.translateChoice sel g)).residual choice hmsep)
  change ((Vcirc R q.a ⊔ Vcirc R d).subgroupOf (stabilizer R q.a)).Normal at hn
  rw [hqa] at hn
  exact hn

/-- Source inputs give normality for every prescribed moving pair. -/
theorem moving_product_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p)
    {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) :
    ((Vcirc R a ⊔ Vcirc R d).subgroupOf (stabilizer R a)).Normal := by
  have spans : ∀ r : Counterexample geometry, CentralizerChoice r → ResidualFacts r :=
    fun r sel => residual_facts source hb modules transfer initial facts r
      (bad_at hb p.color_a bad r.a r.color_a) hlarge sel
  exact moving_product_normal_of_residualFacts source hb p selected spans ha hd

/-- The original forward product, with every separating residual premise discharged. -/
theorem forward_product_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p) :
    ∃ s, Before p.a' p.a s 2 ∧
      ((Vcirc R p.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal := by
  obtain ⟨s, hs⟩ := p.exists_before (Nat.sub_le (geometry.b R) 2)
  have hs' : Before p.a' p.a s 2 := by
    have hh := before_reverse hs
    simpa only [p.distance_eq_b, Nat.sub_sub_self (show 2 ≤ geometry.b R by omega)] using hh
  refine ⟨s, hs', ?_⟩
  rw [sup_comm]
  exact moving_product_normal source hb modules transfer initial facts p bad hlarge selected
    ((hs'.color (by decide)).trans p.color_a)
    (Continuation.start_moving_at_second source hb modules p hs')

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
