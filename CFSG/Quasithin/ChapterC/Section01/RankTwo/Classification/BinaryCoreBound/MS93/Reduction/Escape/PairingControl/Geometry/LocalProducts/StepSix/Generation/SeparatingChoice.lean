module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Choice

/-!
# Choosing an edge that separates the critical line

The intersection of the natural order-eight group with the endpoint kernel
is proper by faithfulness of the natural action. It contains the critical
commutator line. Consequently an incident order-four displacement contained
in that kernel must contain the critical line as well.

The intersection of all incident displacements is trivial. Choose one
omitting the nontrivial critical line; the preceding cardinal argument gives
its escape from the endpoint kernel. Local transitivity supplies a moving
backward neighbor at this actual edge. No generation conclusion or separation
premise is assumed by the producer.

Source: Meierfrankenfeld--Stellmacher (1993), the choices before (4.3.2)(6),
printed p.885, using the natural-layer and order assertions on pp.881--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- A plane in the endpoint kernel contains the critical line. -/
theorem edge_critical_le_of_le_endpoint_kernel (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (q : Counterexample geometry) (hb : 2 < geometry.b R)
    {t : Vertex R} (hat : Adjacent R q.a t)
    (hEQ : edgeDisplacement q.a t ≤ Q R q.a') :
    criticalCommutator q.a q.a' ≤ edgeDisplacement q.a t := by
  let E := edgeDisplacement q.a t
  let C := U R q.a ⊓ Q R q.a'
  have hUcard := modules.natural.card_at q.a q.color_a
  let : Finite (U R q.a) := Nat.finite_of_card_ne_zero (by rw [hUcard]; decide)
  let : Finite C := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hEC : E ≤ C := le_inf (Initial.edge_le_natural source _ _ q.color_a hat) hEQ
  have hEcard : Nat.card E = 4 := FirstPairing.StepThree.edge_card q (by omega)
    initial q.a t q.color_a hat
  have hlarge : 4 ≤ Nat.card C := hEcard ▸ card_le_of_le hEC
  have hdvd : Nat.card C ∣ 8 := hUcard ▸ card_dvd_of_le (show C ≤ U R q.a from inf_le_left)
  have hne : Nat.card C ≠ 8 := by
    intro hc
    have he : C = U R q.a := eq_of_le_of_card_ge inf_le_left (by rw [hc, hUcard])
    exact natural_not_le_endpoint_kernel source modules q (he ▸ inf_le_right)
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have he : E = C := eq_of_le_of_card_ge hEC (by omega)
  change criticalCommutator q.a q.a' ≤ E
  rw [he]
  apply le_inf
  · exact (commutator_mono le_rfl q.end_Z_le_start_stabilizer).trans
      (Initial.Z_commutator_stabilizer source q.a q.color_a).le
  · exact (q.critical_le_radius_inf_start.trans inf_le_left).trans
      (q.radius_le_end.trans ((Z_le_VBall R q.a' 2).trans
        (geometry.V_le_Q hb q.a' q.end_color)))

/-- Choose an actual incident edge avoiding the critical line, then any moving
neighbor at that edge. -/
theorem exists_separating_backwardChoice (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (q : Counterexample geometry) (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a) :
    ∃ choice : BackwardChoice q,
      ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge := by
  obtain ⟨iq⟩ := initial q
  have hne : criticalCommutator q.a q.a' ≠ ⊥ := by
    intro h
    have hc := iq.critical_card
    rw [h] at hc
    simp at hc
  obtain ⟨t, hat, hsep⟩ := exists_avoiding_edge source hb modules facts q.color_a
    (criticalCommutator q.a q.a') hne
  obtain ⟨d, hdt, hd⟩ := exists_moving_at_edge hb transfer q bad q.color_a hat
  exact ⟨⟨t, d, hat, hdt, hd, fun h => hsep
    (edge_critical_le_of_le_endpoint_kernel source modules initial q hb hat h)⟩, hsep⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
