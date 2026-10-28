module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction.FiniteChoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor

/-!
# Actual incident choices at a critical pair

The critical commutator is a line in the proper terminal kernel of U_a.
The finite natural-module choices lift through the same marked local
projection to actual neighbors. Avoidance of the critical line and failure
of containment in the terminal kernel force the endpoint to move each
chosen edge subgroup. Neither order four nor a contrary-assumption escape
configuration is required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), choices after (4.4.5), printed p.895. ChoiceConstruction applies
regular replacement to these neighbors and retains actual incidence.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem coordinates_le {a : Vertex R} (model : LocalModel a)
    {A B : Subgroup (FreeAmalgam R)} (hA : A ≤ U R a) :
    model.coordinates A ≤ model.coordinates B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have hh : model.equiv ⟨x, hA hx⟩ ∈ model.coordinates B := h ⟨⟨x, hA hx⟩, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hh
    have hyx := congrArg Subtype.val (model.equiv.injective he)
    change (y : FreeAmalgam R) = x at hyx
    simpa only [hyx] using (show (y : FreeAmalgam R) ∈ B from hy)
  · intro h
    exact map_mono (subgroupOf_mono _ h)

private theorem inf_eq_bot_of_order_two {G : Type*} [Group G]
    {D A : Subgroup G} (hD : Nat.card D = 2) (h : ¬ D ≤ A) : D ⊓ A = ⊥ := by
  let : Fact (Nat.card D).Prime := ⟨hD ▸ Nat.prime_two⟩
  rcases ((D ⊓ A).subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (fun W : Subgroup D => W.map D.subtype) hb
    simpa only [map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_bot] using hh
  · exfalso
    apply h
    intro x hx
    have hm : (⟨x, hx⟩ : D) ∈ (D ⊓ A).subgroupOf D := ht.symm ▸ mem_top _
    exact hm.2

/-- The actual critical commutator is a line in the proper terminal kernel
of the natural layer. No value of the critical index is assumed. -/
private theorem critical_flag (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) = 2 ∧
    ⁅Z R a, Z R a'⁆ ≤ U R a ⊓ Q R a' ∧ U R a ⊓ Q R a' ≠ U R a := by
  have hb := common.large_distance
  let s := RegularPaths.naturalStructure common
  have heq := s.critical_commutator_eq geometry a p.start_color a' p.critical
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry a p.start_color a' p.critical
  have hDa : ⁅U R a, U R a'⁆ ≤ U R a := le_normalizer_iff_commutator_le_left.mp hn'
  have hDa' : ⁅U R a, U R a'⁆ ≤ U R a' := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  have hQ : U R a' ≤ Q R a' := (U_le_Z R _).trans
    (Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color) (by
      rw [geometry.distance_constant _ p.end_color, SimpleGraph.dist_self]
      change 0 < geometry.b R
      omega))
  have hne := s.critical_U_noncommutation geometry a p.start_color a' p.critical
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a p.start_color]; decide)
  let : Finite (U R a') := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a' p.end_color]; decide)
  let := geometry.U_elementary (by have := common.large_distance; omega) a p.start_color
  let := geometry.U_elementary (by have := common.large_distance; omega) a' p.end_color
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact card_commutator_eq_two_of_elementary_eight _ _
      (common.natural.card_at _ p.start_color) (common.natural.card_at _ p.end_color) hn hn' hne
  · rw [heq]
    exact le_inf hDa (hDa'.trans hQ)
  · intro h
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hUQ : U R a ≤ Q R a' := h ▸ inf_le_right
    rw [← common.natural.centralizer a' p.end_color] at hUQ
    exact hUQ.trans inf_le_right

/-- Avoiding the critical line while moving outside the terminal kernel
forces the endpoint Z-layer to move the incident subgroup. -/
private theorem not_normalized_of_avoids (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {B : Subgroup (FreeAmalgam R)} (hBU : B ≤ U R a)
    (havoid : ¬ ⁅Z R a, Z R a'⁆ ≤ B) (hmove : ¬ B ≤ U R a ⊓ Q R a') :
    ¬ Z R a' ≤ stabilizer R a ⊓ normalizer (B : Set (FreeAmalgam R)) := by
  intro hn
  have hline := inf_eq_bot_of_order_two (critical_flag common p).1 havoid
  have hsmall : ⁅B, U R a'⁆ ≤ B := le_normalizer_iff_commutator_le_left.mp
    ((U_le_Z R a').trans (hn.trans inf_le_right))
  have hD : ⁅B, U R a'⁆ ≤ ⁅Z R a, Z R a'⁆ :=
    commutator_mono (hBU.trans (U_le_Z R a)) (U_le_Z R a')
  have hc : ⁅B, U R a'⁆ = ⊥ := le_bot_iff.mp (hline ▸ le_inf hD hsmall)
  have hBS : B ≤ stabilizer R a' := hBU.trans ((U_le_Z R a).trans
    (source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).1)
  have hBQ : B ≤ Q R a' := by
    rw [← common.natural.centralizer a' p.end_color]
    exact le_inf hBS (commutator_eq_bot_iff_le_centralizer.mp hc)
  exact hmove (le_inf hBU hBQ)

/-- Two genuine neighbors satisfying the geometric clauses needed before
regular replacement. Both possible nonzero edge orders are handled. -/
theorem incident_choices (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {t : Vertex R} (hat : Adjacent R a t) :
    ∃ t₁ t₂ : Vertex R,
      Adjacent R a t₁ ∧ Adjacent R a t₂ ∧
      (¬ ⁅Z R a, Z R a'⁆ ≤ edgeCommutator R a t₁) ∧
      (¬ ⁅Z R a, Z R a'⁆ ≤ edgeCommutator R a t₂) ∧
      (¬ Z R a' ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t₁ : Set (FreeAmalgam R))) ∧
      (¬ Z R a' ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t₂ : Set (FreeAmalgam R))) ∧
      (edgeCommutator R a t₁ ⊓ edgeCommutator R a t₂) ⊓ Q R a' = ⊥ := by
  let modules := RegularPaths.moduleFacts common
  obtain ⟨model⟩ := localModel_nonempty source modules a p.start_color
  let E := edgeCommutator R a t
  let D := ⁅Z R a, Z R a'⁆
  let C := U R a ⊓ Q R a'
  have hEU : E ≤ U R a := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance modules a t p.start_color hat
  obtain ⟨hD, hDC, hC⟩ := critical_flag common p
  have hDU : D ≤ U R a := hDC.trans inf_le_left
  have hCU : C ≤ U R a := inf_le_left
  have hEC : Nat.card E = 2 ∨ Nat.card E = 4 := by
    have hdiv := card_dvd_of_le hEU
    rw [common.natural.card_at a p.start_color] at hdiv
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hn : Nat.card E ≠ 1 := fun h =>
      Escape.EdgeTransfer.edge_commutator_ne_bot modules a t p.start_color hat
        (Subgroup.card_eq_one.mp h)
    have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance modules a t p.start_color hat
    change Nat.card E ≤ 4 at hsmall
    change Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 ∨ Nat.card E = 8 at hh
    omega
  have hcoordsC : model.coordinates C ≠ ⊤ := by
    intro h
    apply hC
    apply model.coordinates_injective hCU le_rfl
    rw [h, LocalModel.coordinates, subgroupOf_self, map_top_of_surjective _ model.equiv.surjective]
  obtain ⟨g, h, hgD, hhD, hgC, hhC, hsep⟩ := finite_choices
    (model.coordinates E) (model.coordinates D) (model.coordinates C)
    (by rwa [model.coordinates_card E hEU])
    (by rwa [model.coordinates_card D hDU])
    ((coordinates_le model hDU).mpr hDC) hcoordsC
  obtain ⟨t₁, ht₁, he₁⟩ := model.realizes_plane source p.start_color hat g
  obtain ⟨t₂, ht₂, he₂⟩ := model.realizes_plane source p.start_color hat h
  have h₁U := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance modules a t₁ p.start_color ht₁
  have h₂U := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance modules a t₂ p.start_color ht₂
  change model.coordinates (edgeCommutator R a t₁) = move g (model.coordinates E) at he₁
  change model.coordinates (edgeCommutator R a t₂) = move h (model.coordinates E) at he₂
  have hav₁ : ¬ D ≤ edgeCommutator R a t₁ := by
    intro hn
    apply hgD
    rw [← he₁]
    exact (coordinates_le model hDU).mpr hn
  have hav₂ : ¬ D ≤ edgeCommutator R a t₂ := by
    intro hn
    apply hhD
    rw [← he₂]
    exact (coordinates_le model hDU).mpr hn
  have hm₁ : ¬ edgeCommutator R a t₁ ≤ C := by
    intro hn
    apply hgC
    rw [← he₁]
    exact (coordinates_le model h₁U).mpr hn
  have hm₂ : ¬ edgeCommutator R a t₂ ≤ C := by
    intro hn
    apply hhC
    rw [← he₂]
    exact (coordinates_le model h₂U).mpr hn
  refine ⟨t₁, t₂, ht₁, ht₂, hav₁, hav₂,
    not_normalized_of_avoids common p h₁U hav₁ hm₁,
    not_normalized_of_avoids common p h₂U hav₂ hm₂, ?_⟩
  have he : (edgeCommutator R a t₁ ⊓ edgeCommutator R a t₂) ⊓ C = ⊥ := by
    apply model.coordinates_injective (inf_le_left.trans (inf_le_left.trans h₁U)) bot_le
    change model.coordinates ((edgeCommutator R a t₁ ⊓ edgeCommutator R a t₂) ⊓ C) =
      model.coordinates ⊥
    rw [model.coordinates_inf, model.coordinates_inf, he₁, he₂, hsep]
    simp only [LocalModel.coordinates, bot_subgroupOf, Subgroup.map_bot]
  apply le_bot_iff.mp
  rw [← he]
  exact le_inf inf_le_left (le_inf (inf_le_left.trans (inf_le_left.trans h₁U)) inf_le_right)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
