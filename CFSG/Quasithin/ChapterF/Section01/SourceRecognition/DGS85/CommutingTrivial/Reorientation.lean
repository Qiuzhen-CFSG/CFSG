module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood

/-!
# Selecting and transporting the reverse critical pair

If a neighboring span escapes the opposite two-core, one of its center
summands escapes. DGS 6.2(d) turns this into escape from the full kernel U;
the global minimum and the triangle inequality give distance exactly b.
The summand at the center of the ball cannot escape, so the selected
vertex is a genuine neighbor. No acyclicity is needed.

The original action transports both intersections and commutators. Thus
an element exchanging the two span vertices carries the forward trivial
commutator to the reverse one. This is the selection and final conjugation
step in 9.2; constructing that exchange from the reoriented Chapter 8
conclusions remains part of the Chapter 9 argument.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 9.2, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Both the minimum-distance equality and full-kernel escape transport together. -/
theorem criticalPair_translate [∀ i, Finite (F i)] {v w : Vertex F}
    (hc : IsCriticalPair F v w) (g : G) : IsCriticalPair F (g • v) (g • w) := by
  refine ⟨(dist_smul F g v w).trans hc.1, ?_⟩
  intro h
  apply hc.2
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  rwa [← Z_translate, ← U_translate, inv_smul_smul, inv_smul_smul] at hm

/-- The forward critical center forces its neighboring span to escape the opposite core. -/
theorem V_not_le_Q_of_criticalPair {a a' beta : Vertex F}
    (hc : IsCriticalPair F a a') (ha : (graph F).Adj beta a)
    (hQU : Q F a' ≤ U F a') : ¬ V F beta 1 ≤ Q F a' := by
  intro h
  apply hc.2
  have hZV : Z F a ≤ V F beta 1 :=
    le_iSup_of_le a (le_iSup_of_le
      ((mem_ball_one F beta a).mpr (Or.inl ha)) le_rfl)
  exact hZV.trans (h.trans hQU)

/-- Reverse span escape selects the actual neighboring critical pair used in 9.2. -/
theorem exists_neighbor_criticalPair [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    {v w : Vertex F} (hd : (graph F).dist v w + 1 = b F)
    (he : ¬ V F v 1 ≤ Q F w) :
    ∃ z : Vertex F, (graph F).Adj v z ∧ IsCriticalPair F z w ∧
      ¬ Z F z ≤ Q F w := by
  have hex : ∃ z, z ∈ ball F v 1 ∧ ¬ Z F z ≤ Q F w := by
    by_contra! hn
    apply he
    exact iSup_le fun z => iSup_le fun hz => hn z hz
  obtain ⟨z, hz, hez⟩ := hex
  have hadj : (graph F).Adj v z := by
    rcases (mem_ball_one F v z).mp hz with hadj | rfl
    · exact hadj
    · exact (hez (Z_le_Q_of_dist_lt_b F hZ hS v w (by omega))).elim
  have hescape : ¬ Z F z ≤ U F w := by
    intro hzU
    let := Z_elementary F hZ z
    exact hez (two_subgroup_le_Q F w (hS w) (IsElementaryAbelian.isPGroup 2 _) hzU)
  refine ⟨z, hadj, ⟨?_, hescape⟩, hez⟩
  have hlow : b F ≤ (graph F).dist z w := Nat.sInf_le ⟨z, w, rfl, hescape⟩
  have ht := (connected F hgen).dist_triangle (u := z) (v := v) (w := w)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at ht
  omega

/-- Conjugation moves V, the intersected Q, and the acted-on V by the same element. -/
theorem neighbor_commutator_translate [∀ i, Finite (F i)]
    (v w : Vertex F) (g : G) :
    ⁅V F (g • v) 1 ⊓ Q F (g • w), V F (g • w) 1⁆ =
      (⁅V F v 1 ⊓ Q F w, V F w 1⁆).map (MulAut.conj g).toMonoidHom := by
  rw [V_translate, Q_translate, V_translate, map_commutator,
    map_inf _ _ _ (MulAut.conj g).injective]

/-- Triviality of the literal neighbor commutator is invariant under the graph action. -/
theorem neighbor_commutator_eq_bot_iff_translate [∀ i, Finite (F i)]
    (v w : Vertex F) (g : G) :
    ⁅V F (g • v) 1 ⊓ Q F (g • w), V F (g • w) 1⁆ = ⊥ ↔
      ⁅V F v 1 ⊓ Q F w, V F w 1⁆ = ⊥ := by
  rw [neighbor_commutator_translate, map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]

/-- The exchange element in 9.2 turns the original trivial commutator into the reverse one. -/
theorem reverse_commutator_eq_bot_of_exchange [∀ i, Finite (F i)]
    {v w : Vertex F} (h : ⁅V F v 1 ⊓ Q F w, V F w 1⁆ = ⊥)
    (g : G) (hgv : g • v = w) (hgw : g • w = v) :
    ⁅V F w 1 ⊓ Q F v, V F v 1⁆ = ⊥ := by
  have he := (neighbor_commutator_eq_bot_iff_translate F v w g).mpr h
  rwa [hgv, hgw] at he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
