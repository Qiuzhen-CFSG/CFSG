module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeIntersectionApplication

/-!
# The full neighboring-span bound in the radius-three argument

Conjugate the intersection inside the terminal local group, while keeping
one marked moving neighbor and its full-edge Sylow fixed. The proved omega
placement applies to every translated radius-three span when b >= 7 or
the moving quotient is linear or dihedral. The 8.3 commutator bound and
relative normality of H then control every neighboring center. Relative
normal generation joins these bounds to give [W intersect Q_alpha',V_alpha']
<= H. This does not require every neighbor to move the original actor.

The reduced application discharges the 8.3 and normality premises on the
literal F1.11 graph, in either orientation. The nonlinear b=5 placement
and the residual index contradiction remain separate obligations.

Source: DGS, *Groups and Graphs* (1985), 8.4, paragraph after (3), p.138.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Transport one marked omega bound to every neighboring center and then
to their actual radius-one span. Normality is relative to the terminal actor. -/
theorem source_radius_three_full_span_bound
    (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {beta a' : Vertex (family P)} (hb : 1 < b (family P))
    (w : (graph (family P)).neighborSet a')
    (M : IsRankOneModel (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)))
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hcase : 6 < b (family P) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 2 (2 ^ n)) ∨
      Nonempty ((d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* DihedralGroup 5))
    (H : Subgroup G) (hn : d.localGroup a' ≤ normalizer (H : Set G))
    (hbound : ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤ H) :
    ⁅V (family P) beta 3 ⊓ Q (family P) a',V (family P) a' 1⁆ ≤ H := by
  let := finite_endpoints h
  let F := family P
  let I := V F beta 3 ⊓ Q F a'
  have hVL : V F a' 1 ≤ d.localGroup a' :=
    (V_le_Q_of_dist_add_lt_b F h.generate (fun v => (source_Z_Q_U h v).1)
      a' a' 1 (by simpa using hb) (d.kernel_sylow a')).trans ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default))
  have hall (v : (graph F).neighborSet a') : ⁅I,Z F v.val⁆ ≤ H := by
    obtain ⟨g,hg,hgv⟩ := d.transitive a' w v
    have hga : g⁻¹ • a' = a' := (stabilizer F a').inv_mem (d.local_le a' hg)
    have heq : I.map (MulAut.conj g⁻¹).toMonoidHom =
        V F (g⁻¹ • beta) 3 ⊓ Q F a' := by
      dsimp only [I]
      rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,←V_translate,←Q_translate,hga]
    have hi : I.map (MulAut.conj g⁻¹).toMonoidHom ≤
        quotientSylowOmegaPreimage (d.localGroup w.val) R := by
      rw [heq]
      exact source_radius_three_intersection_omega_of_large_or_elementary_model
        h d w M R hR hcase
    have hc := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((commutator_mono hi le_rfl).trans hbound)
    have hmap : (I.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = I := by
      rw [map_map]
      convert map_id I using 1
      ext x
      simp [mul_assoc]
    have hH : H.map (MulAut.conj g).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hn hg)
    rwa [map_commutator,hmap,←Z_translate,hgv,hH] at hc
  have hZ : ⁅Z F a',I⁆ ≤ H := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr
      ((Z_centralizes_Q F a' (source_Z_Q_U h a').1).trans (centralizer_le inf_le_right))]
    exact bot_le
  rw [V_one_eq_sup_neighbors,commutator_comm]
  apply commutator_sup_le_of_relative_normal (d.localGroup a') _ _ I H hn
    ((Z_le_V F a' 1).trans hVL) (iSup_le fun v => (Z_neighbor_le_V F v.property).trans hVL) hZ
  exact commutator_iSup_le_of_relative_normal (d.localGroup a') I H _ hn
    (fun v => (Z_neighbor_le_V F v.property).trans hVL)
    (fun v => by rw [commutator_comm]; exact hall v)

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original critical configuration supplies both 8.3 and relative
normality. Only the stated already-proved intersection branches are used. -/
theorem reduced_radius_three_full_span_bound
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5)) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 3 ⊓ Q F a',V F a' 1⁆ ≤ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let := finite_endpoints ht
  have hb1 : 1 < b F := by change 3 < b F at hb; omega
  obtain ⟨hn,hHZ,_⟩ := source_critical_commutator_structure ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb1 hcomm models
  have hZL : Z F w.val ≤ d.localGroup a' :=
    ((Z_neighbor_le_V F w.property).trans
      (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
        a' a' 1 (by simpa using hb1) (d.kernel_sylow a'))).trans
      ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default))
  have hn' : d.localGroup a' ≤ normalizer (H : Set (Reduction.G₀ J S₀)) :=
    (normal_subgroupOf_iff_le_normalizer ((hHZ w).trans hZL)).mp hn
  exact source_radius_three_full_span_bound ht d hb1 w (models w.val) R hR hcase H hn'
    (reduced_moving_omega_commutator h hob models hc hab hd hb1 hcomm w hm R hR)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
