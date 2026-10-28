module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic

/-!
# Existence and uniqueness reduction for the moving-neighbor Z-layer

The quotient-fixed preimage B is normalized by the whole local stabilizer.
If every radius-two Z-layer lay in B, the moving radius commutator would lie
in Z, forcing H to be trivial. The preceding order bound excludes this.
An actual local conjugator then puts a moving neighbor over any given edge.

The final uniqueness theorem combines this existence result with the
noncentral intersection of two moving neighbors. It still takes the first
assertion of (4.3.4) as an explicit premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(vi), and the
“In particular” clause of (4.3.4), printed pp.882--883,886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
variable [Finite M]

/-- The genuine fixed preimage B is normal relative to the stabilizer. -/
theorem B_normalized (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ≤ normalizer (B R a (geometry.Z_normal a) : Set (FreeAmalgam R)) := by
  have hV : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  rw [le_normalizer_iff]
  intro g hg x hx
  have hfix : act R g a = a := hg
  have hLi : (Ltilde R a).map (MulAut.conj g⁻¹).toMonoidHom = Ltilde R a := by
    rw [← Ltilde_act, hfix]
  have hZn : (Z R a).map (MulAut.conj g).toMonoidHom = Z R a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hg)
  obtain ⟨hxV, hc⟩ := (mem_B_iff R a (geometry.Z_normal a) hV x).mp hx
  apply (mem_B_iff R a (geometry.Z_normal a) hV _).mpr
  refine ⟨le_normalizer_iff.mp (V_normalized a) g hg x hxV, ?_⟩
  intro l hl
  have hl' : (MulAut.conj g⁻¹) l ∈ Ltilde R a := by
    rw [← hLi]
    exact mem_map_of_mem _ hl
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hc _ hl')
  rw [hZn] at hh
  simpa only [map_commutatorElement, MulAut.conj_apply, inv_inv,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh

/-- A stabilizer element preserves the exact moving-neighbor condition. -/
theorem moving_of_local_act (hb : 2 < geometry.b R) (a d : Vertex R)
    (ha : color R a = false) (hd : d ∈ movingNeighbors geometry a)
    (g : FreeAmalgam R) (hg : g ∈ stabilizer R a) :
    act R g d ∈ movingNeighbors geometry a := by
  have hfix : act R g a = a := hg
  refine ⟨?_, ?_⟩
  · rw [← hfix, dist_act]
    exact hd.1
  · intro h
    apply hd.2
    have hB : (B R a (geometry.Z_normal a)).map (MulAut.conj g⁻¹).toMonoidHom =
        B R a (geometry.Z_normal a) :=
      mem_normalizer_iff_map_conj_eq.mp (B_normalized hb a ha ((stabilizer R a).inv_mem hg))
    rw [Z_act, ← hB] at h
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h

/-- The nontriviality of H forces V outside B. -/
theorem radius_not_le_B (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (initial : InitialFacts p) : ¬ V R p.a ≤ B R p.a (geometry.Z_normal p.a) := by
  intro h
  have hV : V R p.a ≤ stabilizer R p.a :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
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

/-- Some vertex at exactly distance two has its Z-layer outside B. -/
theorem exists_moving (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (initial : InitialFacts p) : ∃ d, d ∈ movingNeighbors geometry p.a := by
  by_contra! h
  apply radius_not_le_B p hb initial
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

/-- A moving neighbor exists over every specified edge. -/
theorem exists_moving_at_edge (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (initial : InitialFacts p) (t : Vertex R) (hat : Adjacent R p.a t) :
    ∃ d, Adjacent R d t ∧ d ∈ movingNeighbors geometry p.a := by
  obtain ⟨d, hd⟩ := exists_moving p hb initial
  obtain ⟨s, has, hsd⟩ := exists_common_neighbor_of_dist_two R p.a d hd.1
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.a has hat
  refine ⟨act R g d, ?_, moving_of_local_act hb p.a d p.color_a hd g hg⟩
  rw [← hgs]
  exact (adjacent_act_iff R g d s).mpr hsd

/-- The neighboring equality implies the full existence-and-uniqueness clause. -/
theorem moving_Z_unique_of_equal_Z
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (equal_Z : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
      ∀ d e, Adjacent R d t → Adjacent R e t →
        ¬ U R d ⊓ Z R e ≤ localCenter e → Z R d = Z R e)
    (p : Counterexample geometry) (t : Vertex R) (ht : Before p.a' p.a t 1) :
    ∃ d, Adjacent R d t ∧ d ∈ movingNeighbors geometry p.a ∧
      ∀ e, Adjacent R e t → e ∈ movingNeighbors geometry p.a → Z R e = Z R d := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨d, hdt, hd⟩ := exists_moving_at_edge p hb hi t ht.endpoint_adjacent
  refine ⟨d, hdt, hd, fun e het he => ?_⟩
  exact equal_Z p t ht e d het hdt
    (moving_intersection_noncentral hb modules p initial control p.a t e d p.color_a
      ht.endpoint_adjacent het hdt he hd)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
