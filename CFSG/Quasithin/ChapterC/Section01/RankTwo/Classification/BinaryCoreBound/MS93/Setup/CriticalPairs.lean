module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Critical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts

/-!
# Critical pairs under the source centralizer hypothesis

At the first kernel missed by a subgroup initially inside Q_alpha, its
predecessor still contains that subgroup. The endpoint has M-color because
an H-kernel contains each adjacent M-kernel. Applying the specified edge
centralizer equality gives the X-bound and noncommutation; centralization
of Q_alpha then proves that the reversed pair is critical as well.

The centralizer hypothesis of source 2.2 remains explicit. Its derivation
from the binary input belongs to the common reduction, not to these
conditional graph arguments. Conjugation preserves both defining clauses
of criticality on the original infinite free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), 2.2(i)--(iii), pp.856--857.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

private theorem first_kernel_exit (A : Subgroup (FreeAmalgam R)) (a c : Vertex R)
    (hAa : A ≤ Q R a) (hAc : ¬ A ≤ Q R c) :
    ∃ m t, color R m = false ∧ Adjacent R m t ∧
      A ≤ Q R t ∧ ¬ A ≤ Q R m ∧ (cosetGraph R).dist a m ≤ (cosetGraph R).dist a c := by
  classical
  have he : ∃ n : ℕ, ∃ m, (cosetGraph R).dist a m = n ∧ ¬ A ≤ Q R m :=
    ⟨_, c, rfl, hAc⟩
  obtain ⟨m, hd, hm⟩ := Nat.find_spec he
  have hne : a ≠ m := by rintro rfl; exact hm hAa
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a m
  have hpn : ¬ p.Nil := fun hn => hne hn.eq
  have ht : Adjacent R p.penultimate m :=
    (cosetGraph_adj R _ _).mp (p.adj_penultimate hpn)
  have hlt : (cosetGraph R).dist a p.penultimate < Nat.find he := by
    have hd' := SimpleGraph.dist_le p.dropLast
    have hl := p.length_dropLast_add_one hpn
    omega
  have hAt : A ≤ Q R p.penultimate := by
    by_contra hn
    exact Nat.find_min he hlt ⟨_, rfl, hn⟩
  have hcol : color R m = false := by
    cases hc : color R m
    · rfl
    · exact (hm (hAt.trans (Q_le_adjacent_h R hc ht))).elim
  exact ⟨m, p.penultimate, hcol, adjacent_symm R ht, hAt, hm,
    hd ▸ Nat.find_min' he ⟨c, rfl, hAc⟩⟩

/-- The centralizer hypothesis of source 2.2, at every actual edge. -/
def EdgeCentralizerCondition : Prop :=
  ∀ a t, color R a = false → Adjacent R a t →
    Q R t ⊓ centralizer (Z R a : Set (FreeAmalgam R)) = Q R a

/-- Source 2.2(i), with exactly its additional centralizer hypothesis. -/
theorem X_le_Q_of_dist_lt (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false) (c : Vertex R)
    (hd : (cosetGraph R).dist a c < criticalDistance R a (g.exists_critical a ha)) :
    X R a ≤ Q R c := by
  by_contra hn
  obtain ⟨m, t, hm, hmt, hXt, hXm, hdist⟩ :=
    first_kernel_exit R (X R a) a c (omegaCenter_le _) hn
  have hmb : (cosetGraph R).dist m a < criticalDistance R m (g.exists_critical m hm) := by
    rw [SimpleGraph.dist_comm, g.distance_constant m hm, ← g.distance_constant a ha]
    exact hdist.trans_lt hd
  have hZm : Z R m ≤ Q R a := Z_le_Q_of_dist_lt R m _ hmb
  apply hXm
  rw [← hC m t hm hmt]
  apply le_inf hXt
  intro x hx z hz
  exact (mem_omegaCenter_iff.mp hx).2.2 z (hZm hz)

/-- A critical pair with positive distance has a predecessor containing Z_alpha. -/
theorem critical_predecessor (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) (hb : 0 < criticalDistance R a he)
    {a' : Vertex R} (hc : CriticalPair R a a' he) :
    ∃ t, Adjacent R a' t ∧ color R t = true ∧ Z R a ≤ Q R t := by
  have hne : a ≠ a' := by
    rintro rfl
    have hd := hc.1
    simp only [SimpleGraph.dist_self] at hd
    omega
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hpn : ¬ p.Nil := fun hn => hne hn.eq
  have ht : Adjacent R p.penultimate a' :=
    (cosetGraph_adj R _ _).mp (p.adj_penultimate hpn)
  have hlt : (cosetGraph R).dist a p.penultimate < criticalDistance R a he := by
    have hd := SimpleGraph.dist_le p.dropLast
    have hl := p.length_dropLast_add_one hpn
    have hdist := hc.1
    omega
  have hcol : color R p.penultimate = true := by
    have hcol' := critical_endpoint_color R a ha he hc
    have hh := adjacent_color_ne R ht
    cases hx : color R p.penultimate <;> simp_all
  exact ⟨p.penultimate, adjacent_symm R ht, hcol, Z_le_Q_of_dist_lt R a he hlt⟩

/-- Source 2.2(ii): the actual critical Z-layers do not commute. -/
theorem critical_noncommutation (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    {a' : Vertex R} (hc : CriticalPair R a a' (g.exists_critical a ha)) :
    ⁅Z R a, Z R a'⁆ ≠ ⊥ := by
  intro heq
  obtain ⟨t, hat, _, hZt⟩ := critical_predecessor R a ha _ hb hc
  apply hc.2
  rw [← hC a' t (critical_endpoint_color R a ha _ hc) hat]
  exact le_inf hZt (commutator_eq_bot_iff_le_centralizer.mp heq)

/-- Source 2.2(iii): reversal preserves both clauses of criticality. -/
theorem critical_reverse (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (a' : Vertex R) (ha' : color R a' = false)
    (hc : CriticalPair R a a' (g.exists_critical a ha)) :
    CriticalPair R a' a (g.exists_critical a' ha') := by
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.dist_comm, hc.1, g.distance_constant a ha, g.distance_constant a' ha']
  · intro hn
    apply critical_noncommutation R g hC a ha hb hc
    apply le_bot_iff.mp
    calc
      ⁅Z R a, Z R a'⁆ ≤ ⁅Z R a, Q R a⁆ := commutator_mono le_rfl hn
      _ = ⊥ := g.centralizes a ha

omit [Finite M] in
/-- Conjugation transports genuine critical pairs, including noncontainment. -/
theorem criticalPair_act_iff (f : FreeAmalgam R) (a a' : Vertex R)
    (he : ∃ n, CriticalRadius R a n) (he' : ∃ n, CriticalRadius R (act R f a) n) :
    CriticalPair R (act R f a) (act R f a') he' ↔ CriticalPair R a a' he := by
  simp only [CriticalPair, dist_act, criticalDistance_act R f a he he', Z_act, Q_act,
    map_le_map_iff_of_injective (f := (MulAut.conj f⁻¹).toMonoidHom)
      (MulAut.conj f⁻¹).injective]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
