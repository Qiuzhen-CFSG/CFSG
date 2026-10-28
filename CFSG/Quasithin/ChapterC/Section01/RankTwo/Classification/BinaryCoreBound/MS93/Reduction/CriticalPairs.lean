module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.LocalCentralizer

/-!
# Centralizers and critical pairs at every binary M-vertex

Conjugation transports the exact local centralizer to every M-vertex. Before
the critical radius, X_alpha lies in Q_rho: induction along a shortest path
puts it in the local stabilizer, while Z_rho lies in Q_alpha and hence commutes
with X_alpha. The centralizer equality completes the induction.

At the critical endpoint Z_alpha still lies in the stabilizer, so containment
in the centralizer of Z_alpha' would contradict criticality. This proves
noncommutation and then reversal of the critical pair. These are source
(2.2)(i)--(iii), independent of the later natural-module and escape arguments.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.856--857.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
theorem C_act (g : FreeAmalgam R) (a : Vertex R) :
    C R (act R g a) = (C R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  rw [C, stabilizer_act, Z_act]
  apply le_antisymm
  · rintro x ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    intro z hz
    apply e.injective
    have hh : e z * e y = e y * e z := hc (e z) (mem_map_of_mem e.toMonoidHom hz)
    simpa only [map_mul] using hh
  · rintro x ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem e.toMonoidHom hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change e z * e y = e y * e z
    simpa only [map_mul] using congrArg e (hc z hz)

theorem LocalSource.C_eq_Q (source : LocalSource L R) (hR : R ≠ ⊥)
    (a : Vertex R) (ha : color R a = false) : C R a = Q R a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := C_act (R := R) g (alpha R)
  have hq := Q_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hh hq
  have hbase := source.C_alpha hR
  change C R (mVertex R 1) = Q R (mVertex R 1) at hbase
  rw [hh, hbase, hq]

theorem LocalSource.adjacent_centralizer (source : LocalSource L R) (hR : R ≠ ⊥)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    Q R t ⊓ centralizer (Z R a : Set (FreeAmalgam R)) = Q R a := by
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    rw [← source.C_eq_Q hR a ha]
    exact ⟨hx.2 a (adjacent_symm R hat), hc⟩
  · intro x hx
    refine ⟨Q_le_adjacent_h R ht hat hx, ?_⟩
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)) hx

omit [Finite M] in
theorem Z_le_stabilizer_of_dist_le (a : Vertex R) (he : ∃ n, CriticalRadius R a n)
    {a' : Vertex R} (hle : (cosetGraph R).dist a a' ≤ criticalDistance R a he) :
    Z R a ≤ stabilizer R a' := by
  by_cases heq : a = a'
  · subst a'
    exact Z_le_stabilizer R a
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hn : ¬ p.Nil := fun h => heq h.eq
  have hlt : (cosetGraph R).dist a p.penultimate < criticalDistance R a he := by
    have hd := SimpleGraph.dist_le p.dropLast
    have hl := p.length_dropLast_add_one hn
    omega
  intro x hx
  exact (Z_le_Q_of_dist_lt R a he hlt hx).2 a'
    ((cosetGraph_adj R _ _).mp (p.adj_penultimate hn))

theorem LocalSource.critical_noncommutation (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    {a' : Vertex R} (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅Z R a, Z R a'⁆ ≠ ⊥ := by
  intro hcomm
  apply hc.2
  rw [← source.C_eq_Q geometry.radical_ne_bot a'
    (critical_endpoint_color R a ha _ hc)]
  exact le_inf (Z_le_stabilizer_of_dist_le a _ hc.1.le)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)

theorem LocalSource.critical_reverse (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (ha' : color R a' = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    CriticalPair R a' a (geometry.exists_critical a' ha') := by
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.dist_comm, hc.1, geometry.distance_constant a ha,
      geometry.distance_constant a' ha']
  · intro hle
    apply source.critical_noncommutation geometry a ha hc
    apply le_bot_iff.mp
    exact (commutator_mono le_rfl hle).trans (Z_centralizes_Q R a ha).le

theorem LocalSource.X_le_Q_of_dist_lt (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (ha' : color R a' = false)
    (hlt : (cosetGraph R).dist a a' < criticalDistance R a (geometry.exists_critical a ha)) :
    X R a ≤ Q R a' := by
  have aux : ∀ n, ∀ t : Vertex R, color R t = false →
      (cosetGraph R).dist a t = n →
      n < criticalDistance R a (geometry.exists_critical a ha) → X R a ≤ Q R t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht hdist hlt
      have hZX : Z R t ≤ Q R a := by
        apply Z_le_Q_of_dist_lt R t (geometry.exists_critical t ht)
        rw [SimpleGraph.dist_comm, geometry.distance_constant t ht]
        rw [geometry.distance_constant a ha] at hlt
        omega
      have hXC : X R a ≤ centralizer (Z R t : Set (FreeAmalgam R)) := by
        intro x hx z hz
        exact (mem_omegaCenter_iff.mp hx).2.2 z (hZX hz)
      suffices hXS : X R a ≤ stabilizer R t by
        rw [← source.C_eq_Q geometry.radical_ne_bot t ht]
        exact le_inf hXS hXC
      obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
      rw [SimpleGraph.dist_comm, hdist] at hp
      cases p with
      | nil => exact (omegaCenter_le (Q R a)).trans (fun _ hx => hx.1)
      | @cons t s a hts p =>
        have hts' := (cosetGraph_adj R _ _).mp hts
        have hs : color R s = true := by
          have hh := adjacent_color_ne R hts'
          cases hcol : color R s <;> simp_all
        cases p with
        | nil => rw [ha] at hs; cases hs
        | @cons s r a hsr p =>
          have hsr' := (cosetGraph_adj R _ _).mp hsr
          have hr : color R r = false := by
            have hh := adjacent_color_ne R hsr'
            cases hcol : color R r <;> simp_all
          have hsmall : (cosetGraph R).dist a r < n := by
            have hh := SimpleGraph.dist_le p.reverse
            simp only [SimpleGraph.Walk.length_reverse] at hh
            simp only [SimpleGraph.Walk.length_cons] at hp
            omega
          have hxq := ih _ hsmall r hr rfl (hsmall.trans hlt)
          intro x hx
          have hxs : x ∈ Q R s := Q_le_adjacent_h R hs (adjacent_symm R hsr') (hxq hx)
          exact hxs.2 t (adjacent_symm R hts')
  exact aux _ a' ha' rfl hlt

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
