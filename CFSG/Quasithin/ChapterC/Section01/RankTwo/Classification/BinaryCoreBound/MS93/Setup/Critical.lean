module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Covariance

/-!
# The critical endpoint and the elementary local MS93 geometry

At an H-vertex the first-neighborhood kernel is its whole edge group. Thus
an M-vertex kernel lies in every adjacent H-vertex kernel. A critical endpoint
cannot have H-color: the predecessor on a shortest walk would already contain
Z by minimality, contradicting critical noncontainment. Bipartiteness then
makes the least distance even.

The same edge containment proves that Z centralizes Q, and positive critical
distance puts Z in Omega-one of Z(Q). Radius-two groups lie in the local
stabilizer when b > 2. The final membership formula checks that B is the actual
quotient-centralizer preimage with the correct relative normality convention.

Source: MS93 (1993), notation and 2.1(ii),(iv),(v), printed pp.854--855,
and the definition of B_alpha on p.859. These proofs do not use acyclicity.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

theorem Z_le_stabilizer (a : Vertex R) : Z R a ≤ stabilizer R a := by
  classical
  rw [Z]
  split_ifs with ha
  · apply iSup_le
    intro b
    apply iSup_le
    intro hab x hx
    exact (omegaCenter_le (Q R b) hx).2 a (adjacent_symm R hab)
  · exact (omegaCenter_le (Q R a)).trans (fun _ hx => hx.1)

theorem Q_hVertex_eq_edge [Finite M] (g : FreeAmalgam R) :
    Q R (hVertex R g) = stabilizer R (mVertex R g) ⊓ stabilizer R (hVertex R g) := by
  have hh := Q_act R g (beta R)
  simp only [beta, act_hVertex, one_mul] at hh
  rw [hh]
  change (neighborhoodKernel R (hVertex R 1)).map _ = _
  rw [neighborhoodKernel_h_base_eq_Sbar, ← Mbar_inf_Hbar,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    ← stabilizer_mVertex, ← stabilizer_hVertex]

theorem Q_h_eq_edge [Finite M] {a t : Vertex R}
    (ht : color R t = true) (hat : Adjacent R a t) :
    Q R t = stabilizer R a ⊓ stabilizer R t := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  · exact Q_hVertex_eq_edge R g
  · change false = true at ht
    cases ht

theorem Q_le_adjacent_h [Finite M] {a t : Vertex R}
    (ht : color R t = true) (hat : Adjacent R a t) : Q R a ≤ Q R t := by
  rw [Q_h_eq_edge R ht hat]
  exact fun _ hx => ⟨hx.1, hx.2 _ hat⟩

theorem Z_centralizes_Q [Finite M] (a : Vertex R) (ha : color R a = false) :
    ⁅Z R a, Q R a⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer, Z, if_pos ha]
  apply iSup_le
  intro b
  apply iSup_le
  intro hab x hx
  have hb : color R b = true := by
    have hne := adjacent_color_ne R hab
    cases hcol : color R b <;> simp_all
  have hcomm := (mem_omegaCenter_iff.mp hx).2.2
  intro y hy
  exact hcomm y (Q_le_adjacent_h R hb hab hy)

theorem Z_le_X_of_positive [Finite M] (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) (hb : 0 < criticalDistance R a he) :
    Z R a ≤ X R a := by
  have hZQ : Z R a ≤ Q R a := Z_le_Q_of_dist_lt R a he (by simpa using hb)
  have hZC := commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)
  rw [Z, if_pos ha]
  apply iSup_le
  intro b
  apply iSup_le
  intro hab x hx
  have hxZ : x ∈ Z R a := by
    have hle : edgeOmega R b ≤ Z R a := by
      rw [Z, if_pos ha]
      exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)
    exact hle hx
  exact mem_omegaCenter_iff.mpr
    ⟨hZQ hxZ, (mem_omegaCenter_iff.mp hx).2.1, fun y hy => hZC hxZ y hy⟩

theorem critical_endpoint_color [Finite M] (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) {a' : Vertex R} (hc : CriticalPair R a a' he) :
    color R a' = false := by
  by_contra h
  have ha' : color R a' = true := by cases hcol : color R a' <;> simp_all
  have hne : a ≠ a' := by
    intro hh
    rw [hh, ha'] at ha
    cases ha
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hpn : ¬ p.Nil := by
    intro hn
    exact hne hn.eq
  have hadj : Adjacent R p.penultimate a' :=
    (cosetGraph_adj R _ _).mp (p.adj_penultimate hpn)
  have hlt : (cosetGraph R).dist a p.penultimate < criticalDistance R a he := by
    have hdist := SimpleGraph.dist_le p.dropLast
    have hlen := p.length_dropLast_add_one hpn
    have hh := hc.1
    omega
  exact hc.2 ((Z_le_Q_of_dist_lt R a he hlt).trans (Q_le_adjacent_h R ha' hadj))

theorem walk_even_iff_color_eq {a b : Vertex R} (p : (cosetGraph R).Walk a b) :
    Even p.length ↔ color R a = color R b := by
  induction p with
  | nil => simp
  | @cons a c b hadj p ih =>
    have hne := adjacent_color_ne R ((cosetGraph_adj R _ _).mp hadj)
    simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    cases h₁ : color R a <;> cases h₂ : color R c <;> cases h₃ : color R b <;> simp_all

theorem criticalDistance_even [Finite M] (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) : Even (criticalDistance R a he) := by
  obtain ⟨a', hc⟩ := criticalPair_exists R a he
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  rw [← hc.1, ← hp, walk_even_iff_color_eq]
  rw [ha, critical_endpoint_color R a ha he hc]

theorem exists_mVertex_of_color {a : Vertex R} (ha : color R a = false) :
    ∃ g, a = mVertex R g := by
  cases a with
  | inl q =>
    induction q using Quotient.inductionOn
    exact ⟨_, rfl⟩
  | inr q =>
    change true = false at ha
    cases ha

theorem criticalRadius_exists_at [Finite M] (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hP : MSCharacteristicCondition R) (a : Vertex R) (ha : color R a = false) :
    ∃ n, CriticalRadius R a n := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  obtain ⟨n, hn⟩ := criticalRadius_exists R hp hne hP
  refine ⟨n, ?_⟩
  have hh := (criticalRadius_act_iff R g (alpha R) n).mpr hn
  simpa only [alpha, act_mVertex, one_mul] using hh

theorem criticalDistance_eq_base (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) (hbase : ∃ n, CriticalRadius R (alpha R) n) :
    criticalDistance R a he = criticalDistance R (alpha R) hbase := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have he' : ∃ n, CriticalRadius R (act R g (alpha R)) n := by
    simpa only [alpha, act_mVertex, one_mul] using he
  simpa only [alpha, act_mVertex, one_mul] using
    criticalDistance_act R g (alpha R) hbase he'

theorem V_le_stabilizer_of_two_lt [Finite M]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hP : MSCharacteristicCondition R)
    (a : Vertex R) (ha : color R a = false)
    (he : ∃ n, CriticalRadius R a n) (hlarge : 2 < criticalDistance R a he) :
    V R a ≤ stabilizer R a := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases hcol : color R t = false
  · have het := criticalRadius_exists_at R hp hne hP t hcol
    have hbase := criticalRadius_exists R hp hne hP
    have hd : criticalDistance R t het = criticalDistance R a he :=
      (criticalDistance_eq_base R t hcol het hbase).trans
        (criticalDistance_eq_base R a ha he hbase).symm
    have hlt : (cosetGraph R).dist t a < criticalDistance R t het := by omega
    exact (Z_le_Q_of_dist_lt R t het hlt).trans (fun _ hx => hx.1)
  · have hc : color R t = true := by cases hh : color R t <;> simp_all
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
    have hnEven : ¬ Even ((cosetGraph R).dist t a) := by
      rw [← hp, walk_even_iff_color_eq, hc, ha]
      decide
    rw [Nat.even_iff] at hnEven
    have hd : (cosetGraph R).dist t a = 1 := by omega
    have hadj : Adjacent R t a :=
      (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hd)
    rw [Z, if_neg hcol]
    exact (omegaCenter_le (Q R t)).trans (fun _ hx => hx.2 a hadj)

open scoped commutatorElement in
theorem mem_B_iff (a : Vertex R)
    (hn : ((Z R a).subgroupOf (stabilizer R a)).Normal)
    (hV : V R a ≤ stabilizer R a) (x : FreeAmalgam R) :
    x ∈ B R a hn ↔ x ∈ V R a ∧ ∀ l ∈ Ltilde R a, ⁅l, x⁆ ∈ Z R a := by
  let := hn
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hv, hc⟩ := mem_centralizerModulo_iff.mp hv
    refine ⟨hv, ?_⟩
    rintro l ⟨k, hk, rfl⟩
    exact hc k hk
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hV hx⟩, mem_centralizerModulo_iff.mpr ⟨hx, ?_⟩, rfl⟩
    intro l hl
    exact hc l (mem_map_of_mem (stabilizer R a).subtype hl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
