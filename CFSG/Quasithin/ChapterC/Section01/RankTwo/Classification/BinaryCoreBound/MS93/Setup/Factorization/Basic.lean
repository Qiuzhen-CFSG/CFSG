module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CriticalPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalStructure

/-!
# Local geometry for the critical factorization argument

A shortest walk supplies the first edge and a common neighbor for vertices
at distance two. Positive even critical distance then places each Z-layer
in the stabilizer two steps away. The X-layer is normalized by its actual
vertex group and both local layers are elementary abelian.

`Factorization.CriticalEscape` retains the literal endpoint-minus-two premise of 2.2(v).
It is an explicit hypothesis, not a proof of the later source escape theorem.
The namespace separates this premise from the definition of the same source
target in `Reduction.ModuleFacts`; their predicates are definitionally equal.
All carriers are subgroups of the original infinite free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), 2.2(iv)--(vi), pp.856--857.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The universal source premise at the vertex two steps before the far endpoint. -/
def Factorization.CriticalEscape (g : Geometry R) : Prop :=
  ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (g.exists_critical a ha) →
    ∀ e, (cosetGraph R).dist e a' = 2 →
      (cosetGraph R).dist a e + 2 = (cosetGraph R).dist a a' → ¬ V R a ≤ Q R e

/-- A first edge on a shortest path, with the exact remaining distance. -/
theorem exists_adjacent_dist_sub_one (a b : Vertex R)
    (hd : 0 < (cosetGraph R).dist a b) :
    ∃ t, Adjacent R a t ∧ (cosetGraph R).dist t b + 1 = (cosetGraph R).dist a b := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a b
  cases p with
  | nil => simp at hd
  | @cons a t b hat p =>
    refine ⟨t, (cosetGraph_adj R _ _).mp hat, ?_⟩
    have hle := SimpleGraph.dist_le p
    have htri := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := b)
    have hone : (cosetGraph R).dist a t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hat
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Vertices at distance two have a common neighbor. -/
theorem exists_common_neighbor_of_dist_two (a c : Vertex R)
    (hd : (cosetGraph R).dist a c = 2) :
    ∃ t, Adjacent R a t ∧ Adjacent R c t := by
  obtain ⟨t, hat, htc⟩ := exists_adjacent_dist_sub_one R a c (by omega)
  refine ⟨t, hat, adjacent_symm R ?_⟩
  exact (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp (by omega))

/-- Even distance preserves the bipartite color. -/
theorem color_eq_of_dist_even (a c : Vertex R)
    (hd : Even ((cosetGraph R).dist a c)) : color R a = color R c := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
  exact (walk_even_iff_color_eq R p).mp (hp.symm ▸ hd)

/-- The X-layer transforms by the actual right-coset conjugation. -/
theorem X_act (f : FreeAmalgam R) (a : Vertex R) :
    X R (act R f a) = (X R a).map (MulAut.conj f⁻¹).toMonoidHom := by
  exact edgeOmega_act R f a

/-- The whole vertex stabilizer normalizes X. -/
theorem X_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (X R a : Set (FreeAmalgam R)) := by
  intro f hf
  rw [mem_normalizer_iff_map_conj_eq]
  change (X R a).map (MulAut.conj f).toMonoidHom = X R a
  have he := X_act R f⁻¹ a
  have hfa : act R f⁻¹ a = a := (stabilizer R a).inv_mem hf
  simpa only [hfa, inv_inv] using he.symm

/-- Positive critical distance makes Z local at every vertex two steps away. -/
theorem Z_le_stabilizer_of_dist_two (g : Geometry R) (a : Vertex R)
    (ha : color R a = false) (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (c : Vertex R) (hd : (cosetGraph R).dist a c = 2) :
    Z R a ≤ stabilizer R c := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  have heven := g.even a ha
  have htwo : 2 ≤ criticalDistance R a (g.exists_critical a ha) := by
    obtain ⟨n, hn⟩ := heven
    omega
  have hone : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  exact (Z_le_Q_of_dist_lt R a (g.exists_critical a ha) (by omega)).trans
    (fun _ hx => hx.2 c (adjacent_symm R hct))

/-- Relative normality of X, without asserting ambient normality. -/
theorem X_normal (a : Vertex R) : ((X R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (X_normalized R a)

/-- X is elementary abelian on its actual subgroup carrier. -/
theorem X_elementary (a : Vertex R) : IsElementaryAbelian 2 (X R a) :=
  omegaCenter_elementary (Q R a)

/-- The kernel acts trivially by conjugation on X. -/
theorem Q_le_centralizer_X (a : Vertex R) :
    Q R a ≤ centralizer (X R a : Set (FreeAmalgam R)) := by
  intro q hq x hx
  exact ((mem_omegaCenter_iff.mp hx).2.2 q hq).symm

/-- Positive distance places Z in the elementary abelian X-layer. -/
theorem Z_elementary_of_positive (g : Geometry R) (a : Vertex R)
    (ha : color R a = false) (hb : 0 < criticalDistance R a (g.exists_critical a ha)) :
    IsElementaryAbelian 2 (Z R a) := by
  have hZX := g.omega_bound a ha hb
  refine {
    toIsMulCommutative := isMulCommutative_iff.mpr ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro x y
    exact Subtype.ext ((mem_omegaCenter_iff.mp (hZX y.property)).2.2 x
      (omegaCenter_le (Q R a) (hZX x.property)))
  · intro x
    exact Subtype.ext (mem_omegaCenter_iff.mp (hZX x.property)).2.1

/-- The reverse product in source 2.2(v) is genuinely contained in G_alpha. -/
theorem reverse_join_le_stabilizer_of_dist_two (g : Geometry R) (a : Vertex R)
    (ha : color R a = false) (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (c : Vertex R) (hd : (cosetGraph R).dist a c = 2) :
    Z R c ⊔ X R a ≤ stabilizer R a := by
  have hc : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hd]; decide)).symm.trans ha
  have hbc : 0 < criticalDistance R c (g.exists_critical c hc) := by
    rw [g.distance_constant c hc, ← g.distance_constant a ha]
    exact hb
  exact sup_le (Z_le_stabilizer_of_dist_two R g c hc hbc a (by
    rwa [SimpleGraph.dist_comm]))
    ((omegaCenter_le (Q R a)).trans (fun _ hx => hx.1))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
