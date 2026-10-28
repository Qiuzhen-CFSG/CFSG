module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NeighborCenters
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# Radius-two control along a noncommuting critical path

In the epsilon-two case, the radius-two span at the first endpoint centralizes
the centers at the two neighbors of the penultimate even vertex. The natural
center splitting therefore makes it centralize that vertex's whole center.
The earlier centralizer-Sylow alternative places this two-group in its actual
two-core. At the preceding odd vertex, the radius-one span normalizes the
abelian radius-two group, so the second commutator vanishes. Literal section
coordinates transfer this identity to a quadratic quotient action.

These are (7.5)(2)--(3)'s containment and quadraticity assertions. The radius
escape and the long-distance exclusion are separate assertions. In particular,
no permutation kernel is identified with its Sylow two-core.

Source: DGS, *Groups and Graphs* (1985), (7.5)(2)--(3), pp.129--130.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The distance budget controls every generator of a radius subgroup in the
actual two-core, rather than only the permutation kernel. -/
theorem graph_V_le_Q_of_distance (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v t : Vertex (family P)} {i : ℕ}
    (hd : (graph (family P)).dist v t + i < b (family P)) :
    V (family P) v i ≤ Q (family P) t := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply graph_Z_le_Q_of_short h hS
  have hx' := (mem_ball_iff (family P) h.generate v x i).mp hx
  have htri := (connected_graph h).dist_triangle (u := x) (v := v) (w := t)
  rw [SimpleGraph.dist_comm (u := x) (v := v)] at htri
  omega

/-- DGS (7.5)(2)'s core containment, at the last even vertex of a critical
path. The local splitting is proved from the same natural endpoint data. -/
theorem graph_epsilonTwo_radius_two_le_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t y x : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hty : (graph (family P)).Adj t y) (hyx : (graph (family P)).Adj y x)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hdy : (graph (family P)).dist v y + 1 = (graph (family P)).dist v t)
    (hdx : (graph (family P)).dist v x + 1 = (graph (family P)).dist v y)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w)) :
    V (family P) v 2 ≤ Q (family P) y := by
  let := finite_endpoints h
  have hb : 2 < b (family P) := by omega
  have hp := graph_V_isPGroup_of_short h hS v hb
  have hVL : V (family P) v 2 ≤ L y := by
    rw [←hstar y t hty.symm]
    exact local_twoGroup_le_star (d y t hty.symm) (by rw [hstar]; exact hodd y)
      _ hp (graph_V_le_stabilizer_of_distance h (by omega))
  have hZW : Z (family P) w ≤ L v := by
    let := graph_Z_elementary h w
    rw [←hstar v u hvu]
    exact local_twoGroup_le_star (d v u hvu) (by rw [hstar]; exact hodd v) _
      (IsElementaryAbelian.isPGroup 2 _)
      (Z_le_stabilizer_of_dist_le_b (family P) h.generate w v
        (by rw [SimpleGraph.dist_comm,hc.1]))
  obtain ⟨g,hg⟩ := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).1
  have hvw : v.type = w.type := (same_orbit_iff (family P) v w).mp ⟨g,hg⟩
  have hwy : w.type = y.type := by
    have h₁ := hwt.1
    have h₂ := hty.1
    cases hw : w.type <;> cases ht : t.type <;> cases hy : y.type <;> simp_all
  have hvy := hvw.trans hwy
  have hxt : x ≠ t := by
    intro he
    rw [he] at hdx
    omega
  have hs := graph_epsilonTwo_centers_split_of_type h hB L d hstar hodd hdich
    hvu hepsilon hnat₀ hvy hyx hty.symm hxt
  have hid := graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hdt hepsilon hnat₀ hnat₁
  have hCx : V (family P) v 2 ≤ centralizer (Z (family P) x : Set G) :=
    (graph_V_le_Q_of_distance h hS (by omega)).trans (graph_Q_centralizes_Z h x)
  have hCt : V (family P) v 2 ≤ centralizer (Z (family P) t : Set G) := by
    rw [←hid.2.1]
    exact commutator_eq_bot_iff_le_centralizer.mp (graph_V_centralizes_commutator h hS hc hb)
  have hCy : V (family P) v 2 ≤ centralizer (Z (family P) y : Set G) := by
    rw [le_centralizer_iff,hs.1]
    exact sup_le (le_centralizer_iff.mp hCx) (le_centralizer_iff.mp hCt)
  have hCS := (hdich y).resolve_right (fun he =>
    center_ne_omega_of_noncommuting (L v) _ _ hZW hne
      ((graph_center_equality_of_type h L hcov hvy).mpr he))
  have hQN : Q (family P) y ≤ L y ⊓ centralizer (Z (family P) y : Set G) := by
    obtain ⟨S,hS⟩ := hCS
    rw [←hS]
    exact map_subtype_le _
  have hnQ : L y ⊓ centralizer (Z (family P) y : Set G) ≤
      normalizer (Q (family P) y : Set G) := by
    have hLP : L y ≤ stabilizer (family P) y := by
      rw [←hstar y t hty.symm]
      exact (d y t hty.symm).Pstar_le
    exact (inf_le_left.trans hLP).trans ((stabilizer (family P) y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have he := inf_eq_inf_of_normal_sylow (V (family P) v 2) _ _ hp hQN hnQ hCS
  rw [inf_of_le_left (le_inf hVL hCy)] at he
  exact he.le.trans inf_le_right

/-- The abelian radius-two group centralizes its commutators with the radius-one
span at the last odd path vertex. -/
theorem graph_radius_two_triple_commutator
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v t : Vertex (family P)}
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hb : 4 < b (family P)) :
    ⁅V (family P) v 2,⁅V (family P) v 2,V (family P) t 1⁆⁆ = ⊥ := by
  let := graph_V_elementary_of_twice_radius_lt h hS v (i := 2) (by omega)
  have hnorm : V (family P) t 1 ≤ normalizer (V (family P) v 2 : Set G) :=
    (graph_V_le_stabilizer_of_distance h (by rw [SimpleGraph.dist_comm]; omega)).trans
      (graph_stabilizer_normalizes_V h v 2)
  have hcomm : ⁅V (family P) v 2,V (family P) t 1⁆ ≤ V (family P) v 2 :=
    le_normalizer_iff_commutator_le_left.mp hnorm
  exact bot_unique ((commutator_mono le_rfl hcomm).trans
    (commutator_self_eq_bot_iff.mpr inferInstance).le)

/-- The same radius-two actor lies in the actual last odd local actor and acts
quadratically on any literal marked radius-one section under its core quotient. -/
theorem graph_radius_two_quadratic_section
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v t y : Vertex (family P)} (hty : (graph (family P)).Adj t y)
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hb : 4 < b (family P))
    (hcore : V (family P) v 2 ≤ Q (family P) y)
    (c : LocalRankOneData (stabilizer (family P) t)
      (stabilizer (family P) t ⊓ stabilizer (family P) y))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) t))
    [((Q (family P) t).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)))) :
    V (family P) v 2 ≤ c.Pstar ∧
      IsQuadratic σ (((V (family P) v 2).subgroupOf c.Pstar).map
        (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar))) := by
  have hA : V (family P) v 2 ≤ stabilizer (family P) t :=
    (hcore.trans (source_Z_Q_U h y).2).trans
      ((ballKernel_one_le_edge (family P) hty.symm).trans inf_le_right)
  refine ⟨local_twoGroup_le_star c ho _ (graph_V_isPGroup_of_short h hS v (by omega)) hA,?_⟩
  apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    c.Pstar (V (family P) t 1) (Z (family P) t) (V (family P) v 2) σ _ s
  rw [graph_radius_two_triple_commutator h hS hdt hb]
  exact bot_le

/-- Construct the final two vertices of a long critical path, with the
actual core containment, escape and vanishing second commutator. The Sylow
product is the preceding (7.1)(c) conclusion. -/
theorem graph_epsilonTwo_radius_two_configuration
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w)) :
    b (family P) = 2 ∨
      (6 ≤ b (family P) ∧ ∃ t y : Vertex (family P),
        (graph (family P)).Adj w t ∧ (graph (family P)).Adj t y ∧
        (graph (family P)).dist v t + 1 = b (family P) ∧
        (graph (family P)).dist v y + 2 = b (family P) ∧
        V (family P) v 2 ≤ Q (family P) y ∧
        (¬ V (family P) v 2 ≤ Q (family P) t) ∧
        ⁅V (family P) v 2,⁅V (family P) v 2,V (family P) t 1⁆⁆ = ⊥) := by
  rcases graph_epsilonTwo_distance_gap h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ with hb | hb
  · exact Or.inl hb
  right
  have hvw : v ≠ w := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨t,hwt,hdt⟩ := exists_predecessor (family P) h.generate v w hvw
  rw [hc.1] at hdt
  have hvt : v ≠ t := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdt
    omega
  obtain ⟨y,hty,hdy⟩ := exists_predecessor (family P) h.generate v t hvt
  have hvy : v ≠ y := by
    intro he
    subst y
    simp only [SimpleGraph.dist_self] at hdy
    omega
  obtain ⟨x,hyx,hdx⟩ := exists_predecessor (family P) h.generate v y hvy
  have hcore := graph_epsilonTwo_radius_two_le_core h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hty hyx hdu hdt hdy hdx hepsilon hnat₀ hnat₁
  have hesc := graph_radius_two_escape_of_maximal_edges h hS hc hne (by omega) hsyl
    (fun _ he => graph_edge_isCoatom h he)
  refine ⟨hb,t,y,hwt,hty,hdt,by omega,hcore,?_,
    graph_radius_two_triple_commutator h hS hdt (by omega)⟩
  intro hh
  exact hesc ((hh.trans (source_Z_Q_U h t).2).trans
    ((ballKernel_one_le_edge (family P) hwt.symm).trans inf_le_right))

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
