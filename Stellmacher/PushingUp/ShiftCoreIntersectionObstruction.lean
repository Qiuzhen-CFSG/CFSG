module

public import Stellmacher.PushingUp.DistanceTwoShift

/-!
# The shared core cannot be normal in the left stabilizer

For the distance-two shift of a critical pair with `b ≥ 6`, this module
proves that `Q_a ∩ Q_u` is not normal in `G_a`. This is the final contradiction
in Stellmacher, *Pushing up*, Arch. Math. 46 (1986), proof of (2.4), p. 13.
The upper-bound proof establishes precisely the normality ruled out here.

Choose a common neighbor `d` of `a` and `u`, and the first neighbor `e` on a
shortest path from `a` to the shifted critical endpoint `c`. An element of
`G_a` carries `d` to `e` and `u` to a vertex `μ` adjacent to `e`. Therefore
`d(c,μ) ≤ b−2 < b`. Minimality of the critical distance puts `Z_c` in both
`Q_a` and `Q_μ`. If the shared core were normal in `G_a`, transport under
the right action would identify `Q_a ∩ Q_μ` with `Q_a ∩ Q_u`. Consequently
`Z_c ≤ Q_u`, contradicting the reverse critical pair `(c,u)`.

The distance estimate uses a shortest walk and a triangle inequality; the
core transport and the equality of M-side neighborhood kernels with their
2-cores use the public local-kernel APIs.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u
variable {M : Type u} [Group M] [Finite M]

/-- The shifted core intersection is not normal in the left stabilizer
when the critical distance is at least six. -/
public theorem shift_coreIntersection_not_normal_left
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S) (hcrit : IsCriticalPair S a a')
    (hge : 6 ≤ criticalDistance S)
    (hframe : DistanceTwoShift.Frame S a a' c)
    (hshift : DistanceTwoShift.Conclusion S a a' c u) :
    ¬ ((vertexTwoCore S a ⊓ vertexTwoCore S u).subgroupOf
      (stabilizer S a)).Normal := by
  intro hnormal
  have hb : 0 < criticalDistance S := by omega
  have ha : InMVertexOrbit S a := hcrit.1
  have hu : InMVertexOrbit S u := hshift.shifted_critical.1
  have hNested := stabilizer_isSL2Two_nested_of_mOrbit S u hu hA
  have hres : HasMinimalFrattiniResidual S u := by
    simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
      VertexFrattiniQuotient, VertexCoreQuotient] using
      sl2Two_twoResidual_isMinimalNormal hNested
  have hreverse := (criticalPair_commutator T hTS hP hSne u c
    hshift.shifted_critical hb hres).reverse_critical
  have hc : InMVertexOrbit S c := hreverse.1
  have hed : (cosetGraph S).edist a u = 2 := by
    rw [← (cosetGraph_connected S a u).coe_dist_eq_edist,
      hshift.distance_two]
    rfl
  obtain ⟨d, hd⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  have had : Adjacent S a d := (cosetGraph_adj S a d).mp hd.1
  have hdu : Adjacent S d u :=
    adjacent_symm S ((cosetGraph_adj S u d).mp hd.2)
  obtain ⟨p, hp⟩ := (cosetGraph_connected S).exists_walk_length_eq_dist a c
  have hplen : p.length + 2 = criticalDistance S := hp ▸ hframe.left_length
  let e := p.getVert 1
  have hae : Adjacent S a e := by
    apply (cosetGraph_adj S a e).mp
    simpa [e] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hec : (cosetGraph S).dist e c + 1 = (cosetGraph S).dist a c := by
    have hdrop := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_drop 1)
    simp only [SimpleGraph.Walk.drop_length] at hdrop
    change p.length - 1 = (cosetGraph S).dist e c at hdrop
    omega
  obtain ⟨g, hg, hgde⟩ := stabilizer_transitive_neighbors S a had hae
  let μ := act S g u
  have heμ : Adjacent S e μ := by
    simpa [μ, hgde] using (adjacent_act_iff S g d u).mpr hdu
  have hμ : InMVertexOrbit S μ := by
    obtain ⟨k, hk⟩ := hu
    refine ⟨k * g, ?_⟩
    rw [act_mul, ← hk]
  have hcμ : (cosetGraph S).dist c μ < criticalDistance S := by
    have htri := (cosetGraph_connected S).dist_triangle (u := c) (v := e) (w := μ)
    have heμdist : (cosetGraph S).dist e μ = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj S e μ).mpr heμ)
    have hce : (cosetGraph S).dist c e = (cosetGraph S).dist e c :=
      SimpleGraph.dist_comm
    have hleft := hframe.left_length
    omega
  have hZcQa : vertexZ S c ≤ vertexTwoCore S a := by
    rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS a e ha hae]
    apply vertexZ_le_neighborhoodKernel_of_dist_lt S hc
    rw [SimpleGraph.dist_comm]
    have hleft := hframe.left_length
    omega
  have hZcQμ : vertexZ S c ≤ vertexTwoCore S μ := by
    rw [← mVertex_neighborhoodKernel_eq_twoCore S T hTS μ e hμ (adjacent_symm S heμ)]
    exact vertexZ_le_neighborhoodKernel_of_dist_lt S hc hcμ
  let K : Subgroup (FreeAmalgam S) := vertexTwoCore S a ⊓ vertexTwoCore S u
  let conj : FreeAmalgam S →* FreeAmalgam S := (MulAut.conj g⁻¹).toMonoidHom
  have hKGa : K ≤ stabilizer S a :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  have hnormalizer : stabilizer S a ≤ Subgroup.normalizer (K : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKGa).mp hnormal
  have hKmap : K.map conj = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hnormalizer ((stabilizer S a).inv_mem hg))
  have hgamap : (vertexTwoCore S a).map conj = vertexTwoCore S a := by
    have hga : act S g a = a := hg
    simpa [conj, hga] using (vertexTwoCore_act_eq_map S g a).symm
  have hQμ : vertexTwoCore S μ = (vertexTwoCore S u).map conj := vertexTwoCore_act_eq_map S g u
  have hinf : vertexTwoCore S a ⊓ vertexTwoCore S μ = K := by
    rw [hQμ, ← hgamap, ← Subgroup.map_inf _ _ conj (MulAut.conj g⁻¹).injective]
    exact hKmap
  have hZcQu : vertexZ S c ≤ vertexTwoCore S u := by
    have hZcK : vertexZ S c ≤ K := by
      rw [← hinf]
      exact le_inf hZcQa hZcQμ
    exact hZcK.trans inf_le_right
  apply hreverse.2.2
  rw [mVertex_neighborhoodKernel_eq_twoCore S T hTS u d hu (adjacent_symm S hdu)]
  exact hZcQu

end Stellmacher.PushingUp
