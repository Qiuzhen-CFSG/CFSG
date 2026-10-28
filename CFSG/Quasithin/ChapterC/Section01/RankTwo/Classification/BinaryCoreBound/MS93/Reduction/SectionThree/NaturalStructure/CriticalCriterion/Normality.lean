module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Escape
/-!
# Transport and normality of the source edge witness

A single witness to source (2.3)(d) transports by actual amalgam
conjugation. No choice of a covariant family is needed. To prove normality
two steps along a critical path, move its second vertex to the first using
the intervening vertex stabilizer. Step (2) gives an escaping conjugate;
(d) puts it inside the earlier endpoint X-layer, which centralizes the
witness from (c). This contradicts escape.

The elementary metric lemmas retain adjacency and exact geodesic distances,
and the normality conclusion includes containment in the local group.
Source: Meierfrankenfeld--Stellmacher (1993), (2.3), proof (4), p.858.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

omit [Finite M] in
@[simp] theorem act_inverse_cancel (f : FreeAmalgam R) (a : Vertex R) :
    act R f⁻¹ (act R f a) = a := by rw [← act_mul, mul_inv_cancel, act_one]

omit [Finite M] in
@[simp] theorem act_cancel_inverse (f : FreeAmalgam R) (a : Vertex R) :
    act R f (act R f⁻¹ a) = a := by rw [← act_mul, inv_mul_cancel, act_one]

/-- Transport a single source-(d) witness along the actual group action. -/
theorem EdgeWitness.conjugate {geometry : Geometry R} {a t : Vertex R}
    {A : Subgroup (FreeAmalgam R)} (hA : EdgeWitness R geometry a t A)
    (ha : color R a = false) (hat : Adjacent R a t) (f : FreeAmalgam R) :
    EdgeWitness R geometry (act R f a) (act R f t) (rightConjugate A f) := by
  have hAT := hA.le_edge R ha hat
  have hAG : A ≤ stabilizer R a := hAT.trans (edge_le_stabilizer R ha hat)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [X_act]
    exact map_mono hA.le_X
  · rw [Q_act]
    exact (normal_map_iff A (Q R t) hAT (MulAut.conj f⁻¹)).mpr hA.normal_edge
  · rw [stabilizer_act]
    exact fun hn => hA.not_normal_vertex
      ((normal_map_iff A (stabilizer R a) hAG (MulAut.conj f⁻¹)).mp hn)
  · intro hfa d hc hdist
    have hcolor : color R (act R f⁻¹ (act R f a)) = false := by simpa using ha
    have hback := (criticalPair_act_iff R f⁻¹ (act R f a) d
      (geometry.exists_critical _ hfa) (geometry.exists_critical _ hcolor)).mpr hc
    have hpair : CriticalPair R a (act R f⁻¹ d) (geometry.exists_critical a ha) := by
      simpa only [act_inverse_cancel] using hback
    have htd : (cosetGraph R).dist t (act R f⁻¹ d) + 1 = geometry.b R := by
      have hh := dist_act R f⁻¹ (act R f t) d
      rw [act_inverse_cancel] at hh
      rwa [hh]
    have hbound := map_mono (f := (MulAut.conj f⁻¹).toMonoidHom)
      (hA.critical_bound ha (act R f⁻¹ d) hpair htd)
    simpa only [rightConjugate, map_commutator, ← X_act, act_cancel_inverse] using hbound

omit [Finite M] in
/-- The two-step predecessor exists with its exact geodesic distances. -/
theorem exists_two_before (a a' : Vertex R) (h : 2 ≤ (cosetGraph R).dist a a') :
    ∃ e, (cosetGraph R).dist e a' = 2 ∧
      (cosetGraph R).dist a e + 2 = (cosetGraph R).dist a a' := by
  obtain ⟨t, ha't, hta⟩ := exists_adjacent_dist_sub_one R a' a (by
    rw [SimpleGraph.dist_comm] at h
    omega)
  obtain ⟨e, hte, hea⟩ := exists_adjacent_dist_sub_one R t a (by
    have hh : (cosetGraph R).dist a' a = (cosetGraph R).dist a a' := SimpleGraph.dist_comm
    omega)
  have hta'1 : (cosetGraph R).dist t a' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (adjacent_symm R ha't))
  have het1 : (cosetGraph R).dist e t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (adjacent_symm R hte))
  have h₁ := (cosetGraph_connected R).dist_triangle (u := e) (v := t) (w := a')
  have h₂ := (cosetGraph_connected R).dist_triangle (u := a') (v := e) (w := a)
  simp only [SimpleGraph.dist_comm (u := a') (v := a),
    SimpleGraph.dist_comm (u := e) (v := a),
    SimpleGraph.dist_comm (u := a') (v := e)] at hta hea h₂
  exact ⟨e, by omega, by omega⟩

/-- Either endpoint's X-layer is contained in the other's local group at the
critical distance; the first edge supplies the local containment. -/
theorem critical_X_le_stabilizer (geometry : Geometry R) (hC : EdgeCentralizerCondition R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    X R a ≤ stabilizer R a' := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hdist : (cosetGraph R).dist a' a = geometry.b R := by
    rw [SimpleGraph.dist_comm]
    exact hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨t, ha't, hta⟩ := exists_adjacent_dist_sub_one R a' a (by omega)
  exact (X_le_Q_of_dist_lt R geometry hC a ha t (by
    rw [geometry.distance_constant a ha, SimpleGraph.dist_comm]
    change (cosetGraph R).dist t a < geometry.b R
    omega)).trans (edge_le_stabilizer R ha' ha't)

omit [Finite M] in
/-- In the new critical pair, the moved edge is still the first edge. -/
theorem moved_edge_on_path (geometry : Geometry R)
    {a d t e : Vertex R} (hadj : Adjacent R a t) (hdt : Adjacent R d t)
    (hade : (cosetGraph R).dist a e + 2 = geometry.b R)
    (f : FreeAmalgam R) (hf : f ∈ stabilizer R a)
    (hd : color R (act R f d) = false)
    (hc : CriticalPair R (act R f d) e (geometry.exists_critical _ hd)) :
    (cosetGraph R).dist (act R f t) e + 1 = geometry.b R := by
  have hfix : act R f a = a := hf
  have h₁ : (cosetGraph R).dist (act R f d) (act R f t) = 1 := by
    rw [dist_act]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
  have h₂ : (cosetGraph R).dist (act R f t) a = 1 := by
    rw [← hfix, dist_act]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hadj))
  have hb' : (cosetGraph R).dist (act R f d) e = geometry.b R :=
    hc.1.trans (geometry.distance_constant _ hd)
  have hu := (cosetGraph_connected R).dist_triangle (u := act R f t) (v := a) (w := e)
  have hl := (cosetGraph_connected R).dist_triangle (u := act R f d) (v := act R f t) (w := e)
  omega

/-- A critical commutator bound places the transported source witness inside
the X-layer at the new far endpoint. -/
theorem EdgeWitness.le_far_X {geometry : Geometry R} (hC : EdgeCentralizerCondition R)
    (hb : 0 < geometry.b R) {a t : Vertex R} {A : Subgroup (FreeAmalgam R)}
    (hA : EdgeWitness R geometry a t A) (ha : color R a = false)
    (e : Vertex R) (hc : CriticalPair R a e (geometry.exists_critical a ha))
    (hte : (cosetGraph R).dist t e + 1 = geometry.b R) : A ≤ X R e :=
  (hA.critical_bound ha e hc hte).trans
    (le_normalizer_iff_commutator_le_right.mp
      ((critical_X_le_stabilizer R geometry hC hb a ha e hc).trans (X_normalized R e)))

omit [Finite M] in
/-- The endpoint X-layer centralizes every subgroup lying in its kernel. -/
theorem le_normalizer_of_le_Q {a : Vertex R} {A W : Subgroup (FreeAmalgam R)}
    (hA : A ≤ Q R a) (hW : W ≤ X R a) : W ≤ normalizer A := by
  apply le_normalizer_iff.mpr
  intro w hw x hx
  have hh : w * x = x * w := ((mem_omegaCenter_iff.mp (hW hw)).2.2 x (hA hx)).symm
  simpa only [hh, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- Source (2.3), proof step (4): the given single-edge witness is normal at
the second vertex of each critical path through that edge. -/
theorem normal_at_second {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t c : Vertex R) (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a')
    (A : Subgroup (FreeAmalgam R)) (hA : EdgeWitness R geometry a t A) :
    A ≤ stabilizer R c ∧ (A.subgroupOf (stabilizer R c)).Normal := by
  have hC := source.edgeCentralizerCondition geometry
  have hpos : 0 < geometry.b R := by omega
  have hAc : A ≤ stabilizer R c :=
    (hA.le_X.trans (X_le_Q_of_dist_lt R geometry hC a ha c (by
      rw [geometry.distance_constant a ha]
      change (cosetGraph R).dist a c < geometry.b R
      omega))).trans (fun _ hx => hx.1)
  refine ⟨hAc, ?_⟩
  by_contra hnotAc
  have hb' : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  have hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected R).dist_triangle (u := t) (v := c) (w := a')
    omega
  obtain ⟨e, he, hae⟩ := exists_two_before R a a' (by omega)
  obtain ⟨f, hft, hfc⟩ := stabilizer_transitive_neighbors R t (adjacent_symm R hct)
    (adjacent_symm R hat)
  have hfix : act R f t = t := hft
  have hdat : Adjacent R (act R f a) t := by
    rw [← hfix]
    exact (adjacent_act_iff R f a t).mpr hat
  have hda : (cosetGraph R).dist (act R f a) a = 2 := by
    calc
      _ = (cosetGraph R).dist (act R f a) (act R f c) := congrArg _ hfc.symm
      _ = (cosetGraph R).dist a c := dist_act R f a c
      _ = 2 := hac
  have hfwd := critical_nonnormal_forward R geometry hC a ha (by
    rw [geometry.distance_constant a ha]; exact hpos) a' hc c hac hpath
  have hnotZ : ¬ ((Z R (act R f a) ⊔ X R a).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hfwd.2
    apply (normal_map_iff (Z R a ⊔ X R c) (stabilizer R c) hfwd.1 (MulAut.conj f⁻¹)).mp
    have hmap : (Z R a ⊔ X R c).map (MulAut.conj f⁻¹).toMonoidHom =
        Z R (act R f a) ⊔ X R a := by
      rw [Subgroup.map_sup, ← Z_act, ← X_act, hfc]
    rw [hmap, ← stabilizer_act, hfc]
    exact hn
  have hAf := hA.conjugate R ha hat f
  rw [hfix] at hAf
  have hdf : color R (act R f a) = false := by rwa [action_preserves_color]
  have hAfnot : ¬ ((rightConjugate A f).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hnotAc
    apply (normal_map_iff A (stabilizer R c) hAc (MulAut.conj f⁻¹)).mp
    rw [← stabilizer_act, hfc]
    exact hn
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  obtain ⟨g, hg, hdg, hpair, hn⟩ := escape_pair R source geometry hb hgen a ha a' hc t hat hta'
    e he hae (act R f a) hdat hda hnotZ (rightConjugate A f)
    (hAf.le_edge R hdf hdat) hAf.normal_edge hAfnot W hW
  have hAfg := hAf.conjugate R hdf hdat g
  have hsmall := hAfg.le_far_X R hC hpos hdg e hpair
    (moved_edge_on_path R geometry hat hdat (by omega) g hg hdg hpair)
  have hecol := critical_endpoint_color R _ hdg _ hpair
  have hXe : X R e ≤ Q R a' := X_le_Q_of_dist_lt R geometry hC e hecol a' (by
    rw [geometry.distance_constant e hecol]
    change (cosetGraph R).dist e a' < geometry.b R
    omega)
  exact hn (le_normalizer_of_le_Q R (hsmall.trans hXe) hW.le_X)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
