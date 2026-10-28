module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.Completion
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootPlanes

/-!
# Chosen F4 root transport and its plane-relation assembly

The exact integral Geck routes give an all-root word map to the literal
completion of the two-node relations. Its signed simple-root marking,
evaluation in the matrix cover, and individual root additive laws hold over
every field, without any global presentation assumption.

The Curtis--Tits proof still needs two independent geometric inputs:
`TransportCoherent` is independence of marked root transport inside the
completion, and `HasPairPlaneCharts` moves an entire root plane into a
standard pair in the actual matrix group. Neither input is asserted here.
Given both, a plane identity word is conjugated to an actual pair identity;
its image is then a defining relator of the completion. This proves the
literal plane-relation clause consumed by the two-node kernel assembly.

Sources: GLS3, Theorem 2.9.3 and Lemma 2.9.4, especially the normalizer,
root-transport and plane-conjugation arguments in
`refs/KGroup/GLS3/chapter2.tex`, lines 1393--1462. The chosen-route formulas
are those of `IntegralRootCurveSimpleGeneration`, retaining all Geck signs
and the original parameters, including in characteristic three.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open scoped Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- The positive Tits word, with the same multiplication order as the integral matrices. -/
def transportTitsWord : List typeF4RootPairing_base.support → Word F
  | [] => 1
  | i :: w =>
      FreeGroup.of (true, typeF4RootPairing_baseEquiv.symm i, (1 : F)) *
      FreeGroup.of (false, typeF4RootPairing_baseEquiv.symm i, (-1 : F)) *
      FreeGroup.of (true, typeF4RootPairing_baseEquiv.symm i, (1 : F)) *
      transportTitsWord w

@[simp] theorem transportTitsWord_nil : transportTitsWord F [] = 1 := rfl

theorem transportTitsWord_append (w v : List typeF4RootPairing_base.support) :
    transportTitsWord F (w ++ v) = transportTitsWord F w * transportTitsWord F v := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [List.cons_append, transportTitsWord, ih, mul_assoc]

theorem coverEvaluation_transportTitsWord (w : List typeF4RootPairing_base.support) :
    (coverEvaluation F (transportTitsWord F w)).val =
      rootCurveTitsWord (P := typeF4RootPairing) (S := F) w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [transportTitsWord, map_mul, coverEvaluation_of, Subgroup.coe_mul,
      coverSimple_val, ih, rootCurveTitsWord_cons]
    simp only [sourceIndex, Equiv.apply_symm_apply]
    rfl

/-- A signed simple root transported along a specified Tits word. -/
def transportRouteWord (w : List typeF4RootPairing_base.support)
    (s : Bool) (i : Fin 4) (t : F) : Word F :=
  transportTitsWord F w * FreeGroup.of (s, i, t) * (transportTitsWord F w)⁻¹

theorem transportRouteWord_append (w v : List typeF4RootPairing_base.support)
    (s : Bool) (i : Fin 4) (t : F) :
    transportRouteWord F (w ++ v) s i t =
      transportTitsWord F w * transportRouteWord F v s i t *
        (transportTitsWord F w)⁻¹ := by
  simp only [transportRouteWord, transportTitsWord_append, mul_inv_rev]
  group

/-- The literal chosen route used to define the integral Geck root curve. -/
def transportRootWord (r : typeF4Roots) (t : F) : Word F :=
  let := typeF4RootPairing.indexNeg
  if typeF4RootPairing_base.IsPos r then
    let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    transportRouteWord F route.word true (typeF4RootPairing_baseEquiv.symm route.simple) t
  else
    let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    transportRouteWord F route.word false (typeF4RootPairing_baseEquiv.symm route.simple) t

@[simp] theorem transportRootWord_signed (s : Bool) (i : Fin 4) (t : F) :
    transportRootWord F (signedRoot s i) t = FreeGroup.of (s, i, t) := by
  let := typeF4RootPairing.indexNeg
  have hi := typeF4RootPairing_base.isPos_of_mem_support (sourceIndex i).property
  have hn : ¬typeF4RootPairing_base.IsPos (-(sourceIndex i) : typeF4Roots) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  cases s
  · change transportRootWord F (-(sourceIndex i) : typeF4Roots) t = _
    rw [transportRootWord, if_neg hn, neg_neg]
    simp only [rootRoute_word_simple, rootRoute_simple, transportRouteWord, transportTitsWord_nil, one_mul, inv_one, mul_one,
      sourceIndex, Equiv.symm_apply_apply]
  · change transportRootWord F (sourceIndex i) t = _
    rw [transportRootWord, if_pos hi]
    simp only [rootRoute_word_simple, rootRoute_simple, transportRouteWord, transportTitsWord_nil, one_mul, inv_one, mul_one,
      sourceIndex, Equiv.symm_apply_apply]

theorem coverEvaluation_transportRootWord (r : typeF4Roots) (t : F) :
    coverEvaluation F (transportRootWord F r t) =
      ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r t := by
  let := typeF4RootPairing.indexNeg
  apply Subtype.ext
  by_cases hr : typeF4RootPairing_base.IsPos r
  · simp only [transportRootWord, if_pos hr, transportRouteWord, map_mul, map_inv,
      coverEvaluation_of, Subgroup.coe_mul, Subgroup.coe_inv,
      coverEvaluation_transportTitsWord, coverSimple_val, sourceIndex, Equiv.apply_symm_apply]
    exact (rootCurveUnit_of_pos r hr t).symm
  · simp only [transportRootWord, if_neg hr, transportRouteWord, map_mul, map_inv,
      coverEvaluation_of, Subgroup.coe_mul, Subgroup.coe_inv,
      coverEvaluation_transportTitsWord, coverSimple_val, sourceIndex, Equiv.apply_symm_apply]
    exact (rootCurveUnit_of_neg r hr t).symm

/-- The candidate all-root map, before proving independence of transport. -/
def rootTransport : RootWord F →* PairCompletion F :=
  FreeGroup.lift fun x => pairQuotient F (transportRootWord F x.1 x.2)

@[simp] theorem rootTransport_of (r : typeF4Roots) (t : F) :
    rootTransport F (FreeGroup.of (r, t)) = pairQuotient F (transportRootWord F r t) :=
  FreeGroup.lift_apply_of

@[simp] theorem rootTransport_simple (s : Bool) (i : Fin 4) (t : F) :
    rootTransport F (FreeGroup.of (signedRoot s i, t)) =
      pairQuotient F (FreeGroup.of (s, i, t)) := by
  rw [rootTransport_of, transportRootWord_signed]

@[simp] theorem completionEvaluation_rootTransport (v : RootWord F) :
    completionEvaluation F (rootTransport F v) = rootEvaluation F v := by
  have h : (completionEvaluation F).comp (rootTransport F) = rootEvaluation F := by
    apply FreeGroup.ext_hom
    rintro ⟨r, t⟩
    simp only [MonoidHom.comp_apply, rootTransport_of, completionEvaluation_quotient,
      coverEvaluation_transportRootWord, rootEvaluation_of]
  exact DFunLike.congr_fun h v


/-- A Tits word written using the two Boolean node labels of a pair. -/
def pairTransportTitsWord : List Bool → PairWord F
  | [] => 1
  | k :: v =>
      FreeGroup.of (true, k, (1 : F)) * FreeGroup.of (false, k, (-1 : F)) *
        FreeGroup.of (true, k, (1 : F)) * pairTransportTitsWord v

/-- A signed simple root transported within a standard pair subgroup. -/
def pairTransportRouteWord (v : List Bool) (s k : Bool) (t : F) : PairWord F :=
  pairTransportTitsWord F v * FreeGroup.of (s, k, t) * (pairTransportTitsWord F v)⁻¹

/-- Read a Boolean pair word as a word in the actual numbered simple roots. -/
def pairTransportNodes (i j : Fin 4) (v : List Bool) :
    List typeF4RootPairing_base.support :=
  v.map fun k => sourceIndex (pairNode i j k)

theorem pairInclusion_pairTransportTitsWord (i j : Fin 4) (v : List Bool) :
    pairInclusion F i j (pairTransportTitsWord F v) =
      transportTitsWord F (pairTransportNodes i j v) := by
  induction v with
  | nil => simp [pairTransportTitsWord, pairTransportNodes]
  | cons k v ih =>
    simp only [pairTransportTitsWord, map_mul, pairInclusion_of, ih,
      pairTransportNodes, List.map_cons, transportTitsWord, sourceIndex,
      Equiv.symm_apply_apply]

theorem pairInclusion_pairTransportRouteWord (i j : Fin 4)
    (v : List Bool) (s k : Bool) (t : F) :
    pairInclusion F i j (pairTransportRouteWord F v s k t) =
      transportRouteWord F (pairTransportNodes i j v) s (pairNode i j k) t := by
  simp only [pairTransportRouteWord, map_mul, map_inv,
    pairInclusion_pairTransportTitsWord, pairInclusion_of, transportRouteWord]

/-- Completion-level independence of marked signed-simple-root transport.
The premise is an equality of actual Geck matrices; the conclusion must be
proved using local pair relations, not global injectivity. This is the
normalizer and Lemma 2.9.4 obligation in GLS3 §2.9.3. -/
def TransportCoherent : Prop :=
  ∀ (w v : List typeF4RootPairing_base.support) (s z : Bool)
    (i j : Fin 4) (t u : F),
    coverEvaluation F (transportRouteWord F w s i t) =
      coverEvaluation F (transportRouteWord F v z j u) →
    pairQuotient F (transportRouteWord F w s i t) =
      pairQuotient F (transportRouteWord F v z j u)

/-- Actual-matrix charts for entire root planes. A single Tits word moves the
plane into a standard pair. Each of its root elements then has a route using
only those two nodes, with the parameter determined by the literal equality.
This includes every intermediate B2 root. There is no completion hypothesis. -/
def HasPairPlaneCharts : Prop :=
  ∀ a b : typeF4Roots, ∃ (w : List typeF4RootPairing_base.support) (i j : Fin 4),
    ∀ (r : rootPlane a b) (t : F), ∃ (v : List Bool) (s k : Bool) (u : F),
      coverEvaluation F (transportTitsWord F w) *
          ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r.val t *
          (coverEvaluation F (transportTitsWord F w))⁻¹ =
        pairEvaluation F i j (pairTransportRouteWord F v s k u)

private theorem transportRootWord_is_route (r : typeF4Roots) (t : F) :
    ∃ (w : List typeF4RootPairing_base.support) (s : Bool) (i : Fin 4),
      transportRootWord F r t = transportRouteWord F w s i t := by
  unfold transportRootWord
  split <;> exact ⟨_, _, _, rfl⟩

/-- Coherence compares a plane-chart root with the fixed chosen root, retaining
its original parameter. -/
theorem rootTransport_conjugate_of_route_eq (hc : TransportCoherent F)
    (w v : List typeF4RootPairing_base.support) (s : Bool) (i : Fin 4) (t : F)
    (r : typeF4Roots) (u : F)
    (h : coverEvaluation F (transportRouteWord F v s i t) =
      coverEvaluation F (transportTitsWord F w) *
        ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r u *
        (coverEvaluation F (transportTitsWord F w))⁻¹) :
    pairQuotient F (transportRouteWord F v s i t) =
      pairQuotient F (transportTitsWord F w) * rootTransport F (FreeGroup.of (r, u)) *
        (pairQuotient F (transportTitsWord F w))⁻¹ := by
  obtain ⟨v₀, s₀, i₀, he⟩ := transportRootWord_is_route F r u
  have hv : coverEvaluation F (transportRouteWord F v s i t) =
      coverEvaluation F (transportRouteWord F (w ++ v₀) s₀ i₀ u) := by
    rw [transportRouteWord_append, ← he, map_mul, map_mul, map_inv,
      coverEvaluation_transportRootWord]
    exact h
  rw [hc v (w ++ v₀) s s₀ i i₀ t u hv, transportRouteWord_append, ← he,
    map_mul, map_mul, map_inv, rootTransport_of]

/-- The two geometric source obligations supply every literal plane relation.
The proof conjugates the whole plane word into one standard pair, where its
identity is a defining relator of the completion. -/
theorem rootTransport_planes_of_coherence_and_charts
    (hc : TransportCoherent F) (hcharts : HasPairPlaneCharts F)
    (a b : typeF4Roots) (v : RootPlaneWord F a b)
    (hv : rootPlaneEvaluation F a b v = 1) :
    rootTransport F (rootPlaneInclusion F a b v) = 1 := by
  obtain ⟨w, i, j, hchart⟩ := hcharts a b
  choose route sign node parameter hroute using hchart
  let κ : RootPlaneWord F a b →* PairWord F := FreeGroup.lift fun x =>
    pairTransportRouteWord F (route x.1 x.2) (sign x.1 x.2) (node x.1 x.2)
      (parameter x.1 x.2)
  let n := coverEvaluation F (transportTitsWord F w)
  let n' := pairQuotient F (transportTitsWord F w)
  have he : (pairEvaluation F i j).comp κ =
      (MulAut.conj n).toMonoidHom.comp (rootPlaneEvaluation F a b) := by
    apply FreeGroup.ext_hom
    rintro ⟨r, t⟩
    change pairEvaluation F i j
      (κ (FreeGroup.of (r, t))) = n * rootPlaneEvaluation F a b (FreeGroup.of (r, t)) * n⁻¹
    rw [show κ (FreeGroup.of (r, t)) =
      pairTransportRouteWord F (route r t) (sign r t) (node r t) (parameter r t) from
        FreeGroup.lift_apply_of]
    simpa only [rootPlaneEvaluation, MonoidHom.comp_apply, rootPlaneInclusion_of,
      rootEvaluation_of] using (hroute r t).symm
  have he' : ((pairQuotient F).comp (pairInclusion F i j)).comp κ =
      (MulAut.conj n').toMonoidHom.comp
        ((rootTransport F).comp (rootPlaneInclusion F a b)) := by
    apply FreeGroup.ext_hom
    rintro ⟨r, t⟩
    change pairQuotient F (pairInclusion F i j (κ (FreeGroup.of (r, t)))) =
      n' * rootTransport F (rootPlaneInclusion F a b (FreeGroup.of (r, t))) * n'⁻¹
    rw [show κ (FreeGroup.of (r, t)) =
      pairTransportRouteWord F (route r t) (sign r t) (node r t) (parameter r t) from
        FreeGroup.lift_apply_of,
      pairInclusion_pairTransportRouteWord, rootPlaneInclusion_of]
    apply rootTransport_conjugate_of_route_eq F hc
    rw [← pairInclusion_pairTransportRouteWord]
    exact (hroute r t).symm
  have hpair : pairEvaluation F i j (κ v) = 1 := by
    change ((pairEvaluation F i j).comp κ) v = 1
    rw [he, MonoidHom.comp_apply, hv, map_one]
  have hquot : pairQuotient F (pairInclusion F i j (κ v)) = 1 := by
    apply (pairQuotient_eq_one_iff F _).mpr
    apply Subgroup.subset_normalClosure
    exact ⟨i, j, κ v, hpair, rfl⟩
  have hconj : (MulAut.conj n') (rootTransport F (rootPlaneInclusion F a b v)) = 1 := by
    change (((MulAut.conj n').toMonoidHom).comp
      ((rootTransport F).comp (rootPlaneInclusion F a b))) v = 1
    rw [← he']
    exact hquot
  exact (MulAut.conj n').injective (hconj.trans (map_one _).symm)


private theorem pairQuotient_simple_add (s : Bool) (i : Fin 4) (t u : F) :
    pairQuotient F (FreeGroup.of (s, i, t + u)) =
      pairQuotient F (FreeGroup.of (s, i, t)) * pairQuotient F (FreeGroup.of (s, i, u)) := by
  have hlocal : pairGenerator F i i s true (t + u) =
      pairGenerator F i i s true t * pairGenerator F i i s true u := by
    apply Subtype.ext
    simp only [pairGenerator_val, Subgroup.coe_mul]
    cases s <;> exact ExceptionalSplit.elementaryRoot_add _ _ F _ t u
  have h := congrArg (pairEmbedding F i i) hlocal
  simpa only [map_mul, pairEmbedding_generator, pairNode, ite_self] using h

private theorem pairQuotient_route_add
    (w : List typeF4RootPairing_base.support) (s : Bool) (i : Fin 4) (t u : F) :
    pairQuotient F (transportRouteWord F w s i (t + u)) =
      pairQuotient F (transportRouteWord F w s i t) *
        pairQuotient F (transportRouteWord F w s i u) := by
  simp only [transportRouteWord, map_mul, map_inv, pairQuotient_simple_add]
  group

/-- Each chosen root curve already obeys the additive law using rank-one local
relations. No route-coherence premise is needed. -/
theorem rootTransport_add (r : typeF4Roots) (t u : F) :
    rootTransport F (FreeGroup.of (r, t + u)) =
      rootTransport F (FreeGroup.of (r, t)) * rootTransport F (FreeGroup.of (r, u)) := by
  simp only [rootTransport_of, transportRootWord]
  split_ifs <;> exact pairQuotient_route_add F _ _ _ t u

@[simp] theorem rootTransport_zero (r : typeF4Roots) :
    rootTransport F (FreeGroup.of (r, (0 : F))) = 1 := by
  have h := rootTransport_add F r 0 0
  rw [add_zero] at h
  apply mul_left_cancel (a := rootTransport F (FreeGroup.of (r, (0 : F))))
  simpa only [mul_one] using h.symm

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
