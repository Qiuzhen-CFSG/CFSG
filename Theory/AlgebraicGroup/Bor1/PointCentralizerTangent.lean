module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.TangentIntersectionFoundation
public import Theory.AlgebraicGroup.Morphism.EndomorphismPullback

/-!
# Characteristic-zero point-centralizer tangents

This module proves the point-centralizer tangent formula from exact
characteristic-zero tangent control for intersections of closed subgroups.
The proof realizes a fixed subgroup as the intersection of the graphs of an
endomorphism and the identity, then specializes to conjugation by an arbitrary
point.  Bor1 Chapter 3, 9.1 states that separability, and hence this tangent
exactness, is automatic in characteristic zero; no semisimplicity hypothesis
is used.  The graph/equalizer reduction is formal, while the intersection
step uses the Cartier and Hopf reducedness foundation in
`ClosedSubgroup.TangentIntersectionFoundation`, originating in Bor1 Chapter
3, 9.1's automatic characteristic-zero separability assertion.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

private theorem identityTangent_range_inter_eq
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    LinearMap.range
        (identityTangentMorphismLinearMap (B.inter C).inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  exact identityTangent_range_eq_inf_charZero B C

private noncomputable def pointConjugationMorphism
    (G : Variety k) [AlgebraicGroup G] (s : Variety.Point G) :
    AlgebraicGroup.Morphism G G where
  toVariety := AlgebraicGroup.conjugationByMorphism G s
  map_one := by
    rw [AlgebraicGroup.conjugationByMorphism_apply]
    simp
  map_mul := by
    intro x y
    simp only [AlgebraicGroup.conjugationByMorphism_apply]
    group

private theorem identityTangentMorphismLinearMap_pointConjugation
    (G : Variety k) [AlgebraicGroup G] (s : Variety.Point G) :
    identityTangentMorphismLinearMap (pointConjugationMorphism G s) =
      identityTangentConjugationLinearMap G s := rfl

private noncomputable def graphMorphism
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    AlgebraicGroup.Morphism G (Variety.prod G H) :=
  AlgebraicGroup.Morphism.prod (AlgebraicGroup.Morphism.id G) f

private theorem identityTangent_graph_eq_of_eq
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f g : AlgebraicGroup.Morphism G H)
    (D : IdentityPointDerivation G)
    (hfg : identityTangentMorphismLinearMap f D =
      identityTangentMorphismLinearMap g D) :
    identityTangentMorphismLinearMap (graphMorphism f) D =
      identityTangentMorphismLinearMap (graphMorphism g) D := by
  apply coordinateTangentMap_injective (Variety.prod G H)
  funext i
  cases i with
  | inl i =>
      let cG := Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)
      let cP := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inl i))
      have hf : (graphMorphism f).toVariety.pullbackAlgHom cP = cG := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [cP, cG, graphMorphism, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.prod, AlgebraicGroup.Morphism.id,
          Variety.Morphism.id,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      have hg : (graphMorphism g).toVariety.pullbackAlgHom cP = cG := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [cP, cG, graphMorphism, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.prod, AlgebraicGroup.Morphism.id,
          Variety.Morphism.id,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      change D ((graphMorphism f).toVariety.pullbackAlgHom cP) =
        D ((graphMorphism g).toVariety.pullbackAlgHom cP)
      rw [hf, hg]
  | inr i =>
      let cH := Variety.PolynomialFunction.ofPolynomial H (MvPolynomial.X i)
      let cP := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inr i))
      have hf : (graphMorphism f).toVariety.pullbackAlgHom cP =
          f.toVariety.pullbackAlgHom cH := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [cP, cH, graphMorphism, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.prod, Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      have hg : (graphMorphism g).toVariety.pullbackAlgHom cP =
          g.toVariety.pullbackAlgHom cH := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [cP, cH, graphMorphism, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.prod, Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      change D ((graphMorphism f).toVariety.pullbackAlgHom cP) =
        D ((graphMorphism g).toVariety.pullbackAlgHom cP)
      rw [hf, hg]
      exact congrArg (fun E : IdentityPointDerivation H => E cH) hfg

private theorem identityTangent_graph_mem_range
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (A : ClosedSubgroup (Variety.prod G H))
    (hA : A = (graphMorphism f).imageClosedSubgroup)
    (D : IdentityPointDerivation G) :
    letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
    identityTangentMorphismLinearMap (graphMorphism f) D ∈
      LinearMap.range
        (identityTangentMorphismLinearMap A.inclusion) := by
  let graph := graphMorphism f
  letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  let hmap : ∀ x, graph.onPoints x ∈ A.toSubgroup := by
    intro x
    rw [hA]
    exact ⟨x, rfl⟩
  let r : AlgebraicGroup.Morphism G A.carrierVariety :=
    graph.codRestrictClosedSubgroup A hmap
  have hfactor : A.inclusion.comp r = graph := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact graph.codRestrictClosedSubgroup_inclusion_apply A hmap x
  refine ⟨identityTangentMorphismLinearMap r D, ?_⟩
  calc
    identityTangentMorphismLinearMap A.inclusion
        (identityTangentMorphismLinearMap r D) =
        identityTangentMorphismLinearMap (A.inclusion.comp r) D := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap graph D := by rw [hfactor]

private theorem identityTangent_equalizer_range_eq_ker_sub
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f g : AlgebraicGroup.Morphism G H) :
    let E := f.equalizerClosedSubgroup g
    LinearMap.range (identityTangentMorphismLinearMap E.inclusion) =
      LinearMap.ker
        (identityTangentMorphismLinearMap f -
          identityTangentMorphismLinearMap g) := by
  let E := f.equalizerClosedSubgroup g
  let graphF := graphMorphism f
  let graphG := graphMorphism g
  let A := graphF.imageClosedSubgroup
  let B := graphG.imageClosedSubgroup
  let I := A.inter B
  letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  letI : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
  apply le_antisymm
  · rintro D ⟨X, rfl⟩
    rw [LinearMap.mem_ker]
    have hfactor : f.comp E.inclusion = g.comp E.inclusion := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      exact (f.mem_equalizerClosedSubgroup_iff g
        (E.inclusion.onPoints x)).mp (E.pointEquiv x).property
    have hfg :
        identityTangentMorphismLinearMap f
            (identityTangentMorphismLinearMap E.inclusion X) =
          identityTangentMorphismLinearMap g
            (identityTangentMorphismLinearMap E.inclusion X) := by
      calc
        identityTangentMorphismLinearMap f
            (identityTangentMorphismLinearMap E.inclusion X) =
            identityTangentMorphismLinearMap (f.comp E.inclusion) X := by
          rw [identityTangentMorphismLinearMap_comp]
          rfl
        _ = identityTangentMorphismLinearMap (g.comp E.inclusion) X := by
          rw [hfactor]
        _ = identityTangentMorphismLinearMap g
            (identityTangentMorphismLinearMap E.inclusion X) := by
          rw [identityTangentMorphismLinearMap_comp]
          rfl
    exact sub_eq_zero.mpr hfg
  · intro D hD
    rw [LinearMap.mem_ker] at hD
    have hfg : identityTangentMorphismLinearMap f D =
        identityTangentMorphismLinearMap g D := sub_eq_zero.mp hD
    let P : IdentityPointDerivation (Variety.prod G H) :=
      identityTangentMorphismLinearMap graphF D
    have hPgraph :
        identityTangentMorphismLinearMap graphG D = P := by
      exact (identityTangent_graph_eq_of_eq f g D hfg).symm
    have hPA : P ∈ LinearMap.range
        (identityTangentMorphismLinearMap A.inclusion) :=
      identityTangent_graph_mem_range f A rfl D
    have hPB : P ∈ LinearMap.range
        (identityTangentMorphismLinearMap B.inclusion) := by
      rw [← hPgraph]
      exact identityTangent_graph_mem_range g B rfl D
    have hPI : P ∈ LinearMap.range
        (identityTangentMorphismLinearMap I.inclusion) := by
      rw [identityTangent_range_inter_eq A B]
      exact Submodule.mem_inf.mpr ⟨hPA, hPB⟩
    let q : AlgebraicGroup.Morphism I.carrierVariety G :=
      (AlgebraicGroup.Morphism.fst G H).comp I.inclusion
    have hqmap : ∀ x, q.onPoints x ∈ E.toSubgroup := by
      intro x
      rw [f.mem_equalizerClosedSubgroup_iff g]
      let z := I.inclusion.onPoints x
      have hzI : z ∈ I.toSubgroup := (I.pointEquiv x).property
      have hzAB := (ClosedSubgroup.mem_inter_iff A B z).mp hzI
      have hzA : z ∈ graphF.image := hzAB.1
      have hzB : z ∈ graphG.image := hzAB.2
      rcases hzA with ⟨a, ha⟩
      rcases hzB with ⟨b, hb⟩
      have habPair : (a, f.onPoints a) = (b, g.onPoints b) := by
        change Variety.prodPointEquiv G H (graphF.onPoints a) =
          Variety.prodPointEquiv G H (graphG.onPoints b)
        exact congrArg (Variety.prodPointEquiv G H) (ha.trans hb.symm)
      have hab : a = b := congrArg Prod.fst habPair
      have hfgab : f.onPoints a = g.onPoints b :=
        congrArg Prod.snd habPair
      have hqa : q.onPoints x = a := by
        change (Variety.prodPointEquiv G H z).1 = a
        rw [← ha]
        rfl
      rw [hqa]
      simpa [hab] using hfgab
    let p : AlgebraicGroup.Morphism I.carrierVariety E.carrierVariety :=
      q.codRestrictClosedSubgroup E hqmap
    have hpfactor : E.inclusion.comp p = q := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      exact q.codRestrictClosedSubgroup_inclusion_apply E hqmap x
    rcases hPI with ⟨X, hX⟩
    refine ⟨identityTangentMorphismLinearMap p X, ?_⟩
    have hfstGraph :
        (AlgebraicGroup.Morphism.fst G H).comp graphF =
          AlgebraicGroup.Morphism.id G := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      rfl
    calc
      identityTangentMorphismLinearMap E.inclusion
          (identityTangentMorphismLinearMap p X) =
          identityTangentMorphismLinearMap (E.inclusion.comp p) X := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap q X := by rw [hpfactor]
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          (identityTangentMorphismLinearMap I.inclusion X) := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          P := by rw [hX]
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          (identityTangentMorphismLinearMap graphF D) := rfl
      _ = identityTangentMorphismLinearMap
          ((AlgebraicGroup.Morphism.fst G H).comp graphF) D := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap
          (AlgebraicGroup.Morphism.id G) D := by rw [hfstGraph]
      _ = D := by
        rw [identityTangentMorphismLinearMap_id]
        rfl

private lemma mem_cyclicClosure_centralizer_of_commute
    {G : Variety k} [AlgebraicGroup G] (s x : Variety.Point G)
    (hcomm : s * x = x * s) :
    x ∈ (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer := by
  change x ∈ Subgroup.centralizer
    ((subgroupZariskiClosure G (Subgroup.zpowers s)).toSubgroup :
      Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let Z : Set (Variety.Point G) := {z | z * x = x * z}
  have hZclosed : IsClosed Z := by
    apply Variety.isClosed_iff_isZariskiClosed.mpr
    simpa [Z, AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply] using
      Variety.Morphism.isZariskiClosed_equalizer
        (AlgebraicGroup.rightMulMorphism G x)
        (AlgebraicGroup.leftMulMorphism G x)
  have hpowers : (Subgroup.zpowers s : Set (Variety.Point G)) ⊆ Z := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact (show Commute s x from hcomm).zpow_left n
  exact closure_minimal hpowers hZclosed hy

private lemma commute_of_mem_cyclicClosure_centralizer
    {G : Variety k} [AlgebraicGroup G] (s x : Variety.Point G)
    (hx : x ∈ (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer) :
    s * x = x * s := by
  have hs : s ∈
      (subgroupZariskiClosure G (Subgroup.zpowers s)).toSubgroup :=
    subset_closure (Subgroup.mem_zpowers s)
  exact (Subgroup.mem_centralizer_iff.mp hx) s hs

/-- Over an algebraically closed characteristic-zero field, the identity
tangent of the centralizer of the cyclic Zariski closure of any point is
exactly the fixed subspace of tangent conjugation by that point. -/
public theorem identityTangent_pointCentralizer_range_eq_fixed
    (G : Variety k) [AlgebraicGroup G] (s : Variety.Point G) :
    let C := (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer
    LinearMap.range (identityTangentMorphismLinearMap C.inclusion) =
      LinearMap.ker
        (identityTangentConjugationLinearMap G s - LinearMap.id) := by
  let f := pointConjugationMorphism G s
  let g := AlgebraicGroup.Morphism.id G
  let E := f.equalizerClosedSubgroup g
  let C := (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer
  have hEC : E = C := by
    apply SetLike.ext
    intro x
    change x ∈ (f.equalizerClosedSubgroup g).toSubgroup ↔ x ∈ C.toSubgroup
    rw [f.mem_equalizerClosedSubgroup_iff g]
    change s * x * s⁻¹ = x ↔ x ∈ C.toSubgroup
    constructor
    · intro hx
      apply mem_cyclicClosure_centralizer_of_commute s x
      calc
        s * x = (s * x * s⁻¹) * s := by group
        _ = x * s := by rw [hx]
    · intro hx
      have hcomm := commute_of_mem_cyclicClosure_centralizer s x hx
      rw [hcomm]
      group
  have hEqualizer := identityTangent_equalizer_range_eq_ker_sub f g
  change LinearMap.range (identityTangentMorphismLinearMap E.inclusion) =
      LinearMap.ker
        (identityTangentMorphismLinearMap f -
          identityTangentMorphismLinearMap g) at hEqualizer
  rw [hEC] at hEqualizer
  simpa [f, g, C, identityTangentMorphismLinearMap_pointConjugation] using
    hEqualizer


end Theory.AlgebraicGroup.Bor1
