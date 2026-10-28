module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Reduction
public import Theory.AlgebraicGroup.Bor1.SmoothSemisimpleFixedCotangent
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator

/-!
External torus fixed tangents, as used in Borel III, 9.4(1).

A torus normalizing a closed subgroup acts on that subgroup by conjugation.
Every embedded identity tangent fixed by this action comes from its actual
pointwise centralizer. Neither containment of the torus in the subgroup nor
ambient normality of the subgroup is needed.

For one semisimple normalizing point, restriction of regular functions carries
the ambient conjugation eigenvectors onto a spanning family in the subgroup's
coordinate ring. Smoothness makes the pullback-difference ideal radical, so an
invariant derivation annihilates the ideal of the fixed points and lifts through
the centralizer inclusion. Noetherian minimality then handles the whole torus:
cut a minimal normalized subgroup carrying the tangent by one point centralizer.
Commutativity of the torus preserves normalization after this cut.

Sources: `refs/KGroup/Bor1/Chapter3.tex`, Proposition 9.1, the corollary to 9.2,
and Proposition 9.4(1). This proves the external-action tangent input of
`FixedSubgroups.Reduction`, independently of tangent weight decomposition.
-/

universe u
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
open Bor1
variable {k : Type u} [Field k] [IsAlgClosed k]

private def normalizedConjugation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s : Variety.Point G) (hs : s ∈ H.normalizer) :
    AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety := by
  let c : AlgebraicGroup.Morphism G G := {
    toVariety := AlgebraicGroup.conjugationByMorphism G s
    map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
    map_mul := by
      intro x y
      simp only [AlgebraicGroup.conjugationByMorphism_apply]
      group }
  exact (c.comp H.inclusion).codRestrictClosedSubgroup H (fun x =>
    (Subgroup.mem_normalizer_iff.mp hs _).mp (H.pointEquiv x).property)

omit [IsAlgClosed k] in
private lemma normalizedConjugation_include
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s : Variety.Point G) (hs : s ∈ H.normalizer)
    (x : Variety.Point H.carrierVariety) :
    H.includePoint ((normalizedConjugation H s hs).onPoints x) =
      s * H.includePoint x * s⁻¹ := by
  change H.inclusion.onPoints _ = _
  simp only [normalizedConjugation]
  rfl

omit [IsAlgClosed k] in
private lemma weightVectors_span_of_surjective
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] A) (psi : B →ₐ[k] B) (r : A →ₐ[k] B)
    (hr : Function.Surjective r) (hcomm : ∀ a, psi (r a) = r (phi a))
    (hspan : Submodule.span k (weightVectors phi) = ⊤) :
    Submodule.span k (weightVectors psi) = ⊤ := by
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨a, rfl⟩ := hr b
  have ha : a ∈ Submodule.span k (weightVectors phi) := by rw [hspan]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
      apply Submodule.subset_span
      obtain ⟨c, hc⟩ := ha
      exact ⟨c, by rw [hcomm, hc, map_mul, AlgHom.commutes]⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span k (weightVectors psi)))
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

private lemma normalizedConjugation_weightVectors_span
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s : Variety.Point G) (hs : s ∈ H.normalizer) (hsemi : IsSemisimpleElement G s) :
    Submodule.span k (weightVectors (normalizedConjugation H s hs).toVariety.pullbackAlgHom) = ⊤ := by
  apply weightVectors_span_of_surjective
    (AlgebraicGroup.conjugationByMorphism G s).pullbackAlgHom
    _ H.inclusion.toVariety.pullbackAlgHom H.restrictionRingHom_surjective
  · intro a
    apply Variety.PolynomialFunction.ext
    intro x
    change a (H.includePoint ((normalizedConjugation H s hs).onPoints x)) =
      a (s * H.includePoint x * s⁻¹)
    rw [normalizedConjugation_include]
  · exact weightVectors_span_eq_top_of_locallyFinite_of_finitelySemisimple _
      (conjugationPullback_locallyFinite G s)
      (conjugationBy_semisimpleElement_isSemisimple s hsemi)

private lemma derivation_vanishes_on_fixedPoints_of_weightSpan
    (G : Variety k) [AlgebraicGroup G] (psi : AlgebraicGroup.Morphism G G)
    (hspan : Submodule.span k (weightVectors psi.toVariety.pullbackAlgHom) = ⊤)
    (D : Bor1.IdentityPointDerivation G)
    (hD : ∀ a, D (psi.toVariety.pullbackAlgHom a) = D a)
    (f : G.PolynomialFunction)
    (hf : f ∈ fixedPointVanishingIdeal G psi.toVariety) : D f = 0 := by
  let : Algebra.Smooth k G.PolynomialFunction := polynomialFunction_smooth_of_algebraicGroup G
  have heq := fixedPointDifferenceIdeal_eq_weightIdeal_of_weightVectors_span
    psi.toVariety.pullbackAlgHom hspan
  have hrad : (fixedPointDifferenceIdeal psi.toVariety.pullbackAlgHom).IsRadical := by
    rw [heq]
    exact weightIdeal_isRadical_of_weightVectors_span _ hspan
  rw [fixedPointVanishingIdeal_eq_radical_differenceIdeal, hrad.radical, heq] at hf
  have hboth : ∀ a ∈ Ideal.span (nontrivialWeightVectors psi.toVariety.pullbackAlgHom),
      D a = 0 ∧ a 1 = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        obtain ⟨c, hc, hcb⟩ := hb
        have hw : psi.toVariety.pullbackAlgHom b = c • b := by
          simpa only [Algebra.smul_def] using hcb
        constructor
        · have hd := hD b
          rw [hw, Derivation.map_smul D c b] at hd
          change c * D b = D b at hd
          by_contra hne
          exact hc ((mul_eq_right₀ hne).mp hd)
        · have hv : b (psi.toVariety.toFun 1) = c * b 1 := by
            have hv := congrArg (fun a : G.PolynomialFunction => a 1) hcb
            change b (psi.toVariety.toFun 1) = (algebraMap k G.PolynomialFunction c * b) 1 at hv
            simpa only [polynomialFunction_mul_apply,
              polynomialFunction_algebraMap_apply] using hv
          rw [psi.map_one] at hv
          by_contra hne
          exact hc ((mul_eq_right₀ hne).mp hv.symm)
    | zero => exact ⟨map_zero D, rfl⟩
    | add a b _ _ ha hb =>
        constructor
        · rw [map_add, ha.1, hb.1, add_zero]
        · change a 1 + b 1 = 0
          rw [ha.2, hb.2, add_zero]
    | smul c a _ ha =>
        constructor
        · change D (c * a) = 0
          rw [D.leibniz]
          change c 1 * D a + a 1 * D c = 0
          rw [ha.1, ha.2, mul_zero, zero_mul, add_zero]
        · change c 1 * a 1 = 0
          rw [ha.2, mul_zero]
  exact (hboth f hf).1

/-- The embedded tangent of a normalized subgroup lifts to the single-point
fixed subgroup whenever that point is semisimple. -/
public theorem externalSemisimplePoint_fixed_tangent
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s : Variety.Point G) (hs : s ∈ H.normalizer) (hsemi : IsSemisimpleElement G s)
    (D : IdentityPointDerivation G) (hDH : D ∈ closedSubgroupTangent H)
    (hfixed : Theory.AlgebraicGroup.identityTangentConjugationLinearMap G s D = D) :
    D ∈ closedSubgroupTangent (H.inter (semisimpleCommutatorPointCentralizer s)) := by
  obtain ⟨E, hE⟩ := hDH
  let psi := normalizedConjugation H s hs
  let r := H.inclusion.toVariety.pullbackAlgHom
  have hEr (a : G.PolynomialFunction) : E (r a) = D a := by
    exact congrArg (fun F : Bor1.IdentityPointDerivation G => F a) hE
  have hcomm (a : G.PolynomialFunction) :
      psi.toVariety.pullbackAlgHom (r a) =
        r ((AlgebraicGroup.conjugationByMorphism G s).pullbackAlgHom a) := by
    apply Variety.PolynomialFunction.ext
    intro x
    change a (H.includePoint (psi.onPoints x)) = a (s * H.includePoint x * s⁻¹)
    rw [normalizedConjugation_include]
  have hEinv (a : H.carrierVariety.PolynomialFunction) :
      E (psi.toVariety.pullbackAlgHom a) = E a := by
    obtain ⟨b, rfl⟩ := H.restrictionRingHom_surjective a
    change E (psi.toVariety.pullbackAlgHom (r b)) = E (r b)
    rw [hcomm, hEr, hEr]
    exact congrArg (fun F : IdentityPointDerivation G => F b) hfixed
  apply (identityTangent_inclusion_range_iff_vanishingIdeal _ D).mpr
  intro f hf
  rw [← hEr]
  apply derivation_vanishes_on_fixedPoints_of_weightSpan H.carrierVariety psi
    (normalizedConjugation_weightVectors_span H s hs hsemi) E hEinv
  rw [mem_fixedPointVanishingIdeal_iff]
  intro x hx
  change f (H.includePoint x) = 0
  apply ((H.inter (semisimpleCommutatorPointCentralizer s)).mem_vanishingIdeal_iff f).mp hf
  refine ⟨(H.pointEquiv x).property, ?_⟩
  have hxinc := congrArg H.includePoint hx
  change H.includePoint ((normalizedConjugation H s hs).onPoints x) = H.includePoint x at hxinc
  rw [normalizedConjugation_include] at hxinc
  change H.includePoint x ∈ Subgroup.centralizer ({s} : Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  subst y
  have h := congrArg (fun z : Variety.Point G => z * s) hxinc
  simpa [mul_assoc] using h

/-- Fixed embedded tangents for an external subtorus lift through the
pointwise-centralizer inclusion. -/
public theorem externalSubtorus_fixed_tangent
    {G : Variety k} [AlgebraicGroup G] (H Q : ClosedSubgroup G)
    (hQ : IsSubtorus Q) (hQN : Q ≤ H.normalizer)
    (D : IdentityPointDerivation G) (hDH : D ∈ closedSubgroupTangent H)
    (hfixed : ∀ q : Variety.Point Q.carrierVariety,
      Theory.AlgebraicGroup.identityTangentConjugationLinearMap G (Q.includePoint q) D = D) :
    D ∈ closedSubgroupTangent (H.pointwiseCentralizer Q) := by
  classical
  let qualifies : ClosedSubgroup G → Prop := fun V =>
    V ≤ H ∧ Q ≤ V.normalizer ∧ D ∈ closedSubgroupTangent V
  let closedSet : ClosedSubgroup G → TopologicalSpace.Closeds (Variety.Point G) :=
    fun V => ⟨(V : Set (Variety.Point G)),
      Variety.isClosed_iff_isZariskiClosed.mpr V.isZariskiClosed⟩
  let family : Set (TopologicalSpace.Closeds (Variety.Point G)) :=
    {A | ∃ V : ClosedSubgroup G, qualifies V ∧ A = closedSet V}
  have hfamily : family.Nonempty :=
    ⟨closedSet H, H, ⟨(fun _ hx => hx), hQN, hDH⟩, rfl⟩
  obtain ⟨A, hAfamily, hAmin⟩ := noetherian_closedSets_minimumCondition G family hfamily
  obtain ⟨V, hV, rfl⟩ := hAfamily
  have hVC : V ≤ Q.centralizer := by
    by_contra hnot
    obtain ⟨x, hxV, hxC⟩ := Set.not_subset.mp hnot
    change x ∉ Subgroup.centralizer (Q.toSubgroup : Set (Variety.Point G)) at hxC
    rw [Subgroup.mem_centralizer_iff] at hxC
    push Not at hxC
    obtain ⟨s, hsQ, hsx⟩ := hxC
    let q : Variety.Point Q.carrierVariety := Q.pointEquiv.symm ⟨s, hsQ⟩
    have hq : Q.includePoint q = s := by
      change (Q.pointEquiv q).val = s
      simp [q]
    have hssemi : IsSemisimpleElement G s := by
      rw [← hq]
      exact morphism_preserves_semisimpleElement Q.inclusion q (hQ.all_semisimple q)
    let C := semisimpleCommutatorPointCentralizer s
    let W := V.inter C
    have hQW : Q ≤ W.normalizer := by
      intro t htQ
      have htC : t ∈ C := by
        change t ∈ Subgroup.centralizer ({s} : Set (Variety.Point G))
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        subst z
        let tQ : Variety.Point Q.carrierVariety := Q.pointEquiv.symm ⟨t, htQ⟩
        have htval : Q.includePoint tQ = t := by
          change (Q.pointEquiv tQ).val = t
          simp [tQ]
        have hcomm := isMulCommutative_iff.mp hQ.isMulCommutative q tQ
        have hamb := congrArg Q.inclusion.onPoints hcomm
        change Q.includePoint q * Q.includePoint tQ = Q.includePoint tQ * Q.includePoint q at hamb
        simpa only [hq, htval] using hamb
      have htN : t ∈ Subgroup.normalizer (C.toSubgroup : Set (Variety.Point G)) :=
        C.toSubgroup.le_normalizer htC
      change t ∈ Subgroup.normalizer (W.toSubgroup : Set (Variety.Point G))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      change (y ∈ V ∧ y ∈ C) ↔ (t * y * t⁻¹ ∈ V ∧ t * y * t⁻¹ ∈ C)
      exact and_congr (Subgroup.mem_normalizer_iff.mp (hV.2.1 htQ) y)
        (Subgroup.mem_normalizer_iff.mp htN y)
    have hDW : D ∈ closedSubgroupTangent W := by
      apply externalSemisimplePoint_fixed_tangent V s (hV.2.1 hsQ) hssemi D hV.2.2
      rw [← hq]
      exact hfixed q
    have hWfamily : closedSet W ∈ family :=
      ⟨W, ⟨fun _ hx => hV.1 hx.1, hQW, hDW⟩, rfl⟩
    have hproper : closedSet W < closedSet V := by
      constructor
      · exact fun _ hx => hx.1
      · intro hreverse
        have hxW : x ∈ W := hreverse hxV
        have hxCs : x ∈ Subgroup.centralizer ({s} : Set (Variety.Point G)) := hxW.2
        exact hsx ((Subgroup.mem_centralizer_iff.mp hxCs) s (by simp))
    exact hAmin (closedSet W) hWfamily hproper
  have hVF : V ≤ H.pointwiseCentralizer Q := fun _ hx => ⟨hV.1 hx, hVC hx⟩
  exact closedSubgroupTangent_mono hVF hV.2.2

/-- The fixed-tangent lifting contract for every subtorus of a group
normalizing `H`. In particular this applies to a normalizing torus `T`. -/
public theorem hasExternalFixedTangentLifting_of_normalizes
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hTN : T ≤ H.normalizer) : HasExternalFixedTangentLifting H T := by
  intro Q hQ hQT D hDH hfixed
  exact externalSubtorus_fixed_tangent H Q hQ (fun _ hx => hTN (hQT hx)) D hDH hfixed

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
