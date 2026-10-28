module

public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Bor1.SemisimplePointCentralizerTangent
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Chain
public import Theory.AlgebraicGroup.Tori.DiagonalizableClosedSubgroupSemisimple

/-!
This module identifies the identity tangent of the centralizer of a
diagonalizable closed subgroup.  An identity tangent of the ambient algebraic
group lies in the range of the centralizer inclusion differential exactly when
it is fixed by tangent conjugation by every point of the subgroup.

The reverse inclusion is the substantive part of the corollary to GLS Bor1,
Chapter 3, Proposition 9.2, and gives the tangent assertion used in Proposition
9.4(1).  Choose, by Noetherian minimality, a closed subgroup containing the
centralizer through whose inclusion the fixed tangent lifts.  If its identity
component is not contained in the centralizer, a noncommuting point is cut out
by one semisimple subgroup point.  The semisimple point-centralizer tangent
formula, Bor1 Proposition 9.1, then produces a strictly smaller candidate.
Thus the identity component lies in the centralizer, and identity-component
tangent surjectivity gives the desired lift.  The forward inclusion follows
from conjugation naturality and commutativity of diagonalizable groups.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

omit [IsAlgClosed k] in
private lemma diagonalizableClosedSubgroup_isMulCommutative
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) :
    IsMulCommutative (Variety.Point S.carrierVariety) := by
  obtain ⟨n, D, ⟨e⟩⟩ := hS
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  apply IsMulCommutative.of_comm
  intro x y
  apply Function.LeftInverse.injective e.hom_inv_id
  rw [map_mul, map_mul]
  apply D.inclusion_injective
  rw [map_mul, map_mul]
  have hdiag := dVariety_isMulCommutative (k := k) n
  rw [isMulCommutative_iff] at hdiag
  exact hdiag _ _

omit [IsAlgClosed k] in
private lemma diagonalizableClosedSubgroup_le_centralizer
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) : S ≤ S.centralizer := by
  have hcomm := diagonalizableClosedSubgroup_isMulCommutative hS
  rw [isMulCommutative_iff] at hcomm
  intro x hx
  change x ∈ Subgroup.centralizer
    (S.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let xS := S.pointEquiv.symm ⟨x, hx⟩
  let yS := S.pointEquiv.symm ⟨y, hy⟩
  have hxy := hcomm yS xS
  have hamb := congrArg S.inclusion.onPoints hxy
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  have hyval : S.inclusion.onPoints yS = y := by
    change (S.pointEquiv yS).val = y
    simp [yS]
  simpa [map_mul, hxval, hyval] using hamb

omit [IsAlgClosed k] in
private lemma mem_cyclicClosure_centralizer_of_commute
    {G : Variety k} [AlgebraicGroup G] (s x : Variety.Point G)
    (hcomm : s * x = x * s) :
    x ∈ (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer := by
  change x ∈ Subgroup.centralizer
    ((subgroupZariskiClosure G (Subgroup.zpowers s)).toSubgroup :
      Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let E : Set (Variety.Point G) := {z | z * x = x * z}
  have hEclosed : IsClosed E := by
    apply Variety.isClosed_iff_isZariskiClosed.mpr
    simpa [E, AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply] using
      Variety.Morphism.isZariskiClosed_equalizer
        (AlgebraicGroup.rightMulMorphism G x)
        (AlgebraicGroup.leftMulMorphism G x)
  have hpowers : (Subgroup.zpowers s : Set (Variety.Point G)) ⊆ E := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact (show Commute s x from hcomm).zpow_left n
  exact closure_minimal hpowers hEclosed hy

private lemma diagonalizableClosedSubgroup_all_semisimple_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S)
    (s : Variety.Point S.carrierVariety) :
    IsSemisimpleElement G (S.includePoint s) :=
  morphism_preserves_semisimpleElement S.inclusion s (hS.all_semisimple s)

private lemma identityTangentConjugationLinearMap_eq_id_of_centralPoint
    {Q : Variety k} [AlgebraicGroup Q]
    (q : Variety.Point Q)
    (hq : ∀ x : Variety.Point Q, Commute q x) :
    identityTangentConjugationLinearMap Q q = LinearMap.id := by
  apply LinearMap.ext
  intro E
  apply Derivation.ext
  intro p
  rw [LinearMap.id_apply, identityTangentConjugationLinearMap_apply]
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro x
  change p (q * x * q⁻¹) = p x
  congr 1
  calc
    q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [(hq x).eq]
    _ = x := by simp

/-- Every identity tangent fixed by conjugation by all points of a
diagonalizable closed subgroup lifts through its centralizer inclusion. -/
public theorem identityTangent_fixed_mem_centralizer_range
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G) (hS : IsDiagonalizableClosedSubgroup S)
    (D : IdentityPointDerivation G)
    (hD : ∀ s : Variety.Point S.carrierVariety,
      identityTangentConjugationLinearMap G (S.includePoint s) D = D) :
    D ∈ LinearMap.range
      (identityTangentMorphismLinearMap S.centralizer.inclusion) := by
  classical
  let C := S.centralizer
  have hSC : S ≤ C := diagonalizableClosedSubgroup_le_centralizer hS
  let qualifies : ClosedSubgroup G → Prop := fun H ↦
    C ≤ H ∧
      D ∈ LinearMap.range
        (identityTangentMorphismLinearMap H.inclusion)
  let closedSet : ClosedSubgroup G →
      TopologicalSpace.Closeds (Variety.Point G) := fun H ↦
    ⟨(H : Set (Variety.Point G)),
      Variety.isClosed_iff_isZariskiClosed.mpr H.isZariskiClosed⟩
  let family : Set (TopologicalSpace.Closeds (Variety.Point G)) :=
    {A | ∃ H : ClosedSubgroup G, qualifies H ∧ A = closedSet H}
  have hfamily : family.Nonempty := by
    let T : ClosedSubgroup G := ClosedSubgroup.top
    have hCT : C ≤ T := by intro x hx; trivial
    have hDT : D ∈ LinearMap.range
        (identityTangentMorphismLinearMap T.inclusion) := by
      let r : AlgebraicGroup.Morphism G T.carrierVariety :=
        (AlgebraicGroup.Morphism.id G).codRestrictClosedSubgroup T
          (fun _ ↦ trivial)
      refine ⟨identityTangentMorphismLinearMap r D, ?_⟩
      calc
        identityTangentMorphismLinearMap T.inclusion
            (identityTangentMorphismLinearMap r D) =
            identityTangentMorphismLinearMap (T.inclusion.comp r) D := by
          rw [identityTangentMorphismLinearMap_comp]
          rfl
        _ = identityTangentMorphismLinearMap
            (AlgebraicGroup.Morphism.id G) D := by
          congr 1
        _ = D := by rw [identityTangentMorphismLinearMap_id]; rfl
    exact ⟨closedSet T, T, ⟨hCT, hDT⟩, rfl⟩
  obtain ⟨A, hAfamily, hAmin⟩ :=
    noetherian_closedSets_minimumCondition G family hfamily
  rcases hAfamily with ⟨H, hHqualifies, hAH⟩
  subst A
  rcases hHqualifies with ⟨hCH, hDH⟩
  have hH0C : H.identityComponentAmbient ≤ C := by
    by_contra hnot
    obtain ⟨x, hxH0, hxC⟩ := Set.not_subset.mp hnot
    have hxnot : x ∉ Subgroup.centralizer
        (S.toSubgroup : Set (Variety.Point G)) := hxC
    rw [Subgroup.mem_centralizer_iff] at hxnot
    push Not at hxnot
    obtain ⟨s0, hs0S, hs0x⟩ := hxnot
    let s : Variety.Point S.carrierVariety :=
      S.pointEquiv.symm ⟨s0, hs0S⟩
    have hsval : S.includePoint s = s0 := by
      change (S.pointEquiv s).val = s0
      simp [s]
    have hsC : s0 ∈ C := hSC hs0S
    have hsH : s0 ∈ H := hCH hsC
    let sH : Variety.Point H.carrierVariety :=
      H.pointEquiv.symm ⟨s0, hsH⟩
    have hsHval : H.includePoint sH = s0 := by
      change (H.pointEquiv sH).val = s0
      simp [sH]
    have hssemiG : IsSemisimpleElement G s0 := by
      rw [← hsval]
      exact diagonalizableClosedSubgroup_all_semisimple_ambient hS s
    have hssemiH : IsSemisimpleElement H.carrierVariety sH := by
      have h := (closedSubgroup_semisimpleElement_iff H hsH).mp hssemiG
      simpa [sH] using h
    obtain ⟨DH, hDHval⟩ := hDH
    have hDHfixed :
        identityTangentConjugationLinearMap H.carrierVariety sH DH = DH := by
      apply identityTangentMorphismLinearMap_inclusion_injective H
      have hnat := congrArg (fun L => L DH)
        (identityTangentMorphismLinearMap_conjugation_naturality
          H.inclusion sH)
      change identityTangentMorphismLinearMap H.inclusion
          (identityTangentConjugationLinearMap H.carrierVariety sH DH) =
        identityTangentConjugationLinearMap G (H.includePoint sH)
          (identityTangentMorphismLinearMap H.inclusion DH) at hnat
      rw [hnat, hsHval, ← hsval, hDHval, hD]
    let P : ClosedSubgroup H.carrierVariety :=
      subgroupZariskiClosure H.carrierVariety (Subgroup.zpowers sH)
    letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
    let Z : ClosedSubgroup H.carrierVariety := P.centralizer
    letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
    have hDHker : DH ∈ LinearMap.ker
        (identityTangentConjugationLinearMap H.carrierVariety sH -
          LinearMap.id) := by
      rw [LinearMap.mem_ker]
      change identityTangentConjugationLinearMap H.carrierVariety sH DH - DH = 0
      rw [hDHfixed, sub_self]
    have hDHrange : DH ∈ LinearMap.range
        (identityTangentMorphismLinearMap Z.inclusion) := by
      rw [identityTangent_semisimplePointCentralizer_range_eq_fixed
        H.carrierVariety sH hssemiH]
      exact hDHker
    obtain ⟨DZ, hDZ⟩ := hDHrange
    let f : AlgebraicGroup.Morphism Z.carrierVariety G :=
      H.inclusion.comp Z.inclusion
    let H' : ClosedSubgroup G := f.imageClosedSubgroup
    let q : AlgebraicGroup.Morphism Z.carrierVariety H'.carrierVariety :=
      f.codRestrictClosedSubgroup H' (fun z ↦ ⟨z, rfl⟩)
    have hqcomp : H'.inclusion.comp q = f := by
      apply AlgebraicGroup.Morphism.ext
      funext z
      exact f.codRestrictClosedSubgroup_inclusion_apply H'
        (fun z ↦ ⟨z, rfl⟩) z
    have hDH' : D ∈ LinearMap.range
        (identityTangentMorphismLinearMap H'.inclusion) := by
      refine ⟨identityTangentMorphismLinearMap q DZ, ?_⟩
      calc
        identityTangentMorphismLinearMap H'.inclusion
            (identityTangentMorphismLinearMap q DZ) =
            identityTangentMorphismLinearMap (H'.inclusion.comp q) DZ := by
          rw [identityTangentMorphismLinearMap_comp]
          rfl
        _ = identityTangentMorphismLinearMap f DZ := by rw [hqcomp]
        _ = identityTangentMorphismLinearMap H.inclusion
            (identityTangentMorphismLinearMap Z.inclusion DZ) := by
          rw [identityTangentMorphismLinearMap_comp]
          rfl
        _ = identityTangentMorphismLinearMap H.inclusion DH := by rw [hDZ]
        _ = D := hDHval
    have hH'H : H' ≤ H := by
      intro y hy
      change y ∈ f.image at hy
      rcases hy with ⟨z, rfl⟩
      exact (H.pointEquiv (Z.includePoint z)).property
    have hCH' : C ≤ H' := by
      intro c hc
      have hcH : c ∈ H := hCH hc
      let cH : Variety.Point H.carrierVariety :=
        H.pointEquiv.symm ⟨c, hcH⟩
      have hcHval : H.includePoint cH = c := by
        change (H.pointEquiv cH).val = c
        simp [cH]
      have hcs0 : s0 * c = c * s0 := by
        have hc' : c ∈ Subgroup.centralizer
            (S.toSubgroup : Set (Variety.Point G)) := hc
        exact (Subgroup.mem_centralizer_iff.mp hc') s0 hs0S
      have hcommH : sH * cH = cH * sH := by
        apply H.inclusion_injective
        have hsHval' : H.inclusion.onPoints sH = s0 := hsHval
        have hcHval' : H.inclusion.onPoints cH = c := hcHval
        rw [map_mul, map_mul, hsHval', hcHval']
        exact hcs0
      have hcHZ : cH ∈ Z :=
        mem_cyclicClosure_centralizer_of_commute sH cH hcommH
      let z : Variety.Point Z.carrierVariety := Z.pointEquiv.symm ⟨cH, hcHZ⟩
      change c ∈ f.image
      refine ⟨z, ?_⟩
      change H.includePoint (Z.includePoint z) = c
      have hzval : Z.includePoint z = cH := by
        change (Z.pointEquiv z).val = cH
        simp [z]
      rw [hzval, hcHval]
    have hxnotH' : x ∉ H' := by
      intro hxH'
      change x ∈ f.image at hxH'
      rcases hxH' with ⟨z, hz⟩
      have hzcentral : Z.includePoint z ∈ Z :=
        (Z.pointEquiv z).property
      change Z.includePoint z ∈ Subgroup.centralizer
          (P.toSubgroup : Set (Variety.Point H.carrierVariety)) at hzcentral
      have hsHP : sH ∈ P := by
        exact subset_closure (Subgroup.mem_zpowers sH)
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzcentral) sH hsHP
      have hamb := congrArg H.inclusion.onPoints hcomm
      have hzval : H.includePoint (Z.includePoint z) = x := hz
      apply hs0x
      have hsHval' : H.inclusion.onPoints sH = s0 := hsHval
      have hzval' : H.inclusion.onPoints (Z.includePoint z) = x := hzval
      rw [map_mul, map_mul, hsHval', hzval'] at hamb
      exact hamb
    have hproperSet : closedSet H' < closedSet H := by
      constructor
      · exact hH'H
      · intro hreverse
        exact hxnotH' (hreverse (H.identityComponentAmbient_le hxH0))
    have hH'family : closedSet H' ∈ family :=
      ⟨H', ⟨hCH', hDH'⟩, rfl⟩
    exact hAmin (closedSet H') hH'family hproperSet
  obtain ⟨DH, hDHval⟩ := hDH
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  letI : AlgebraicGroup H0.carrierVariety := H0.carrierAlgebraicGroup
  obtain ⟨D0, hD0⟩ :=
    identityComponent_inclusion_tangent_surjective H.carrierVariety DH
  let f0 : AlgebraicGroup.Morphism H0.carrierVariety G :=
    H.inclusion.comp H0.inclusion
  let K : ClosedSubgroup G := H.identityComponentAmbient
  let q0 : AlgebraicGroup.Morphism H0.carrierVariety K.carrierVariety :=
    f0.codRestrictClosedSubgroup K (fun z ↦ ⟨z, rfl⟩)
  have hq0comp : K.inclusion.comp q0 = f0 := by
    apply AlgebraicGroup.Morphism.ext
    funext z
    exact f0.codRestrictClosedSubgroup_inclusion_apply K
      (fun z ↦ ⟨z, rfl⟩) z
  let r : AlgebraicGroup.Morphism K.carrierVariety C.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup C
      (fun z ↦ hH0C (K.pointEquiv z).property)
  refine ⟨identityTangentMorphismLinearMap r
      (identityTangentMorphismLinearMap q0 D0), ?_⟩
  calc
    identityTangentMorphismLinearMap C.inclusion
        (identityTangentMorphismLinearMap r
          (identityTangentMorphismLinearMap q0 D0)) =
        identityTangentMorphismLinearMap (C.inclusion.comp r)
          (identityTangentMorphismLinearMap q0 D0) := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap K.inclusion
          (identityTangentMorphismLinearMap q0 D0) := by
      congr 1
    _ = identityTangentMorphismLinearMap (K.inclusion.comp q0) D0 := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap f0 D0 := by rw [hq0comp]
    _ = identityTangentMorphismLinearMap H.inclusion
          (identityTangentMorphismLinearMap H0.inclusion D0) := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap H.inclusion DH := by rw [hD0]
    _ = D := hDHval

/-- Every identity tangent coming from the centralizer is fixed by tangent
conjugation by every point of the diagonalizable subgroup. -/
public theorem identityTangent_centralizer_range_fixed
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G) (hS : IsDiagonalizableClosedSubgroup S)
    (D : IdentityPointDerivation G)
    (hD : D ∈ LinearMap.range
      (identityTangentMorphismLinearMap S.centralizer.inclusion)) :
    ∀ s : Variety.Point S.carrierVariety,
      identityTangentConjugationLinearMap G (S.includePoint s) D = D := by
  classical
  intro s
  rcases hD with ⟨DC, rfl⟩
  let C := S.centralizer
  have hSC : S ≤ C := diagonalizableClosedSubgroup_le_centralizer hS
  have hsC : S.includePoint s ∈ C :=
    hSC (S.pointEquiv s).property
  let sC : Variety.Point C.carrierVariety :=
    C.pointEquiv.symm ⟨S.includePoint s, hsC⟩
  have hsCval : C.includePoint sC = S.includePoint s := by
    change (C.pointEquiv sC).val = S.includePoint s
    simp [sC]
  have hsCcentral : ∀ x : Variety.Point C.carrierVariety,
      Commute sC x := by
    intro x
    apply C.inclusion_injective
    change S.includePoint s * C.includePoint x =
      C.includePoint x * S.includePoint s
    exact (Subgroup.mem_centralizer_iff.mp (C.pointEquiv x).property)
      (S.includePoint s) (S.pointEquiv s).property
  have hnat := LinearMap.congr_fun
    (identityTangentMorphismLinearMap_conjugation_naturality C.inclusion sC) DC
  change identityTangentMorphismLinearMap C.inclusion
      (identityTangentConjugationLinearMap C.carrierVariety sC DC) =
    identityTangentConjugationLinearMap G (C.includePoint sC)
      (identityTangentMorphismLinearMap C.inclusion DC) at hnat
  rw [← hsCval, ← hnat,
    identityTangentConjugationLinearMap_eq_id_of_centralPoint sC hsCcentral]
  rfl

/-- The identity tangent range of a diagonalizable subgroup's centralizer is
the intersection of the fixed kernels for its pointwise conjugation action. -/
public theorem identityTangent_centralizer_range_eq_iInf_fixed
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G) (hS : IsDiagonalizableClosedSubgroup S) :
    LinearMap.range
        (identityTangentMorphismLinearMap S.centralizer.inclusion) =
      ⨅ s : Variety.Point S.carrierVariety,
        LinearMap.ker
          (identityTangentConjugationLinearMap G (S.includePoint s) -
            LinearMap.id) := by
  apply le_antisymm
  · intro D hD
    rw [Submodule.mem_iInf]
    intro s
    rw [LinearMap.mem_ker]
    change identityTangentConjugationLinearMap G (S.includePoint s) D - D = 0
    rw [identityTangent_centralizer_range_fixed S hS D hD s, sub_self]
  · intro D hD
    apply identityTangent_fixed_mem_centralizer_range S hS D
    intro s
    have hs := (Submodule.mem_iInf _).mp hD s
    rw [LinearMap.mem_ker] at hs
    change identityTangentConjugationLinearMap G (S.includePoint s) D - D = 0 at hs
    exact sub_eq_zero.mp hs

end Theory.AlgebraicGroup.Bor1
