module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Bor1.PointCentralizerTangent
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.TangentIntersectionFoundation
public import Theory.AlgebraicGroup.Dimension.Chain
public import Theory.AlgebraicGroup.RootSubgroups.TangentAdjointFixedCenter
public import Theory.AlgebraicGroup.RootSubgroups.TangentLie

/-!
# Characteristic-zero centralizer differential exactness

For an algebraically closed characteristic-zero field, this module identifies
the embedded identity-component tangent of the centralizer of a closed subgroup
with the kernel of the simultaneous differentials of conjugation by its points.
The proof follows Bor1 Chapter 3, Sections 9.1--9.2: the point-centralizer
formula and exact tangent intersections reduce the reverse inclusion to a
Noetherian minimal closed-subgroup argument.  The final specialization to the
Lie center assumes connectedness, exactly as required by the connected
adjoint-fixed tangent theorem.  No root-system classification result is used.

-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The simultaneous differential of the conjugation orbit equations for all
points of a closed subgroup. -/
public noncomputable def centralizerOrbitDifferential
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) :
    IdentityPointDerivation G →ₗ[k]
      (Variety.Point S.carrierVariety → IdentityPointDerivation G) where
  toFun D s :=
    identityTangentConjugationLinearMap G (S.includePoint s) D - D
  map_add' D E := by
    funext s
    apply Derivation.ext
    intro a
    change
      (D + E) ((AlgebraicGroup.conjugationByMorphism G
          (S.includePoint s)).pullbackAlgHom a) - (D + E) a =
        (D ((AlgebraicGroup.conjugationByMorphism G
            (S.includePoint s)).pullbackAlgHom a) - D a) +
          (E ((AlgebraicGroup.conjugationByMorphism G
            (S.includePoint s)).pullbackAlgHom a) - E a)
    simp only [Derivation.add_apply]
    abel
  map_smul' c D := by
    funext s
    apply Derivation.ext
    intro a
    change
      (c • D) ((AlgebraicGroup.conjugationByMorphism G
          (S.includePoint s)).pullbackAlgHom a) - (c • D) a =
        c • (D ((AlgebraicGroup.conjugationByMorphism G
          (S.includePoint s)).pullbackAlgHom a) - D a)
    simp only [Derivation.smul_apply, smul_eq_mul, mul_sub]

private lemma centralizerOrbitDifferential_mem_ker_iff
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (D : IdentityPointDerivation G) :
    D ∈ LinearMap.ker (centralizerOrbitDifferential S) ↔
      ∀ s : Variety.Point S.carrierVariety,
        identityTangentConjugationLinearMap G (S.includePoint s) D = D := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h s
    have hs := congrFun h s
    exact sub_eq_zero.mp hs
  · intro h
    funext s
    exact sub_eq_zero.mpr (h s)

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

private lemma tangent_range_mono
    {G : Variety k} [AlgebraicGroup G] {B C : ClosedSubgroup G}
    (hBC : B ≤ C) :
    LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ≤
      LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  let f : AlgebraicGroup.Morphism B.carrierVariety C.carrierVariety :=
    B.inclusion.codRestrictClosedSubgroup C
      (fun x ↦ hBC (B.pointEquiv x).property)
  have hcomp : C.inclusion.comp f = B.inclusion := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact (B.inclusion.codRestrictClosedSubgroup_inclusion_apply C
      (fun x ↦ hBC (B.pointEquiv x).property) x).symm
  rintro D ⟨E, rfl⟩
  refine ⟨identityTangentMorphismLinearMap f E, ?_⟩
  rw [← LinearMap.comp_apply, ← identityTangentMorphismLinearMap_comp,
    hcomp]

private lemma identityTangent_range_identityComponentAmbient_eq
    {G : Variety k} [AlgebraicGroup G] (C : ClosedSubgroup G) :
    LinearMap.range
        (identityTangentMorphismLinearMap C.identityComponentAmbient.inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  apply le_antisymm
  · exact tangent_range_mono C.identityComponentAmbient_le
  · rintro D ⟨E, rfl⟩
    let C0 := AlgebraicGroup.identityComponentClosedSubgroup C.carrierVariety
    letI : AlgebraicGroup C0.carrierVariety := C0.carrierAlgebraicGroup
    obtain ⟨E0, hE0⟩ :=
      identityComponent_inclusion_tangent_surjective C.carrierVariety E
    let f0 : AlgebraicGroup.Morphism C0.carrierVariety G :=
      C.inclusion.comp C0.inclusion
    let K : ClosedSubgroup G := C.identityComponentAmbient
    let q0 : AlgebraicGroup.Morphism C0.carrierVariety K.carrierVariety :=
      f0.codRestrictClosedSubgroup K (fun z ↦ ⟨z, rfl⟩)
    have hq0comp : K.inclusion.comp q0 = f0 := by
      apply AlgebraicGroup.Morphism.ext
      funext z
      exact f0.codRestrictClosedSubgroup_inclusion_apply K
        (fun z ↦ ⟨z, rfl⟩) z
    refine ⟨identityTangentMorphismLinearMap q0 E0, ?_⟩
    calc
      identityTangentMorphismLinearMap K.inclusion
          (identityTangentMorphismLinearMap q0 E0) =
          identityTangentMorphismLinearMap (K.inclusion.comp q0) E0 := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap f0 E0 := by rw [hq0comp]
      _ = identityTangentMorphismLinearMap C.inclusion
          (identityTangentMorphismLinearMap C0.inclusion E0) := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap C.inclusion E := by rw [hE0]

private theorem identityTangent_fixed_mem_centralizer_range
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G) (D : IdentityPointDerivation G)
    (hD : ∀ s : Variety.Point S.carrierVariety,
      identityTangentConjugationLinearMap G (S.includePoint s) D = D) :
    D ∈ LinearMap.range
      (identityTangentMorphismLinearMap S.centralizer.inclusion) := by
  classical
  let C := S.centralizer
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
            (AlgebraicGroup.Morphism.id G) D := by congr 1
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
    let P : ClosedSubgroup G :=
      subgroupZariskiClosure G (Subgroup.zpowers s0)
    let Z : ClosedSubgroup G := P.centralizer
    have hDZ : D ∈ LinearMap.range
        (identityTangentMorphismLinearMap Z.inclusion) := by
      rw [identityTangent_pointCentralizer_range_eq_fixed G s0]
      rw [LinearMap.mem_ker]
      change identityTangentConjugationLinearMap G s0 D - D = 0
      rw [← hsval, hD s, sub_self]
    let H' : ClosedSubgroup G := H.inter Z
    have hDH' : D ∈ LinearMap.range
        (identityTangentMorphismLinearMap H'.inclusion) := by
      rw [identityTangent_range_eq_inf_charZero H Z]
      exact ⟨hDH, hDZ⟩
    have hH'H : H' ≤ H := by
      intro y hy
      exact (ClosedSubgroup.mem_inter_iff H Z y).mp hy |>.1
    have hCH' : C ≤ H' := by
      intro c hc
      apply (ClosedSubgroup.mem_inter_iff H Z c).mpr
      refine ⟨hCH hc, ?_⟩
      have hcs0 : s0 * c = c * s0 := by
        exact (Subgroup.mem_centralizer_iff.mp hc) s0 hs0S
      exact mem_cyclicClosure_centralizer_of_commute s0 c hcs0
    have hxnotZ : x ∉ Z := by
      intro hxZ
      change x ∈ Subgroup.centralizer
        (P.toSubgroup : Set (Variety.Point G)) at hxZ
      have hs0P : s0 ∈ P := subset_closure (Subgroup.mem_zpowers s0)
      exact hs0x ((Subgroup.mem_centralizer_iff.mp hxZ) s0 hs0P)
    have hxnotH' : x ∉ H' := by
      intro hxH'
      exact hxnotZ ((ClosedSubgroup.mem_inter_iff H Z x).mp hxH' |>.2)
    have hproperSet : closedSet H' < closedSet H := by
      constructor
      · exact hH'H
      · intro hreverse
        exact hxnotH' (hreverse (H.identityComponentAmbient_le hxH0))
    exact hAmin (closedSet H') ⟨H', ⟨hCH', hDH'⟩, rfl⟩ hproperSet
  have hDH0 : D ∈ LinearMap.range (identityTangentMorphismLinearMap
      H.identityComponentAmbient.inclusion) := by
    rw [identityTangent_range_identityComponentAmbient_eq H]
    exact hDH
  exact tangent_range_mono hH0C hDH0

private theorem centralizer_range_le_fixed
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) :
    LinearMap.range
        (identityTangentMorphismLinearMap S.centralizer.inclusion) ≤
      LinearMap.ker (centralizerOrbitDifferential S) := by
  intro D hD
  apply (centralizerOrbitDifferential_mem_ker_iff S D).mpr
  intro s
  let P : ClosedSubgroup G :=
    subgroupZariskiClosure G (Subgroup.zpowers (S.includePoint s))
  let Z : ClosedSubgroup G := P.centralizer
  have hCZ : S.centralizer ≤ Z := by
    intro c hc
    have hcomm : S.includePoint s * c = c * S.includePoint s :=
      (Subgroup.mem_centralizer_iff.mp hc)
        (S.includePoint s) (S.pointEquiv s).property
    exact mem_cyclicClosure_centralizer_of_commute (S.includePoint s) c hcomm
  have hDZ := tangent_range_mono hCZ hD
  rw [identityTangent_pointCentralizer_range_eq_fixed G (S.includePoint s)] at hDZ
  rw [LinearMap.mem_ker] at hDZ
  exact sub_eq_zero.mp hDZ

/-- In characteristic zero, the identity-component centralizer tangent is the
kernel of the simultaneous infinitesimal conjugation equations. -/
public theorem identityComponentCentralizerTangent_range_eq_orbitDifferential_ker
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) :
    LinearMap.range (identityTangentMorphismLinearMap
        S.centralizer.identityComponentAmbient.inclusion) =
      LinearMap.ker (centralizerOrbitDifferential S) := by
  rw [identityTangent_range_identityComponentAmbient_eq]
  apply le_antisymm
  · exact centralizer_range_le_fixed S
  · intro D hD
    apply identityTangent_fixed_mem_centralizer_range S D
    exact (centralizerOrbitDifferential_mem_ker_iff S D).mp hD

/-- For a connected group, specializing the subgroup to the whole group
identifies the centralizer tangent with the Lie-algebra center. -/
public theorem identityComponentCenterTangent_range_eq_lieCenter
    {G : Variety k} [AlgebraicGroup G]
    (hG : _root_.IsConnected (Set.univ : Set (Variety.Point G))) :
    LinearMap.range (identityTangentMorphismLinearMap
        (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion) =
      (LieAlgebra.center k
        (Theory.AlgebraicGroup.IdentityPointDerivation G)).toSubmodule := by
  rw [identityComponentCentralizerTangent_range_eq_orbitDifferential_ker]
  ext D
  rw [centralizerOrbitDifferential_mem_ker_iff]
  constructor
  · intro hD
    apply (identityTangent_pointwise_fixed_iff_mem_lieCenter G hG D).mp
    intro g
    let s : Variety.Point (ClosedSubgroup.top (G := G)).carrierVariety :=
      (ClosedSubgroup.top (G := G)).pointEquiv.symm ⟨g, trivial⟩
    have hs : (ClosedSubgroup.top (G := G)).includePoint s = g := by
      change ((ClosedSubgroup.top (G := G)).pointEquiv s).val = g
      simp [s]
    simpa only [hs] using hD s
  · intro hD s
    exact (identityTangent_pointwise_fixed_iff_mem_lieCenter G hG D).mpr hD
      ((ClosedSubgroup.top (G := G)).includePoint s)

end Theory.AlgebraicGroup.Bor1
