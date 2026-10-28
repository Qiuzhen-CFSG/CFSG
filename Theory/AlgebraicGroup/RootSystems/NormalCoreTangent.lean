module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.TangentIntersectionFoundation
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
# Tangent-preserving normal cores

This module constructs a connected normal closed subgroup without losing a
prescribed conjugation-invariant subspace of the identity tangent.  The ambient
field is algebraically closed, and the intersection step additionally assumes
characteristic zero.

The first results identify the embedded tangent of a conjugate, show that a
closed subgroup and its ambient identity component have the same embedded
tangent, and expose the exact tangent formula for a binary closed-subgroup
intersection through the root-system tangent API.  The last theorem starts
with a connected algebraic group `G`, a closed subgroup `H`, and an invariant
subspace `W` contained in the tangent of `H`, and produces a connected normal
closed subgroup `N ≤ H` whose tangent still contains `W`.

The proof is the standard finite normal-core argument.  Exact intersection
tangents put `W` in every finite intersection of conjugates of `H`.  Choose
such an intersection of minimal dimension.  Intersecting it with one further
conjugate has the same ambient identity component, so that component lies in
every conjugate of `H`.  Its own conjugates remain connected and lie in the
chosen finite intersection, which proves normality after passing back to the
identity component.  The tangent formula for intersections comes from the
characteristic-zero smooth intersection foundation; the remaining ingredients
are conjugation functoriality, connected-component tangent surjectivity, and
the closed-subgroup dimension API.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma identityTangentMorphismLinearMap_comp_local
    {G L M : Variety k} [AlgebraicGroup G] [AlgebraicGroup L]
    [AlgebraicGroup M]
    (f : AlgebraicGroup.Morphism G L)
    (g : AlgebraicGroup.Morphism L M) :
    identityTangentMorphismLinearMap (g.comp f) =
      (identityTangentMorphismLinearMap g).comp
        (identityTangentMorphismLinearMap f) := by
  ext D a
  rfl

omit [IsAlgClosed k] in
private lemma identityTangentMorphismLinearMap_id_local
    (G : Variety k) [AlgebraicGroup G] :
    identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.id G) =
      LinearMap.id := by
  ext D a
  rfl

omit [IsAlgClosed k] in
private lemma identityTangentRepresentation_action_eq
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    ((identityTangentRepresentation G).action g).1 =
      identityTangentConjugationLinearMap G g := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro a
  rw [identityTangentRepresentation_action_apply,
    identityTangentConjugationLinearMap_apply]

omit [IsAlgClosed k] in
private lemma identityTangentConjugationLinearMap_one_local
    (G : Variety k) [AlgebraicGroup G] :
    identityTangentConjugationLinearMap G 1 = LinearMap.id := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism G 1).pullbackAlgHom f) = D f
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism G 1).toFun x) = f x
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  simp

omit [IsAlgClosed k] in
private lemma identityTangentConjugationLinearMap_mul_local
    (G : Variety k) [AlgebraicGroup G] (g h : Variety.Point G) :
    identityTangentConjugationLinearMap G (g * h) =
      (identityTangentConjugationLinearMap G g).comp
        (identityTangentConjugationLinearMap G h) := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism G (g * h)).pullbackAlgHom f) =
    D ((AlgebraicGroup.conjugationByMorphism G h).pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom f))
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism G (g * h)).toFun x) =
    f ((AlgebraicGroup.conjugationByMorphism G g).toFun
      ((AlgebraicGroup.conjugationByMorphism G h).toFun x))
  simp only [AlgebraicGroup.conjugationByMorphism_apply]
  congr 1
  group

omit [IsAlgClosed k] in
private def ambientConjugationMorphism
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    AlgebraicGroup.Morphism G G where
  toVariety := AlgebraicGroup.conjugationByMorphism G g
  map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
  map_mul := by
    intro x y
    simp only [AlgebraicGroup.conjugationByMorphism_apply]
    group

omit [IsAlgClosed k] in
private lemma identityTangentMorphismLinearMap_ambientConjugation
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    identityTangentMorphismLinearMap (ambientConjugationMorphism G g) =
      identityTangentConjugationLinearMap G g := by
  rfl

omit [IsAlgClosed k] in
private lemma identityTangentMorphismLinearMap_iso_hom_surjective
    {G L : Variety k} [AlgebraicGroup G] [AlgebraicGroup L]
    (e : AlgebraicGroup.Iso G L) :
    Function.Surjective (identityTangentMorphismLinearMap e.hom) := by
  intro D
  refine ⟨identityTangentMorphismLinearMap e.inv D, ?_⟩
  change ((identityTangentMorphismLinearMap e.hom).comp
    (identityTangentMorphismLinearMap e.inv)) D = D
  rw [← identityTangentMorphismLinearMap_comp_local]
  have hinv : e.hom.comp e.inv = AlgebraicGroup.Morphism.id L := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact e.inv_hom_id x
  rw [hinv, identityTangentMorphismLinearMap_id_local]
  rfl

omit [IsAlgClosed k] in
/-- Conjugating a closed subgroup conjugates its embedded identity tangent
range by the ambient identity-tangent representation. -/
public theorem identityTangent_range_conjugate_eq_map
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (g : Variety.Point G) :
    LinearMap.range
        (identityTangentMorphismLinearMap (H.conjugate g).inclusion) =
      Submodule.map (identityTangentConjugationLinearMap G g)
        (LinearMap.range
          (identityTangentMorphismLinearMap H.inclusion)) := by
  let e := H.conjugateIso g
  have hmorphism :
      (H.conjugate g).inclusion.comp e.hom =
        (ambientConjugationMorphism G g).comp H.inclusion := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact H.conjugateIso_hom_inclusion_apply g x
  have hdifferential :
      (identityTangentMorphismLinearMap (H.conjugate g).inclusion).comp
          (identityTangentMorphismLinearMap e.hom) =
        (identityTangentConjugationLinearMap G g).comp
          (identityTangentMorphismLinearMap H.inclusion) := by
    rw [← identityTangentMorphismLinearMap_comp_local, hmorphism,
      identityTangentMorphismLinearMap_comp_local,
      identityTangentMorphismLinearMap_ambientConjugation]
  apply le_antisymm
  · rintro _ ⟨D, rfl⟩
    obtain ⟨E, rfl⟩ :=
      identityTangentMorphismLinearMap_iso_hom_surjective e D
    refine ⟨identityTangentMorphismLinearMap H.inclusion E, ⟨E, rfl⟩, ?_⟩
    exact (LinearMap.congr_fun hdifferential E).symm
  · rintro _ ⟨_, ⟨D, rfl⟩, rfl⟩
    refine ⟨identityTangentMorphismLinearMap e.hom D, ?_⟩
    exact LinearMap.congr_fun hdifferential D

/-- A closed subgroup and its ambient identity component have the same
embedded identity tangent range. -/
public theorem identityComponentAmbient_tangent_range_eq
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    LinearMap.range (identityTangentMorphismLinearMap
      H.identityComponentAmbient.inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  let I := H.identityComponentAmbient
  let j : AlgebraicGroup.Morphism I.carrierVariety H.carrierVariety :=
    I.inclusion.codRestrictClosedSubgroup H (by
      intro x
      exact H.identityComponentAmbient_le ((I.pointEquiv x).property))
  have hj : H.inclusion.comp j = I.inclusion := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    change H.inclusion.onPoints (j.onPoints x) = I.inclusion.onPoints x
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      I.inclusion H _ x
  have hle : LinearMap.range (identityTangentMorphismLinearMap I.inclusion) ≤
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
    rintro _ ⟨D, rfl⟩
    refine ⟨identityTangentMorphismLinearMap j D, ?_⟩
    rw [← LinearMap.comp_apply,
      ← identityTangentMorphismLinearMap_comp_local, hj]
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj
      (identityTangentMorphismLinearMap_inclusion_injective I),
    LinearMap.finrank_range_of_inj
      (identityTangentMorphismLinearMap_inclusion_injective H),
    Bor1.identityPointDerivation_finrank_eq_dimension,
    Bor1.identityPointDerivation_finrank_eq_dimension,
    ClosedSubgroup.dimension_identityComponentAmbient]

/-- In characteristic zero, the root-system identity tangent of an
intersection is the intersection of the two embedded tangent ranges. -/
public theorem identityTangent_range_inter_eq_inf_charZero
    [CharZero k] {G : Variety k} [AlgebraicGroup G]
    (B C : ClosedSubgroup G) :
    LinearMap.range (identityTangentMorphismLinearMap (B.inter C).inclusion) =
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) ⊓
        LinearMap.range (identityTangentMorphismLinearMap C.inclusion) := by
  exact Bor1.identityTangent_range_eq_inf_charZero B C

private def finiteConjugateIntersection
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    List (Variety.Point G) → ClosedSubgroup G
  | [] => H
  | g :: l => (finiteConjugateIntersection H l).inter (H.conjugate g)

omit [IsAlgClosed k] in
private lemma finiteConjugateIntersection_le
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (l : List (Variety.Point G)) :
    finiteConjugateIntersection H l ≤ H := by
  induction l with
  | nil => exact fun _ hx => hx
  | cons g l ih =>
      intro x hx
      exact ih ((ClosedSubgroup.mem_inter_iff
        (finiteConjugateIntersection H l) (H.conjugate g) x).mp hx).1

private lemma finiteConjugateIntersection_tangent
    [CharZero k] {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G)
    (W : Submodule k (IdentityPointDerivation G))
    (hWinvariant : IsInvariantSubmodule (identityTangentRepresentation G) W)
    (hWH : W ≤
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion))
    (l : List (Variety.Point G)) :
    W ≤ LinearMap.range (identityTangentMorphismLinearMap
      (finiteConjugateIntersection H l).inclusion) := by
  have hWconjugate : ∀ g : Variety.Point G,
      W ≤ LinearMap.range (identityTangentMorphismLinearMap
        (H.conjugate g).inclusion) := by
    intro g
    rw [identityTangent_range_conjugate_eq_map]
    intro D hD
    let E := identityTangentConjugationLinearMap G g⁻¹ D
    have hEW := hWinvariant g⁻¹ D hD
    rw [identityTangentRepresentation_action_eq] at hEW
    change E ∈ W at hEW
    refine ⟨E, hWH hEW, ?_⟩
    change ((identityTangentConjugationLinearMap G g).comp
      (identityTangentConjugationLinearMap G g⁻¹)) D = D
    rw [← identityTangentConjugationLinearMap_mul_local, mul_inv_cancel,
      identityTangentConjugationLinearMap_one_local]
    rfl
  induction l with
  | nil => exact hWH
  | cons g l ih =>
      rw [finiteConjugateIntersection,
        identityTangent_range_inter_eq_inf_charZero]
      exact le_inf ih (hWconjugate g)

omit [IsAlgClosed k] in
private lemma conjugate_le_finiteConjugateIntersection
    {G : Variety k} [AlgebraicGroup G]
    (H N : ClosedSubgroup G)
    (hN : ∀ g : Variety.Point G, N ≤ H.conjugate g)
    (a : Variety.Point G) (l : List (Variety.Point G)) :
    N.conjugate a ≤ finiteConjugateIntersection H l := by
  induction l with
  | nil =>
      intro y hy
      have hyN := (ClosedSubgroup.mem_conjugate_iff N a y).mp hy
      have hyConjugate := hN a⁻¹ hyN
      have hyH :=
        (ClosedSubgroup.mem_conjugate_iff H a⁻¹ (a⁻¹ * y * a)).mp
          hyConjugate
      change y ∈ H.toSubgroup
      simpa [mul_assoc] using hyH
  | cons g l ih =>
      intro y hy
      apply (ClosedSubgroup.mem_inter_iff
        (finiteConjugateIntersection H l) (H.conjugate g) y).mpr
      refine ⟨ih hy, ?_⟩
      apply (ClosedSubgroup.mem_conjugate_iff H g y).mpr
      have hyN := (ClosedSubgroup.mem_conjugate_iff N a y).mp hy
      have hyConjugate := hN (a⁻¹ * g) hyN
      have hyH := (ClosedSubgroup.mem_conjugate_iff H (a⁻¹ * g)
        (a⁻¹ * y * a)).mp hyConjugate
      simpa [mul_assoc] using hyH

omit [IsAlgClosed k] in
private lemma closedSubgroup_conjugate_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (g : Variety.Point G) :
    _root_.IsConnected (H.conjugate g : Set (Variety.Point G)) := by
  have hcarrier : (H.conjugate g : Set (Variety.Point G)) =
      (AlgebraicGroup.conjugationByMorphism G g).toFun ''
        (H : Set (Variety.Point G)) := by
    ext y
    constructor
    · intro hy
      have hy' := (ClosedSubgroup.mem_conjugate_iff H g y).mp hy
      refine ⟨g⁻¹ * y * g, hy', ?_⟩
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      simp [mul_assoc]
    · rintro ⟨z, hz, rfl⟩
      change z ∈ H.toSubgroup at hz
      apply (ClosedSubgroup.mem_conjugate_iff H g _).mpr
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      simpa [mul_assoc] using hz
  rw [hcarrier]
  exact hH.image _
    (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn

/-- A conjugation-invariant identity-tangent subspace contained in the tangent
of a closed subgroup is contained in the tangent of a connected normal closed
subgroup inside it. -/
public theorem exists_connected_normal_closedSubgroup_le_with_tangent_range
    [CharZero k] {G : Variety k} [AlgebraicGroup G]
    (_hG : Variety.IsConnected G)
    (H : ClosedSubgroup G)
    (W : Submodule k (IdentityPointDerivation G))
    (hWinvariant : IsInvariantSubmodule (identityTangentRepresentation G) W)
    (hWH : W ≤
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion)) :
    ∃ N : ClosedSubgroup G,
      N ≤ H ∧
      _root_.IsConnected (N : Set (Variety.Point G)) ∧
      N.toSubgroup.Normal ∧
      W ≤ LinearMap.range
        (identityTangentMorphismLinearMap N.inclusion) := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ l : List (Variety.Point G),
      Cardinal.toNat (Variety.dimension
        (finiteConjugateIntersection H l).carrierVariety) = n
  have hP : ∃ n, P n := by
    refine ⟨Cardinal.toNat (Variety.dimension H.carrierVariety), [], ?_⟩
    rfl
  let n := Nat.find hP
  obtain ⟨l, hl⟩ := Nat.find_spec hP
  let K := finiteConjugateIntersection H l
  let N := K.identityComponentAmbient
  have hN_all_conjugates : ∀ g : Variety.Point G, N ≤ H.conjugate g := by
    intro g
    let J := K.inter (H.conjugate g)
    have hKnat : Cardinal.toNat (Variety.dimension K.carrierVariety) = n := by
      simpa [K] using hl
    have hminNat :
        Cardinal.toNat (Variety.dimension K.carrierVariety) ≤
          Cardinal.toNat (Variety.dimension J.carrierVariety) := by
      rw [hKnat]
      simpa [n, P, J, K, finiteConjugateIntersection] using
        (Nat.find_min' hP
          (show P (Cardinal.toNat (Variety.dimension J.carrierVariety)) by
            refine ⟨g :: l, ?_⟩
            simp [J, K, finiteConjugateIntersection]))
    have hdim : Variety.dimension K.carrierVariety ≤
        Variety.dimension J.carrierVariety :=
      (Cardinal.toNat_le_iff_le_of_lt_aleph0
        (variety_dimension_lt_aleph0 K.carrierVariety)
        (variety_dimension_lt_aleph0 J.carrierVariety)).mp hminNat
    have hJleK : J ≤ K := by
      intro x hx
      exact ((ClosedSubgroup.mem_inter_iff K (H.conjugate g) x).mp hx).1
    have hJ0leK : J.identityComponentAmbient ≤ K :=
      fun x hx => hJleK (J.identityComponentAmbient_le hx)
    have hcomponents : K.identityComponentAmbient =
        J.identityComponentAmbient :=
      J.identityComponentAmbient_eq_of_le_of_dimension_le K hJ0leK hdim
    intro x hx
    have hxJ0 : x ∈ J.identityComponentAmbient := by
      rw [← hcomponents]
      exact hx
    have hxJ : x ∈ J := J.identityComponentAmbient_le hxJ0
    exact ((ClosedSubgroup.mem_inter_iff K (H.conjugate g) x).mp hxJ).2
  have hNleK : N ≤ K := K.identityComponentAmbient_le
  have hNleH : N ≤ H :=
    fun x hx => finiteConjugateIntersection_le H l (hNleK hx)
  have hNconnected : _root_.IsConnected (N : Set (Variety.Point G)) :=
    K.identityComponentAmbient_isConnected
  have hNnormal : N.toSubgroup.Normal := by
    constructor
    intro x hx g
    have hNgK : N.conjugate g ≤ K :=
      conjugate_le_finiteConjugateIntersection H N hN_all_conjugates g l
    have hNgConnected : _root_.IsConnected
        (N.conjugate g : Set (Variety.Point G)) :=
      closedSubgroup_conjugate_isConnected N hNconnected g
    have hNgN : N.conjugate g ≤ N :=
      connected_closedSubgroup_le_identityComponentAmbient
        (N.conjugate g) K hNgConnected hNgK
    apply hNgN
    apply (ClosedSubgroup.mem_conjugate_iff N g _).mpr
    simpa [mul_assoc] using hx
  have hWK : W ≤ LinearMap.range
      (identityTangentMorphismLinearMap K.inclusion) :=
    finiteConjugateIntersection_tangent H W hWinvariant hWH l
  have hWN : W ≤ LinearMap.range
      (identityTangentMorphismLinearMap N.inclusion) := by
    rw [identityComponentAmbient_tangent_range_eq]
    exact hWK
  exact ⟨N, hNleH, hNconnected, hNnormal, hWN⟩

end Theory.AlgebraicGroup
