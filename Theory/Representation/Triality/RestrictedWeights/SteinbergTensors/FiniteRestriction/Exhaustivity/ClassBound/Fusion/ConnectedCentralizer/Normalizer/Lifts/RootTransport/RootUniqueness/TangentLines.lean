module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.RootUniqueness.CharacterPowers
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Independence
public import Theory.AlgebraicGroup.RootSubgroups.TangentMultiplicityOne

/-!
# Root-weight tangent lines from actual D4 tangent spanning

The differential of a root parametrization identifies its embedded subgroup
tangent with a nonzero line of inverse root weight. The embedded torus tangent
has trivial weight. Independence of distinct group characters then isolates
each line and excludes every higher inverse-root weight, provided the given
torus and root-subgroup tangents span. Tangent rigidity integrates these two
facts to scalar equality of root parametrizations, including in characteristic
two where equality of tangents alone would not suffice.

Spanning remains an explicit geometric premise. Its producer is the existing
`ConnectedLang.FrobeniusDifferential.TangentSpan` development. No statement
about faithful differentiation of characters or an alternate D4 carrier is used.

Source: GLS3, Theorem 1.9.5(b), `refs/KGroup/GLS3/Chapter1.tex`.
The weight-space argument follows the analogous concrete F4 `TangentLines`
module, but applies here to the supplied geometry and actual subgroup tangents.
-/

open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

private theorem parameter_tangent_injective (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    Function.Injective (Bor1.identityTangentMorphismLinearMap x.inv) := by
  intro D E h
  have h' := congrArg (Bor1.identityTangentMorphismLinearMap x.hom) h
  have hcomp : x.hom.comp x.inv = AlgebraicGroup.Morphism.id X.carrierVariety := by
    apply AlgebraicGroup.Morphism.ext
    funext y
    exact x.inv_hom_id y
  change (Bor1.identityTangentMorphismLinearMap x.hom ∘ₗ
    Bor1.identityTangentMorphismLinearMap x.inv) D =
    (Bor1.identityTangentMorphismLinearMap x.hom ∘ₗ
    Bor1.identityTangentMorphismLinearMap x.inv) E at h'
  rw [← Bor1.identityTangentMorphismLinearMap_comp, hcomp,
    Bor1.identityTangentMorphismLinearMap_id] at h'
  exact h'

private theorem tangentRange_eq_span (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap X.inclusion) =
      Submodule.span k {oneParameterTangent X x} := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = oneParameterTangent X x)
    exact oneParameterTangent_mem_range_inclusion X x
  · rw [finrank_span_singleton (oneParameterTangent_ne_zero X x)]
    calc
      _ ≤ Module.finrank k (Bor1.IdentityPointDerivation X.carrierVariety) :=
        LinearMap.finrank_range_le _
      _ ≤ Module.finrank k (Bor1.IdentityPointDerivation (KPlus k)) :=
        LinearMap.finrank_le_finrank_of_injective (parameter_tangent_injective X x)
      _ ≤ 1 := by
        have h := LinearMap.finrank_le_finrank_of_injective
          (Bor1.coordinateTangentMap_injective (KPlus k))
        simpa [KPlus, additiveGroupVariety] using h

private theorem weightSpace_eq_of_spanning_submodules
    {k : Type*} [Field k] {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    {ι : Type*} (w : ι → TorusWeight T) (hw : Function.Injective w)
    (L : ι → Submodule k V) (hL : ∀ i, L i ≤ weightSpace ρ T (w i))
    (hspan : (⨆ i, L i) = ⊤) (i : ι) :
    weightSpace ρ T (w i) = L i := by
  let Z := ⨆ χ : TorusWeight T, ⨆ (_ : χ ≠ w i), weightSpace ρ T χ
  have hdis : Disjoint (weightSpace ρ T (w i)) Z := weightSpace_iSupIndep ρ T (w i)
  apply Eq.symm
  apply eq_of_le_of_inf_le_of_le_sup (hL i) (z := Z)
  · rw [hdis.eq_bot]
    exact bot_le
  · apply le_trans le_top
    rw [← hspan]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst j
      exact le_sup_left
    · have hweight : w j ≠ w i := fun h => hji (hw h)
      have hz : weightSpace ρ T (w j) ≤ Z :=
        le_iSup_of_le (w j) (le_iSup_of_le hweight le_rfl)
      exact le_trans (hL j) (le_trans hz le_sup_right)

private theorem weightSpace_eq_bot_of_spanning_submodules
    {k : Type*} [Field k] {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G)
    {ι : Type*} (w : ι → TorusWeight T)
    (L : ι → Submodule k V) (hL : ∀ i, L i ≤ weightSpace ρ T (w i))
    (hspan : (⨆ i, L i) = ⊤) (χ : TorusWeight T)
    (hχ : ∀ i, w i ≠ χ) : weightSpace ρ T χ = ⊥ := by
  have hdis := weightSpace_iSupIndep ρ T χ
  have htop : (⊤ : Submodule k V) ≤
      ⨆ ψ : TorusWeight T, ⨆ (_ : ψ ≠ χ), weightSpace ρ T ψ := by
    rw [← hspan]
    exact iSup_le fun i => le_trans (hL i)
      (le_iSup_of_le (w i) (le_iSup_of_le (hχ i) le_rfl))
  simpa only [disjoint_top] using hdis.mono_right htop

end Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
namespace ClassBound.ConnectedCentralizer.Normalizer.RootUniqueness

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private noncomputable def tangentWeight (S : Geometry K) :
    Option S.roots.Root → TorusWeight S.torus
  | none => 1
  | some a => (S.roots.rootWeight a)⁻¹

private theorem tangentWeight_injective (S : Geometry K) :
    Function.Injective (tangentWeight S) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b =>
      have hb : S.roots.rootWeight b = 1 := by
        simpa only [tangentWeight, inv_inv, inv_one] using congrArg Inv.inv h.symm
      exact False.elim (S.realized.rootWeight_ne_one b hb)
  | some a =>
    cases j with
    | none =>
      have ha : S.roots.rootWeight a = 1 := by
        simpa only [tangentWeight, inv_inv, inv_one] using congrArg Inv.inv h
      exact False.elim (S.realized.rootWeight_ne_one a ha)
    | some b =>
      exact congrArg some (S.realized.1 (inv_injective h))

private theorem tangentWeight_ne_higher (S : Geometry K) (a : S.roots.Root)
    {n : ℕ} (hn : 2 ≤ n) (i : Option S.roots.Root) :
    tangentWeight S i ≠ ((S.roots.rootWeight a)⁻¹) ^ n := by
  intro h
  cases i with
  | none =>
    have ha : S.roots.rootWeight a ^ n = 1 := by
      simpa only [tangentWeight, inv_pow, inv_inv, inv_one] using congrArg Inv.inv h.symm
    exact rootWeight_pow_ne_one S a (by omega) ha
  | some b =>
    have ha : S.roots.rootWeight a ^ n = S.roots.rootWeight b := by
      simpa only [tangentWeight, inv_pow, inv_inv] using congrArg Inv.inv h.symm
    exact rootWeight_pow_ne_rootWeight S a b hn ha

private noncomputable def tangentSummand (S : Geometry K) :
    Option S.roots.Root → Submodule k (IdentityPointDerivation K)
  | none => LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion)
  | some a => LinearMap.range
      (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)

private theorem tangentSummand_le_weightSpace (S : Geometry K) (i : Option S.roots.Root) :
    tangentSummand S i ≤ weightSpace (identityTangentRepresentation K) S.torus
      (tangentWeight S i) := by
  cases i with
  | none => exact torusTangentRange_le_trivialWeight S.maximalTorus.1
  | some a =>
    change LinearMap.range
      (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion) ≤ _
    rw [tangentRange_eq_span (S.roots.rootSubgroup a) (S.rootParameter a)]
    apply Submodule.span_le.mpr
    rintro v (rfl : v = oneParameterTangent _ _)
    exact (oneParameterTangent_isWeightVector S.torus (S.roots.rootSubgroup a)
      (S.rootParameter a) (S.realized.2.2.1 a).2).2

omit [IsAlgClosed k] in
private theorem tangentSummand_iSup_eq (S : Geometry K) :
    (⨆ i, tangentSummand S i) =
      LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
        (⨆ a : S.roots.Root, LinearMap.range
          (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i with
    | none => exact le_sup_left
    | some a =>
      exact le_trans (le_iSup (fun b : S.roots.Root => LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup b).inclusion)) a)
        le_sup_right
  · refine sup_le (le_iSup (tangentSummand S) none) ?_
    exact iSup_le fun a => le_iSup (tangentSummand S) (some a)

/-- Tangent spanning identifies each inverse root weight space with its actual root line. -/
public theorem root_weightSpace_eq_of_tangent_span (S : Geometry K)
    (hspan : LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) = ⊤)
    (a : S.roots.Root) :
    weightSpace (identityTangentRepresentation K) S.torus (S.roots.rootWeight a)⁻¹ =
      Submodule.span k {oneParameterTangent (S.roots.rootSubgroup a) (S.rootParameter a)} := by
  have hs : (⨆ i, tangentSummand S i) = ⊤ := (tangentSummand_iSup_eq S).trans hspan
  have h := weightSpace_eq_of_spanning_submodules (identityTangentRepresentation K) S.torus
    (tangentWeight S) (tangentWeight_injective S) (tangentSummand S)
    (tangentSummand_le_weightSpace S) hs (some a)
  exact h.trans (tangentRange_eq_span (S.roots.rootSubgroup a) (S.rootParameter a))

/-- Spanning and integral character separation exclude all higher inverse-root weights. -/
public theorem root_higher_weightSpace_eq_bot_of_tangent_span (S : Geometry K)
    (hspan : LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) = ⊤)
    (a : S.roots.Root) (n : ℕ) (hn : 2 ≤ n) :
    weightSpace (identityTangentRepresentation K) S.torus ((S.roots.rootWeight a)⁻¹ ^ n) = ⊥ := by
  have hs : (⨆ i, tangentSummand S i) = ⊤ := (tangentSummand_iSup_eq S).trans hspan
  exact weightSpace_eq_bot_of_spanning_submodules (identityTangentRepresentation K) S.torus
    (tangentWeight S) (tangentSummand S) (tangentSummand_le_weightSpace S) hs _
    (tangentWeight_ne_higher S a hn)

/-- The actual tangent-spanning theorem suffices for scalar uniqueness of root curves. -/
public theorem root_multiplicityOne_of_tangent_span (S : Geometry K)
    (hspan : LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) = ⊤)
    (a : S.roots.Root) : RootWeightSpaceMultiplicityOne S.torus (S.roots.rootWeight a) := by
  apply rootWeightSpaceMultiplicityOne_of_tangent_finrank_eq_one
  · rw [root_weightSpace_eq_of_tangent_span S hspan a]
    exact finrank_span_singleton (oneParameterTangent_ne_zero _ _)
  · exact root_higher_weightSpace_eq_bot_of_tangent_span S hspan a

end ClassBound.ConnectedCentralizer.Normalizer.RootUniqueness
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
