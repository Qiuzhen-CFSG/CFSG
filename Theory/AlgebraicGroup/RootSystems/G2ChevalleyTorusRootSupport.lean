module

public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Dimension.Isomorphism
public import Theory.AlgebraicGroup.RootSubgroups.MaximalTorusTangentDecomposition
public import Theory.AlgebraicGroup.RootSubgroups.NormalizerMembership
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyBruhatDimension
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRootCurves
public import Theory.AlgebraicGroup.RootSystems.G2ChevalleySplitTorusCentralizer

/-!
# Tangent-weight support for the G2 Chevalley carrier

This module identifies every nontrivial inverse split-torus weight occurring in
the identity tangent space of the closed `G2` Chevalley carrier with one of the
twelve explicit root weights.  Combining this support calculation with the
explicit split-torus centralizer equality shows that the torus roots are exactly
the range of those twelve weights.

The proof takes the twelve nonzero tangents of the explicit root curves and the
two-dimensional tangent of the split torus.  Their thirteen distinct weights
make the root tangents independent and their span disjoint from the torus
tangent.  The explicit Bruhat-cover dimension bound then forces these fourteen
directions to exhaust the identity tangent.  Independence of torus weight
spaces excludes every further nonzero weight.

All root curves and torus characters come from the integral Chevalley matrices,
the dimension bound and centralizer equality use the explicit finite Bruhat
cover, and the reverse inclusion differentiates an arbitrary root curve.
Consequently no division by the bad primes is used, so the argument applies
unchanged in characteristics two and three.  The construction is independent
of general root-system classification and of downstream semisimplicity or
center results.
-/

open scoped BigOperators

namespace Theory.AlgebraicGroup.G2Chevalley

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

private def rootWeightExponentTable : Root -> Fin 2 -> Int
  | 0 => ![2, -1]
  | 1 => ![-3, 2]
  | 2 => ![-1, 1]
  | 3 => ![1, 0]
  | 4 => ![3, -1]
  | 5 => ![0, 1]
  | 6 => ![-2, 1]
  | 7 => ![3, -2]
  | 8 => ![1, -1]
  | 9 => ![-1, 0]
  | 10 => ![-3, 1]
  | 11 => ![0, -1]

private lemma rootWeightExponent_eq_table (r : Root) :
    rootWeightExponent r = rootWeightExponentTable r := by
  rcases rootWeightExponent_values with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  fin_cases r <;>
    simp [rootWeightExponentTable, Root.short, Root.long, Root.shortLong,
      Root.twoShortLong, Root.threeShortLong, Root.threeShortTwoLong,
      Root.negShort, Root.negLong, Root.negShortLong, Root.negTwoShortLong,
      Root.negThreeShortLong, Root.negThreeShortTwoLong] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢ <;>
    assumption

private lemma rootWeightExponent_injective :
    Function.Injective rootWeightExponent := by
  intro r s hrs
  rw [rootWeightExponent_eq_table, rootWeightExponent_eq_table] at hrs
  fin_cases r <;> fin_cases s <;>
    simp [rootWeightExponentTable] at hrs ⊢

private lemma rootWeightExponent_ne_zero (r : Root) :
    rootWeightExponent r ≠ 0 := by
  rw [rootWeightExponent_eq_table]
  fin_cases r <;> simp [rootWeightExponentTable]

private lemma rootWeight_eq_exponent_eq {r s : Root}
    (hrs : rootWeight (k := k) r = rootWeight (k := k) s) :
    rootWeightExponent r = rootWeightExponent s := by
  apply dLaurentCharacter_injective (k := k) 2
  have h := congrArg
    (fun chi : TorusWeight (splitTorus (k := k)) =>
      chi.comp (splitTorusIso (k := k)).hom) hrs
  simpa only [rootWeight_comp_splitTorusIso] using h

private lemma rootWeight_injective :
    Function.Injective (rootWeight (k := k)) := by
  intro r s hrs
  apply rootWeightExponent_injective
  exact rootWeight_eq_exponent_eq hrs

private lemma rootWeight_ne_one (r : Root) :
    rootWeight (k := k) r ≠ 1 := by
  intro hr
  have hexp : rootWeightExponent r = 0 := by
    apply dLaurentCharacter_injective (k := k) 2
    have h := congrArg
      (TorusCharacter.pullback (splitTorusIso (k := k)).hom) hr
    rw [map_one] at h
    change (rootWeight (k := k) r).comp
      (splitTorusIso (k := k)).hom = 1 at h
    rw [rootWeight_comp_splitTorusIso] at h
    calc
      dLaurentCharacter (k := k) 2 (rootWeightExponent r) = 1 := h
      _ = dLaurentCharacter (k := k) 2 0 := by
        simp [dLaurentCharacter]
  exact rootWeightExponent_ne_zero r hexp

private noncomputable def rootTangent (r : Root) :
    IdentityPointDerivation (Carrier (k := k)) :=
  oneParameterTangent (rootSubgroup (k := k) r) (rootParametrization r)

private theorem rootTangents_linearIndependent :
    LinearIndependent k (rootTangent (k := k)) := by
  let weights : Root -> TorusWeight (splitTorus (k := k)) :=
    fun r => (rootWeight (k := k) r)⁻¹
  have hweights : Function.Injective weights := by
    intro r s hrs
    exact rootWeight_injective (inv_injective hrs)
  let p : Root -> Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
    fun r => weightSpace (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k)) (weights r)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep
      (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k))).comp hweights
  apply iSupIndep.linearIndependent p hp
  · intro r
    exact (oneParameterTangent_isWeightVector
      (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootParametrization r) (rootWeightEquation r)).2
  · intro r
    exact (oneParameterTangent_isWeightVector
      (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootParametrization r) (rootWeightEquation r)).1

private noncomputable def rootTangentSpan :
    Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
  Submodule.span k (Set.range (rootTangent (k := k)))

private lemma rootTangentSpan_finrank :
    Module.finrank k (rootTangentSpan (k := k)) = 12 := by
  rw [rootTangentSpan, finrank_span_eq_card rootTangents_linearIndependent]
  exact Fintype.card_fin 12

private noncomputable def torusTangentRange :
    Submodule k (IdentityPointDerivation (Carrier (k := k))) :=
  LinearMap.range (identityTangentMorphismLinearMap
    (splitTorus (k := k)).inclusion)

private lemma torusTangentRange_finrank :
    Module.finrank k (torusTangentRange (k := k)) = 2 := by
  rw [torusTangentRange,
    LinearMap.finrank_range_of_inj
      (identityTangentMorphismLinearMap_inclusion_injective
        (splitTorus (k := k))),
    Bor1.identityPointDerivation_finrank_eq_dimension]
  have hdim := algebraicGroupIso_dimension_eq (splitTorusIso (k := k))
  rw [dVariety_dimension_eq] at hdim
  simpa using congrArg Cardinal.toNat hdim.symm

private lemma torusTangentRange_le_zeroWeight :
    torusTangentRange (k := k) ≤
      weightSpace (identityTangentRepresentation (Carrier (k := k)))
        (splitTorus (k := k)) 1 := by
  rintro D ⟨E, rfl⟩
  intro s
  apply Derivation.ext
  intro f
  have hone : (1 : TorusWeight (splitTorus (k := k))).pointCharacter s = 1 :=
    rfl
  rw [hone, one_smul, identityTangentRepresentation_action_apply,
    identityTangentMorphismLinearMap_apply,
    identityTangentMorphismLinearMap_apply]
  change E ((splitTorus (k := k)).inclusion.toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism (Carrier (k := k))
        ((splitTorus (k := k)).includePoint s)).pullbackAlgHom f)) =
    E ((splitTorus (k := k)).inclusion.toVariety.pullbackAlgHom f)
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((splitTorus (k := k)).includePoint s *
      (splitTorus (k := k)).includePoint x *
      ((splitTorus (k := k)).includePoint s)⁻¹) =
    f ((splitTorus (k := k)).includePoint x)
  congr 1
  have hcomm : (splitTorus (k := k)).includePoint s *
      (splitTorus (k := k)).includePoint x =
        (splitTorus (k := k)).includePoint x *
          (splitTorus (k := k)).includePoint s := by
    have hcommT := (splitTorus_isSubtorus (k := k)).isMulCommutative
    rw [isMulCommutative_iff] at hcommT
    exact congrArg (splitTorus (k := k)).inclusion.onPoints (hcommT s x)
  rw [hcomm]
  simp

private noncomputable def tangentWeightIndex : Option Root ->
    TorusWeight (splitTorus (k := k))
  | none => 1
  | some r => (rootWeight (k := k) r)⁻¹

private lemma tangentWeightIndex_injective :
    Function.Injective (tangentWeightIndex (k := k)) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some r =>
          exfalso
          apply rootWeight_ne_one (k := k) r
          have h := congrArg Inv.inv hab
          simpa [tangentWeightIndex] using h.symm
  | some r =>
      cases b with
      | none =>
          exfalso
          apply rootWeight_ne_one (k := k) r
          have h := congrArg Inv.inv hab
          simpa [tangentWeightIndex] using h
      | some s =>
          congr 1
          apply rootWeight_injective (k := k)
          exact inv_injective hab

private lemma torusTangentRange_disjoint_rootTangentSpan :
    Disjoint (torusTangentRange (k := k)) (rootTangentSpan (k := k)) := by
  let p : Option Root ->
      Submodule k (IdentityPointDerivation (Carrier (k := k))) := fun i =>
    weightSpace (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k)) (tangentWeightIndex i)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep
      (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k))).comp tangentWeightIndex_injective
  have hdisjoint : Disjoint (p none)
      (⨆ i ∈ Set.range (@some Root), p i) :=
    hp.disjoint_biSup (x := none) (y := Set.range (@some Root)) (by simp)
  apply hdisjoint.mono
  · simpa [p, tangentWeightIndex] using
      torusTangentRange_le_zeroWeight (k := k)
  · rw [rootTangentSpan]
    apply Submodule.span_le.mpr
    rintro D ⟨r, rfl⟩
    have hle : p (some r) ≤ (⨆ i ∈ Set.range (@some Root), p i) :=
      le_iSup_of_le (some r)
        (le_iSup_of_le
          (show some r ∈ Set.range (@some Root) from ⟨r, rfl⟩)
          (le_refl (p (some r))))
    apply hle
    change oneParameterTangent (rootSubgroup (k := k) r)
      (rootParametrization r) ∈
        weightSpace (identityTangentRepresentation (Carrier (k := k)))
          (splitTorus (k := k)) ((rootWeight (k := k) r)⁻¹)
    exact (oneParameterTangent_isWeightVector
      (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootParametrization r) (rootWeightEquation r)).2

private lemma carrier_identityTangent_finrank_le_fourteen :
    Module.finrank k (IdentityPointDerivation (Carrier (k := k))) ≤ 14 := by
  rw [Bor1.identityPointDerivation_finrank_eq_dimension]
  exact carrier_dimension_le_fourteen (k := k)

private theorem torus_root_tangentSpan_eq_top :
    torusTangentRange (k := k) ⊔ rootTangentSpan (k := k) = ⊤ := by
  apply Submodule.eq_top_of_disjoint
  · rw [torusTangentRange_finrank, rootTangentSpan_finrank]
    exact carrier_identityTangent_finrank_le_fourteen
  · exact torusTangentRange_disjoint_rootTangentSpan

/-- Every nontrivial inverse split-torus weight occurring in the carrier's
identity tangent is one of the twelve explicit G2 root weights. -/
public theorem tangentWeight_eq_rootWeight
    (chi : TorusWeight (splitTorus (k := k))) (hchi : chi ≠ 1)
    {D : IdentityPointDerivation (Carrier (k := k))}
    (hD : IsWeightVector
      (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k)) D chi⁻¹) :
    ∃ r : Root, chi = rootWeight (k := k) r := by
  by_contra hnone
  push Not at hnone
  let p : TorusWeight (splitTorus (k := k)) ->
      Submodule k (IdentityPointDerivation (Carrier (k := k))) := fun psi =>
    weightSpace (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k)) psi
  have hnot : chi⁻¹ ∉ Set.range (tangentWeightIndex (k := k)) := by
    rintro ⟨i, hi⟩
    cases i with
    | none =>
        apply hchi
        have hinv := congrArg Inv.inv hi
        simpa [tangentWeightIndex] using hinv.symm
    | some r =>
        apply hnone r
        exact inv_injective hi.symm
  have hdisjoint : Disjoint (p chi⁻¹)
      (⨆ psi ∈ Set.range (tangentWeightIndex (k := k)), p psi) :=
    (weightSpace_iSupIndep
      (identityTangentRepresentation (Carrier (k := k)))
      (splitTorus (k := k))).disjoint_biSup hnot
  have htorus : torusTangentRange (k := k) ≤
      (⨆ psi ∈ Set.range (tangentWeightIndex (k := k)), p psi) := by
    refine (torusTangentRange_le_zeroWeight (k := k)).trans ?_
    have hone : (1 : TorusWeight (splitTorus (k := k))) =
        tangentWeightIndex (k := k) none := by rfl
    rw [hone]
    exact le_iSup_of_le (tangentWeightIndex (k := k) none)
      (le_iSup_of_le ⟨none, rfl⟩ (le_refl _))
  have hroots : rootTangentSpan (k := k) ≤
      (⨆ psi ∈ Set.range (tangentWeightIndex (k := k)), p psi) := by
    rw [rootTangentSpan]
    apply Submodule.span_le.mpr
    rintro v ⟨r, rfl⟩
    have hle : p ((rootWeight (k := k) r)⁻¹) ≤
        (⨆ psi ∈ Set.range (tangentWeightIndex (k := k)), p psi) :=
      le_iSup_of_le ((rootWeight (k := k) r)⁻¹)
        (le_iSup_of_le ⟨some r, rfl⟩ (le_refl _))
    apply hle
    exact (oneParameterTangent_isWeightVector
      (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootParametrization r) (rootWeightEquation r)).2
  have hDknown : D ∈
      (⨆ psi ∈ Set.range (tangentWeightIndex (k := k)), p psi) := by
    apply (sup_le htorus hroots)
    rw [torus_root_tangentSpan_eq_top]
    trivial
  have hDweight : D ∈ p chi⁻¹ := hD.2
  exact hD.1 (Submodule.disjoint_def.mp hdisjoint D hDweight hDknown)

/-- Every explicit G2 weight is realized by its root curve. -/
@[simp]
public theorem rootWeight_mem_torusRootSet (r : Root) :
    rootWeight (k := k) r ∈ TorusRootSet (splitTorus (k := k)) := by
  exact ⟨rootSubgroup (k := k) r, rootSubgroup_package (k := k) r⟩

/-- The twelve explicit G2 weights are exactly the torus roots of the split
torus in the closed integral Chevalley carrier. -/
public theorem rootWeight_range :
    Set.range (rootWeight (k := k)) =
      TorusRootSet (splitTorus (k := k)) := by
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact rootWeight_mem_torusRootSet r
  · intro chi hchi
    rcases hchi with ⟨X, hX, hEq⟩
    let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
    have hchine : chi ≠ 1 :=
      hX.rootWeight_ne_one_of_centralizer_eq
        (splitTorus_isSubtorus (k := k))
        (splitTorus_centralizer_eq (k := k)) chi hEq
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    obtain ⟨r, hr⟩ := tangentWeight_eq_rootWeight chi hchine
      (oneParameterTangent_isWeightVector
        (splitTorus (k := k)) X x hEq)
    exact ⟨r, hr.symm⟩

end

end Theory.AlgebraicGroup.G2Chevalley
