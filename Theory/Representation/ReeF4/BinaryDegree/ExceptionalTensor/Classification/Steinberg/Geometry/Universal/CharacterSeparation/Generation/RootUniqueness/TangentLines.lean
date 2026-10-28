module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.CharacterPowers
public import Theory.AlgebraicGroup.RootSubgroups.TangentMultiplicityOne

/-!
# Literal F4 tangent lines and root-weight multiplicity

Each canonical additive root parametrization has a nonzero identity tangent
of the inverse root weight. These characters are distinct from each other
and from the trivial character. If their lines together with the fixed
tangent space span the full identity tangent, independence of character
weight spaces identifies each root weight space with its canonical line and
excludes all higher inverse-root weights. Tangent rigidity then integrates
proportional tangents to scalar equality of the ambient root curves.

The spanning equality remains an explicit geometric input. No generation of
an arbitrary root model, full root catalogue, or faithfulness of character
differentiation is assumed. This is a reduction for GLS3, Theorem 1.9.5(b),
`refs/KGroup/GLS3/Chapter1.tex`, rather than a proof of its geometric input.
-/

public section

namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem weightSpace_eq_of_spanning_lines
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

private theorem weightSpace_eq_bot_of_spanning_lines
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

namespace Theory.AlgebraicGroup.F4Chevalley
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual tangent of the canonical additive root parametrization. -/
@[expose] noncomputable def concreteRootTangent (r : Root) :
    IdentityPointDerivation (Carrier (k := k)) :=
  oneParameterTangent (rootSubgroup r) (rootParametrization r)

lemma concreteRootTangent_isWeightVector (r : Root) :
    IsWeightVector (identityTangentRepresentation (Carrier (k := k))) splitTorus
      (concreteRootTangent r) (rootWeight r)⁻¹ :=
  oneParameterTangent_isWeightVector splitTorus (rootSubgroup r)
    (rootParametrization r) (rootWeightEquation r)

/-- The inverse root weights, with a separate trivial weight. -/
@[expose] noncomputable def concreteTangentWeight : Option Root → TorusWeight (splitTorus (k := k))
  | none => 1
  | some r => (rootWeight r)⁻¹

lemma concreteTangentWeight_injective : Function.Injective (concreteTangentWeight (k := k)) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some s =>
      have hs : rootWeight (k := k) s = 1 := by
        simpa only [concreteTangentWeight, inv_inv, inv_one] using congrArg Inv.inv h.symm
      exact False.elim (concreteRootWeight_ne_one s hs)
  | some r =>
    cases j with
    | none =>
      have hr : rootWeight (k := k) r = 1 := by
        simpa only [concreteTangentWeight, inv_inv, inv_one] using congrArg Inv.inv h
      exact False.elim (concreteRootWeight_ne_one r hr)
    | some s =>
      have hrs : rootWeight (k := k) r = rootWeight s := inv_injective h
      exact congrArg some (concreteRootWeight_injective hrs)

lemma concreteTangentWeight_ne_higher (r : Root) {n : ℕ} (hn : 2 ≤ n)
    (i : Option Root) :
    concreteTangentWeight (k := k) i ≠ ((rootWeight r)⁻¹) ^ n := by
  intro h
  cases i with
  | none =>
    have hr : rootWeight (k := k) r ^ n = 1 := by
      simpa only [concreteTangentWeight, inv_pow, inv_inv, inv_one] using congrArg Inv.inv h.symm
    exact concreteRootWeight_pow_ne_one r (by omega) hr
  | some s =>
    have hr : rootWeight (k := k) r ^ n = rootWeight s := by
      simpa only [concreteTangentWeight, inv_pow, inv_inv] using congrArg Inv.inv h.symm
    exact concreteRootWeight_pow_ne r s hn hr

/-- The fixed tangent space and the individual literal root tangent lines. -/
@[expose] noncomputable def concreteTangentSummand :
    Option Root → Submodule k (IdentityPointDerivation (Carrier (k := k)))
  | none => weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus 1
  | some r => Submodule.span k {concreteRootTangent r}

lemma concreteTangentSummand_le_weightSpace (i : Option Root) :
    concreteTangentSummand (k := k) i ≤
      weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus
        (concreteTangentWeight i) := by
  cases i with
  | none => exact le_rfl
  | some r =>
    apply Submodule.span_le.mpr
    rintro v (rfl : v = concreteRootTangent r)
    exact (concreteRootTangent_isWeightVector r).2

/-- Tangent spanning identifies each root weight space with its literal tangent line. -/
lemma concreteRoot_weightSpace_eq_of_tangent_span
    (hspan : (⨆ i, concreteTangentSummand (k := k) i) = ⊤) (r : Root) :
    weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus
        (rootWeight r)⁻¹ = Submodule.span k {concreteRootTangent r} :=
  weightSpace_eq_of_spanning_lines
    (identityTangentRepresentation (Carrier (k := k))) (splitTorus (k := k))
    concreteTangentWeight concreteTangentWeight_injective
    concreteTangentSummand concreteTangentSummand_le_weightSpace hspan (some r)

/-- Tangent spanning excludes all higher inverse-root weights. -/
lemma concreteRoot_higher_weightSpace_eq_bot_of_tangent_span
    (hspan : (⨆ i, concreteTangentSummand (k := k) i) = ⊤)
    (r : Root) (n : ℕ) (hn : 2 ≤ n) :
    weightSpace (identityTangentRepresentation (Carrier (k := k))) splitTorus
        ((rootWeight r)⁻¹ ^ n) = ⊥ :=
  weightSpace_eq_bot_of_spanning_lines
    (identityTangentRepresentation (Carrier (k := k))) (splitTorus (k := k))
    concreteTangentWeight
    concreteTangentSummand concreteTangentSummand_le_weightSpace hspan _
    (concreteTangentWeight_ne_higher r hn)

/-- Tangent spanning gives scalar uniqueness of all parametrizations at a root weight. -/
lemma concreteRoot_multiplicityOne_of_tangent_span
    (hspan : (⨆ i, concreteTangentSummand (k := k) i) = ⊤) (r : Root) :
    RootWeightSpaceMultiplicityOne splitTorus (rootWeight (k := k) r) := by
  apply rootWeightSpaceMultiplicityOne_of_tangent_finrank_eq_one
  · rw [concreteRoot_weightSpace_eq_of_tangent_span hspan r]
    exact finrank_span_singleton (concreteRootTangent_isWeightVector r).1
  · exact concreteRoot_higher_weightSpace_eq_bot_of_tangent_span hspan r


end Theory.AlgebraicGroup.F4Chevalley
