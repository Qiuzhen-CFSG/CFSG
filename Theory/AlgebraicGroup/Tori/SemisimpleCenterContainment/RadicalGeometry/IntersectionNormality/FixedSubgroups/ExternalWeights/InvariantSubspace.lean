module

public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces

/-!
A subspace invariant under a closed torus is the sum of its intersections
with the ambient character weight spaces. Pull the rational representation
back to the torus, restrict it to the invariant subspace, and map its weight
decomposition through the subspace inclusion. Characters of the top closed
subgroup are transported back to the original torus by its canonical inclusion
into that subgroup.

This is the linear decomposition used in Borel III, 9.4:
`refs/KGroup/Bor1/Chapter3.tex`. Invariance is required only under the acting
torus, so the result applies to external actions on subgroup tangents.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A subspace invariant under a closed subtorus decomposes into its
intersections with the ambient representation's character weight spaces. -/
public theorem closedSubtorusRepresentation_invariant_weightSpace_iSup_eq
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (W : Submodule k V)
    (hW : ∀ t : Variety.Point T.carrierVariety, ∀ v ∈ W,
      (ρ.action (T.includePoint t)).1 v ∈ W) :
    (⨆ χ : TorusWeight T, W ⊓ weightSpace ρ T χ) = W := by
  obtain ⟨τ, hτρ, hτ⟩ := rationalRepresentation_pullback_exists T.inclusion ρ hρ
  have hWτ : IsInvariantSubmodule τ W := by
    intro t v hv
    rw [hτρ t]
    exact hW t v hv
  obtain ⟨σ, hστ, hσ⟩ := rationalRepresentation_restriction_exists τ hτ W hWτ
  let S : ClosedSubgroup T.carrierVariety := ClosedSubgroup.top
  let : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism T.carrierVariety S.carrierVariety :=
    (AlgebraicGroup.Morphism.id T.carrierVariety).codRestrictClosedSubgroup S
      (fun _ => trivial)
  have hf (t : Variety.Point T.carrierVariety) : S.includePoint (f.onPoints t) = t := rfl
  have hspan := torusRepresentation_weightSpace_iSup_eq_top σ hσ hT
  apply le_antisymm (iSup_le fun _ => inf_le_left)
  calc
    W = Submodule.map W.subtype (⊤ : Submodule k W) := by
      rw [Submodule.map_top, Submodule.range_subtype]
    _ = ⨆ χ : TorusWeight S, Submodule.map W.subtype (weightSpace σ S χ) := by
      rw [← hspan, Submodule.map_iSup]
    _ ≤ ⨆ χ : TorusWeight T, W ⊓ weightSpace ρ T χ := by
      apply iSup_le
      intro χ
      apply le_trans _ (le_iSup (fun ψ : TorusWeight T => W ⊓ weightSpace ρ T ψ)
        (χ.comp f))
      rintro v ⟨w, hw, rfl⟩
      refine ⟨w.property, ?_⟩
      intro t
      have ht := hw (f.onPoints t)
      change (σ.action (S.includePoint (f.onPoints t))).1 w =
        χ.pointCharacter (f.onPoints t) • w at ht
      rw [hf] at ht
      calc
        (ρ.action (T.includePoint t)).1 (W.subtype w) =
            (τ.action t).1 (W.subtype w) := by rw [hτρ t]; rfl
        _ = W.subtype ((σ.action t).1 w) := (hστ t w).symm
        _ = χ.pointCharacter (f.onPoints t) • W.subtype w := by
          rw [ht, map_smul]
        _ = TorusCharacter.pointCharacter (χ.comp f) t • W.subtype w := rfl

end Theory.AlgebraicGroup
