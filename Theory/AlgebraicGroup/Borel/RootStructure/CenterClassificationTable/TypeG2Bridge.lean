module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4

/-!
The final character-lattice reduction for the type `G₂` row of the center
table in GLS3, Theorem 1.12.5(c)-(d), Table 1.12.5.

For a maximal torus `T`, the center-character description identifies the
ambient center with the character group of
`TorusWeight T ⧸ TorusRootLattice T`.  If the realized roots generate every
torus character, that quotient is trivial, so the center is trivial as well.
Since `universalCenterShape` is definitionally `.trivial` in type `G₂`, the
same equality proves both the universal-version shape and the
arbitrary-version homomorphic-image assertion.

The determinant-one `G₂` Cartan calculation is already available as
`dynkinCartanRelationKernel_G2`.  Transporting it through an actual root
realization to prove `TorusRootLattice T = ⊤` is kept explicit at this module
boundary: `HasRootSystemType` currently compares pairings only on realized
roots and does not by itself identify their lattice with the full torus
character group.  This module therefore uses no placeholder-backed global
center-classification theorem.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k]

private theorem center_eq_bot_of_centerCharacterEquiv_of_rootLattice_eq_top
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ)))
    (hRoot : TorusRootLattice T = ⊤) :
    Subgroup.center (Variety.Point K) = ⊥ := by
  obtain ⟨e⟩ := hCenter
  apply le_antisymm
  · intro z hz
    apply Subgroup.mem_bot.mpr
    let zCenter : Subgroup.center (Variety.Point K) := ⟨z, hz⟩
    have hEval : e zCenter = e 1 := by
      apply MonoidHom.ext
      intro q
      refine Quotient.inductionOn q ?_
      intro χ
      have hq : QuotientGroup.mk' (TorusRootLattice T) χ = 1 := by
        apply (QuotientGroup.eq_one_iff χ).2
        rw [hRoot]
        exact Subgroup.mem_top χ
      change e zCenter (QuotientGroup.mk' (TorusRootLattice T) χ) =
        e 1 (QuotientGroup.mk' (TorusRootLattice T) χ)
      rw [hq, map_one, map_one]
    exact congrArg Subtype.val (e.injective hEval)
  · exact bot_le

/-- The common character-lattice endpoint for the type-`G₂` center table.
Once actual roots span the full torus character group, the universal center
and the center of every isogenous version are both trivial. -/
public theorem typeG2_center_classification_of_rootLattice_eq_top
    {K : Variety k} [AlgebraicGroup K]
    (m : ℕ)
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.G2, m⟩)
    (_hValid : IsValidGeneratorTableClassification ⟨.G2, m⟩)
    (T : ClosedSubgroup K)
    (hCenter : Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ)))
    (hRoot : TorusRootLattice T = ⊤) :
    (IsUniversalVersion K →
      HasCenterShape (K := K) (universalCenterShape ⟨.G2, m⟩)) ∧
    IsCenterHomomorphicImageOfShape (K := K)
      (universalCenterShape ⟨.G2, m⟩) := by
  have hCenterBot : Subgroup.center (Variety.Point K) = ⊥ :=
    center_eq_bot_of_centerCharacterEquiv_of_rootLattice_eq_top
      T hCenter hRoot
  simpa [universalCenterShape, HasCenterShape,
    IsCenterHomomorphicImageOfShape] using
      And.intro (fun _ => hCenterBot) hCenterBot

end Theory.AlgebraicGroup
