module

public import Theory.Character.ModularBlock.SubgroupPrincipalBrauerData
public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent

/-!
# Maximal primitive extra obstructions

An extra obstruction is a two-subgroup whose direct principal Brauer
complement has a primitive central-idempotent factor of augmentation zero.
Among a nonempty family of extra obstructions in a finite group, choose one
of maximal order using finiteness of the subgroup lattice. This provides
the maximality measure for the Third Main contradiction, independently of
the preceding construction of an obstruction from failed Brauer equality.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock.BrauerThirdMain

open ModularBlock PrincipalBlockConstruction

universe v

/-- A subgroup carries an extra obstruction when the direct Brauer image of
the ambient principal selector has a primitive augmentation-zero factor. -/
@[expose] def IsExtraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧
    ∃ b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)),
      IsCentrallyPrimitive b ∧
        groupAlgebraAugmentation
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b

/-- Since the subgroup lattice is finite, a nonempty family of extra
obstructions has a member of maximal order. -/
theorem exists_maximal_extraObstruction
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (hex : ∃ Q : Subgroup G, IsExtraObstruction d Q) :
    ∃ Q : Subgroup G,
      IsExtraObstruction d Q ∧
        ∀ D : Subgroup G, IsExtraObstruction d D →
          Nat.card D ≤ Nat.card Q := by
  classical
  let S : Set (Subgroup G) := {Q | IsExtraObstruction d Q}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := by
    rcases hex with ⟨Q, hQ⟩
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQmax⟩ :=
    hSfinite.exists_maximalFor (fun D : Subgroup G ↦ Nat.card D) S hSne
  refine ⟨Q, hQmax.1, ?_⟩
  intro D hD
  exact hQmax.le hD

end ModularBlock.BrauerThirdMain

