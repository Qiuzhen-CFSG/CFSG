module

public import GorensteinWalter.PGammaL2OuterProduct

/-!
# The two concrete outer generation calculations for K.2

These propositions specify the remaining diagonal and field calculations on
actual PGammaL₂. Every conjugator is in its literal PSL₂ subgroup. This ensures
that the witnesses transport to the original ambient group; a conjugator in
an arbitrary larger automorphism group would not give that conclusion.

The field clause includes every involution with nontrivial field coordinate,
including any putative mixed diagonal--field case. Its proof must handle or
exclude that case using the actual semilinear action.

These are contracts, not assertions of generation. Source: Guralnick--Malle,
Classification of 2F-modules I, Proposition 4.1, manuscript pp.8--9;
Aschbacher--Smith K.2, printed p.453.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
open Subgroup GorensteinWalter
universe u

/-- Four conjugates of a diagonal outer involution, with inner conjugators. -/
def DiagonalFourGeneration : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] {p e : ℕ},
    p.Prime → Odd p → (e = 1 ∨ e = 2) → Nat.card F = p ^ e → 25 < p ^ e →
    ∀ t : PGammaL2 F, t ∉ pGammaL2PSLRange F → t ^ 2 = 1 → t.right = 1 →
    ∃ c : Fin 4 → PSL2 F, pGammaL2PSLRange F ≤
      Subgroup.closure (Set.range fun i =>
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)) * t *
          (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)))⁻¹)

/-- Four conjugates for the nontrivial field coordinate, with inner conjugators. -/
def FieldFourGeneration : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] {p e : ℕ},
    p.Prime → Odd p → (e = 1 ∨ e = 2) → Nat.card F = p ^ e → 25 < p ^ e →
    ∀ t : PGammaL2 F, t ∉ pGammaL2PSLRange F → t ^ 2 = 1 → t.right ≠ 1 →
    ∃ c : Fin 4 → PSL2 F, pGammaL2PSLRange F ≤
      Subgroup.closure (Set.range fun i =>
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)) * t *
          (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)))⁻¹)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
