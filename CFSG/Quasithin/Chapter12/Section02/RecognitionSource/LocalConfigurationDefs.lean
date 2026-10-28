module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import CFSG.Quasithin.Chapter3.Defs

/-!
# Intermediate source conclusions for the local analysis in 12.2.13

The first boundary is the solvable H-star and marked natural-action conclusion
of 12.2.18--20. The second retains the actual cyclic odd subgroup and TI pair
constructed in 12.2.21--24. In particular all cores, residuals, conjugates and
normality statements refer to the displayed subgroups of the original group.

These are statements to be proved by the local source producers, not new
hypotheses of 12.2.3. Neither their existence nor the final split configuration
is asserted here. The rigidity argument in 12.2.25 and the Sylow splitting
argument in 12.2.26 consume the second boundary.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.18--26, printed pp.800--806.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The actual surviving action and H-star conclusions of 12.2.18--20.
Existence of an escaping H-star member is retained explicitly. -/
structure NaturalLocalAnalysis (T : Sylow 2 G) (L V : Subgroup G) (d : ℕ) : Prop where
  dimension : 3 ≤ d ∧ d ≤ 5
  natural : Chapter6.Source.IsConjugationModel L V
    (Representation.specialLinearNatural (k := ZMod 2) d)
  exists_hstar : (Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))).Nonempty
  hstar_solvable : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
    Group.IsSolvable H
  hstar_movement : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
    ¬ V ≤ H.pCoreIn 2

/-- The literal group I=PUV after the cyclicity conclusion 12.2.23. -/
abbrev cyclicPairJoin (P U V : Subgroup G) : Subgroup G := P ⊔ U ⊔ V

/-- The cyclic TI-pair and block conclusions of 12.2.21--24.
The subgroup P has odd prime order. Its normal closure with U is the
two-residual of H, whereas U is the two-core of the pair join I. -/
structure CyclicLocalAnalysis (T : Sylow 2 G) (L V : Subgroup G) (d : ℕ)
    (H P U : Subgroup G) : Prop where
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))
  prime_order : (Nat.card P).Prime
  odd_order : Odd (Nat.card P)
  escapes : ¬ P ≤ normalizer (L : Set G)
  overgroup : H = P ⊔ (T : Subgroup G)
  elementary : IsElementaryAbelian 2 U
  in_core : U ≤ H.pCoreIn 2
  core : (cyclicPairJoin P U V).pCoreIn 2 = U
  residual : (pResidual 2 H).map H.subtype = P ⊔ U
  pair_normal : H ≤ normalizer (cyclicPairJoin P U V : Set G)
  pair : ∃ g ∈ P, g ≠ 1 ∧
    cyclicPairJoin P U V = V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
    U = (U ⊓ V) ⊔ (U ⊓ V).map (MulAut.conj g).toMonoidHom
  inverted : ∃ v ∈ V, v ∉ U ∧ ∀ x ∈ P, v * x * v⁻¹ = x⁻¹
  moved : ⁅U, P⁆ = U
  fixed : U ⊓ centralizer (P : Set G) = ⊥
  transvections : ⁅U, V⁆ = U ⊓ V
  action_kernel : U ⊓ centralizer (V : Set G) = U ⊓ V
  hyperplane : Nat.card (U ⊓ V : Subgroup G) = 2 ^ (d - 1)
  dimension : Nat.card U = 2 ^ (2 * (d - 1))
  block : ChapterC.IsLinearTwoBlock L d

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
