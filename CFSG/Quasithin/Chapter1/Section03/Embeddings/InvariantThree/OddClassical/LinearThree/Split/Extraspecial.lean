module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Extraspecial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Extraspecial.Placement
public import Theory.SpecificGroups.SL3.SplitMonomial.LocalCore

/-!
# The extraspecial split local three-core

The complement R is Sylow three in RS, so the order of the intersection
required by the source is exactly |O₃(RS)|. The monomial placement theorem
constructs a permuted line basis from the solvable product. Then
an actual model equivalence transports both this core and the full Sylow
two-subgroup. A core calculation in the corresponding concrete monomial
subgroup then gives the required order nine. Extraspeciality supplies a
nonabelian three-subgroup in the model; the product order alone would also
allow abelian odd parts contained entirely in the diagonal torus.

The final theorem discharges the geometric placement and both monomial
core calculations, establishing the intersection order from `PairInput`
and the actual `LinearThreeModel`. The central-cover reduction and the
remaining split-branch assembly belong to the parent development.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof
of Proposition 1.3.4, printed p.511 (PDF p.528); GLS3, proof of Theorem
6.5.3, cases (a)–(d), in `refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split

universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Assemble the required intersection order from actual monomial placement
and core computations. All three premises must be proved before this is
used as the unconditional split-branch calculation. -/
theorem extraspecial_local_core_nine_of_monomial_calculations
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    {p : ℕ} (hplace : Extraspecial.MonomialPlacement p (R ⊔ (S : Subgroup Q)))
    (hlinear : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F))
        (H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)),
        (T : Subgroup _) ≤ H → H ≤ Matrix.SL3.SplitMonomial.linear F →
        (∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F),
          U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        Nat.card H = 27 * Nat.card T → Nat.card (pCore 3 H) = 9)
    (hprojective : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
        (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)),
        (T : Subgroup _) ≤ H → H ≤ Matrix.SL3.SplitMonomial.projective F →
        (∃ U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
          U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        Nat.card H = 27 * Nat.card T → Nat.card (pCore 3 H) = 9) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  rcases hplace with ⟨F, _, _, hF, e, he⟩ | ⟨F, _, _, hF, e, he⟩
  · rw [Extraspecial.local_core_intersection_card_of_equiv h e]
    exact hlinear F hF (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)
      (Extraspecial.model_sylow_le_product e) he
      (Extraspecial.model_nonabelian_three_subgroup h hc e)
      (Extraspecial.model_product_card h hc e)
  · rw [Extraspecial.local_core_intersection_card_of_equiv h e]
    exact hprojective F hF (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)
      (Extraspecial.model_sylow_le_product e) he
      (Extraspecial.model_nonabelian_three_subgroup h hc e)
      (Extraspecial.model_product_card h hc e)

/-- For an extraspecial split SL₃ or PSL₃ pair, the three-core of the actual
product RS intersects R in a subgroup of order nine. Extraspeciality and
exponent three follow from the odd-complement alternative in `h`; no
normality of R or additional placement assumption is required. -/
theorem extraspecial_local_core_nine
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : 3 < p) (hpmod : p % 3 = 1)
    (hmodel : LinearThreeModel p Q) (hc : Nat.card R = 27) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  apply extraspecial_local_core_nine_of_monomial_calculations h hc
    (Extraspecial.monomialPlacement_of_extraspecial h hc hp hpodd hp3 hpmod hmodel)
  · intro F _ _ hF
    exact Matrix.SL3.SplitMonomial.linear_core_card_nine F hF hp hpodd hp3 hpmod
  · intro F _ _ hF
    exact Matrix.SL3.SplitMonomial.projective_core_card_nine F hF hp hpodd hp3 hpmod

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
