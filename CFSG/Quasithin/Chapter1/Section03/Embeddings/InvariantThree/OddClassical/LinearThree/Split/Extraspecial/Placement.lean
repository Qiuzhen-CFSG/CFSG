module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Extraspecial.Reduction
public import Theory.SpecificGroups.SL3.SplitMonomial.ProjectiveLift
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis

/-!
# Concrete monomial placement from the linear geometric argument

For the genuine pair RS, transport solvability, the full ambient Sylow
two-subgroup, and the nonabelian three-subgroup through the supplied model
isomorphism. In the projective case, lift these properties to the full inverse
image in SL₃, retaining its scalar kernel. A permuted line basis then gives an
actual SL₃ automorphism, or its induced PSL₃ automorphism, placing RS in the
concrete split monomial subgroup.

The linear geometry has two steps. Fitting theory and the normalizer bound
for nonabelian three-subgroups supply a noncentral abelian subgroup normal
in the solvable overgroup. Clifford theory and exclusion of the irreducible
abelian alternative then construct a permuted line basis over the original
field. The final theorem discharges both steps without extra placement or
local-action assumptions.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, proof of Theorem 6.5.3,
cases (a)–(d) and decomposition (6.5.1), `refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup Theory.GroupTheory
open Matrix.SL3.SplitMonomial
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.Extraspecial
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}

private theorem transported_product_solvable (h : PairInput S R)
    {G : Type v} [Group G] (e : Q ≃* G) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) := by
  let _ := EvenRankTwo.product_solvable h
  exact Group.isSolvable_of_surjective
    (f := (e.subgroupMap (R ⊔ (S : Subgroup Q))).toMonoidHom)
    (e.subgroupMap (R ⊔ (S : Subgroup Q))).surjective

/-- Reduce both actual model alternatives to the same linear invariant-basis
problem. -/
theorem monomialPlacement_of_linear_geometry {p : ℕ}
    (h : PairInput S R) (hc : Nat.card R = 27) (hmodel : LinearThreeModel p Q)
    (hgeom : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 SL(3,F)) (H : Subgroup SL(3,F)), Group.IsSolvable H →
        (T : Subgroup _) ≤ H →
        (∃ U : Subgroup SL(3,F), U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasInvariantBasis H) :
    MonomialPlacement p (R ⊔ (S : Subgroup Q)) := by
  rcases hmodel with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have hb := hgeom F hF
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)
      (transported_product_solvable h e) (model_sylow_le_product e)
      (model_nonabelian_three_subgroup h hc e)
    obtain ⟨a, ha⟩ := exists_linear_map_le_of_invariant_basis _ hb
    refine Or.inl ⟨F, inferInstance, inferInstance, hF, e.trans a, ?_⟩
    rw [Subgroup.map_map] at ha
    exact ha
  · let H := (R ⊔ (S : Subgroup Q)).map e.toMonoidHom
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let _ : Group.IsSolvable H := transported_product_solvable h e
    obtain ⟨T', hT'⟩ := exists_sylow_le_projectivePreimage T H
      (model_sylow_le_product e)
    have hb := hgeom F hF T' (projectivePreimage H) (projectivePreimage_solvable H)
      hT' (projectivePreimage_nonabelian_three_subgroup H
        (model_nonabelian_three_subgroup h hc e))
    obtain ⟨a, ha⟩ := exists_projective_map_le_of_invariant_basis H hb
    refine Or.inr ⟨F, inferInstance, inferInstance, hF, e.trans a, ?_⟩
    rw [Subgroup.map_map] at ha
    exact ha

/-- Conditional assembly through a genuine relatively normal abelian subgroup.
The second step can be proved independently with that subgroup as input;
the final theorem below discharges both steps. -/
theorem monomialPlacement_of_abelian_normal_and_basis {p : ℕ}
    (h : PairInput S R) (hc : Nat.card R = 27) (hmodel : LinearThreeModel p Q)
    (hnormal : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 SL(3,F)) (H : Subgroup SL(3,F)), Group.IsSolvable H →
        (T : Subgroup _) ≤ H →
        (∃ U : Subgroup SL(3,F), U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasNoncentralAbelianNormal H)
    (hbasis : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 SL(3,F)) (H : Subgroup SL(3,F)), Group.IsSolvable H →
        (T : Subgroup _) ≤ H →
        (∃ U : Subgroup SL(3,F), U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasNoncentralAbelianNormal H → HasInvariantBasis H) :
    MonomialPlacement p (R ⊔ (S : Subgroup Q)) := by
  apply monomialPlacement_of_linear_geometry h hc hmodel
  intro F _ _ hF T H hs hT hU
  exact hbasis F hF T H hs hT hU (hnormal F hF T H hs hT hU)

/-- The extraspecial split pair admits an actual SL₃ or PSL₃ model equivalence
carrying its product into the concrete split monomial subgroup. The projective
case uses the full inverse image, including its central kernel. -/
theorem monomialPlacement_of_extraspecial
    (h : PairInput S R) (hc : Nat.card R = 27) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hp3 : 3 < p) (hpmod : p % 3 = 1)
    (hmodel : LinearThreeModel p Q) :
    MonomialPlacement p (R ⊔ (S : Subgroup Q)) := by
  apply monomialPlacement_of_abelian_normal_and_basis h hc hmodel
  · intro F _ _ hF T H hs hT hU
    exact hasNoncentralAbelianNormal_of_solvable_sylow hp hpodd hp3 hpmod
      hF T H hs hT hU
  · intro F _ _ hF T H hs hT hU hA
    exact hasInvariantBasis_of_noncentralAbelianNormal hp hpodd hp3 hpmod
      hF T H hs hT hU hA

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.Extraspecial
