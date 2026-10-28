module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore

/-!
# The monomial route for extraspecial odd unitary pairs

The actual monomial placement and the two concrete core calculations imply
that O₃(RS) ∩ R has order nine. This is a proper subgroup not contained in
Φ(R), invariant under every automorphism preserving the pair, so the pair is
reducible. The argument applies separately to actual SU₃ and PSU₃ models.

The final theorems discharge the monomial placement and both model core
calculations. For an arbitrary quasisimple central cover, `reducible` retains
only `PrimeCover`, the universal earlier input from I.1.3 allowed by this
branch's contract. No local placement or action assumption remains. The
projective argument retains the central scalar kernel throughout.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528);
GLS3, proof of Theorem 6.5.3(a)–(d), `refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial

universe u
variable {Q : Type u} [Group Q] [Finite Q]
variable (p : ℕ)

section ConditionalCalculations

variable
    (hspecial : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) → J.form = 1 →
      ∀ (T : Sylow 2 J.specialSubgroup) (H : Subgroup J.specialSubgroup),
        (T : Subgroup J.specialSubgroup) ≤ H →
        H ≤ HermitianForm.OddThreeLocal.Monomial.special J →
        Nat.card H = 27 * Nat.card T →
        (∃ U : Subgroup J.specialSubgroup,
          U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        Nat.card (pCore 3 H) = 9)
    (hprojective : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) → J.form = 1 →
      ∀ (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
        (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ H →
        H ≤ HermitianForm.OddThreeLocal.Monomial.projective J →
        Nat.card H = 27 * Nat.card T →
        (∃ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
          U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        Nat.card (pCore 3 H) = 9)

include hspecial hprojective

/-- Conditional assembly from actual placement and model core calculations. -/
theorem local_core_nine_of_monomial_calculations
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    (hm : MonomialPlacement p (R ⊔ (S : Subgroup Q))) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  rcases hm with ⟨E, _, _, J, hE, hconj, hJ, e, hle⟩ |
    ⟨E, _, _, J, hE, hconj, hJ, e, hle⟩
  · rw [local_core_intersection_card_of_equiv h e]
    exact hspecial E J hE hconj hJ _ _ (model_sylow_le_product e) hle
      (model_product_card h hc e) (model_nonabelian_three_subgroup h hc e)
  · rw [local_core_intersection_card_of_equiv h e]
    exact hprojective E J hE hconj hJ _ _ (model_sylow_le_product e) hle
      (model_product_card h hc e) (model_nonabelian_three_subgroup h hc e)

/-- Conditional assembly from the two local computations
and placement. The cover premise is universal and contains no local exclusion. -/
theorem reducible_of_monomial_calculations (hcover : PrimeCover.{u})
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p)
    (hplace : Model p Q → MonomialPlacement p (R ⊔ (S : Subgroup Q))) :
    PairReducible (S : Subgroup Q) R := by
  have hmodel := hcover p hp ho hlarge hmod Q h.quasisimple hm
  exact reducible_of_extraspecial_local_core_nine h hc
    (local_core_nine_of_monomial_calculations p hspecial hprojective h hc (hplace hmodel))

end ConditionalCalculations

/-- The actual intersection O₃(RS) ∩ R has order nine in either unitary model.
Both placement and the special/projective core calculations are discharged. -/
theorem local_core_nine_of_model
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    (hm : Model p Q) :
    Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9 := by
  apply local_core_nine_of_monomial_calculations p ?_ ?_ h hc
    (monomialPlacement_of_extraspecial p hp ho hlarge hmod h hc hm)
  · intro E _ _ J hE hconj hJ T H hTH hHM hcard hU
    exact HermitianForm.OddThreeLocal.Monomial.special_core_card_nine
      J hp ho hlarge hmod hE hconj hJ T H hTH hHM hcard hU
  · intro E _ _ J hE hconj hJ T H hTH hHM hcard hU
    exact HermitianForm.OddThreeLocal.Monomial.projective_core_card_nine
      J hp ho hlarge hmod hE hconj hJ T H hTH hHM hcard hU

/-- Extraspecial complements give reducible pair automizers in both actual
SU₃ and PSU₃ models, with no additional local hypothesis. -/
theorem reducible_of_model
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    (hm : Model p Q) : PairReducible (S : Subgroup Q) R :=
  reducible_of_extraspecial_local_core_nine h hc
    (local_core_nine_of_model p hp ho hlarge hmod h hc hm)

/-- The extraspecial branch for every quasisimple central cover of PSU₃(p).
Only the universal earlier cover theorem remains an explicit input. -/
theorem reducible (hcover : PrimeCover.{u})
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (hc : Nat.card R = 27)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R :=
  reducible_of_model p hp ho hlarge hmod h hc
    (hcover p hp ho hlarge hmod Q h.quasisimple hm)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial
