module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.Frames
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.Lifting
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.SylowBound
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.SolvableFrames
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.OrthogonalFrames

/-!
# Monomial placement of extraspecial unitary pairs

The solvable product RS, and its full preimage in the projective case, have
only two and three as prime divisors and contain a nonabelian three-subgroup.
They also contain a full ambient Sylow two-subgroup, of order greater than
eight. Thus the small-Sylow alternative of the solvable representation
argument is excluded. An invariant orthogonal frame then gives the actual
special or projective monomial placement by a change of coordinates.

The conditional assembly remains available as
`monomialPlacement_of_representation_steps`. The final theorem
`monomialPlacement_of_extraspecial` discharges both representation premises
using the solvable frame dichotomy and orthogonalization over the original
quadratic field. It supplies an actual equivalence to an identity-Gram model
with the required monomial containment.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), and GLS3, proof of Theorem 6.5.3(a)–(d), especially (6.5.1).
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial

universe u v

namespace Placement

variable (p : ℕ)
    (hframes : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup, Group.IsSolvable H →
        (∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3) →
        (∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasFrame H ∨ ∀ T : Sylow 2 H, Nat.card T ≤ 8)
    (horthogonal : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup,
        (∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasFrame H → HasOrthogonalFrame H)

include hframes horthogonal

/-- The full ambient Sylow subgroup excludes the small-order alternative. -/
theorem orthogonalFrame_of_representation_steps
    (hp : p.Prime) (ho : Odd p)
    (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (H : Subgroup J.specialSubgroup) (hH : Group.IsSolvable H)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3)
    (hU : ∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (T : Sylow 2 J.specialSubgroup) (hTH : (T : Subgroup _) ≤ H) :
    HasOrthogonalFrame H := by
  apply horthogonal E J hE hc H hU
  rcases hframes E J hE hc H hH hprimes hU with hframe | hsmall
  · exact hframe
  · have hsmallT := hsmall (T.subtype hTH)
    have he : Nat.card (T.subtype hTH) = Nat.card T :=
      Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv
    rw [he] at hsmallT
    exact ((eight_lt_special_sylow_card J p hp ho hE hc T).not_ge hsmallT).elim

end Placement

open Placement

variable {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

/-- Solvability of RS is preserved by an actual model equivalence. -/
theorem model_product_solvable {G : Type v} [Group G]
    (h : PairInput S R) (e : Q ≃* G) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) := by
  let _ := EvenRankTwo.product_solvable h
  exact Group.isSolvable_of_surjective
    (f := (e.subgroupMap (R ⊔ (S : Subgroup Q))).toMonoidHom)
    (e.subgroupMap (R ⊔ (S : Subgroup Q))).surjective

/-- The model image of RS has no prime divisors other than two and three. -/
theorem model_product_prime_divisors {G : Type v} [Group G]
    (h : PairInput S R) (e : Q ≃* G) {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom)) :
    r = 2 ∨ r = 3 := by
  rw [card_map_of_injective e.injective] at hd
  exact EvenRankTwo.product_prime_divisors h hr hd

/-- Conditional assembly for both actual models, retaining the projective scalar kernel. -/
theorem monomialPlacement_of_representation_steps
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hframes : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup, Group.IsSolvable H →
        (∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3) →
        (∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasFrame H ∨ ∀ T : Sylow 2 H, Nat.card T ≤ 8)
    (horthogonal : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup,
        (∃ U : Subgroup J.specialSubgroup, U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) →
        HasFrame H → HasOrthogonalFrame H)
    (h : PairInput S R) (hc : Nat.card R = 27) (hmodel : Model p Q) :
    MonomialPlacement p (R ⊔ (S : Subgroup Q)) := by
  rcases hmodel with ⟨E, _, _, J, hE, hconj, ⟨e⟩⟩ | ⟨E, _, _, J, hE, hconj, ⟨e⟩⟩
  · obtain ⟨C, hC, hframe⟩ := orthogonalFrame_of_representation_steps p hframes horthogonal
      hp ho E J hE hconj _ (model_product_solvable h e)
      (fun _ hr hd => model_product_prime_divisors h e hr hd)
      (model_nonabelian_three_subgroup h hc e)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) (model_sylow_le_product e)
    have hC' : J.conjTranspose C.val * J.form * C.val = (identityGram J).form := by
      simpa only [identityGram_form] using hC
    refine Or.inl ⟨E, inferInstance, inferInstance, identityGram J, hE, hconj,
      identityGram_form J, e.trans (specialEquiv J C hC'), ?_⟩
    change (R ⊔ (S : Subgroup Q)).map
      ((specialEquiv J C hC').toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact special_map_le_monomial_of_frame _ C hC' hframe
  · let H := (R ⊔ (S : Subgroup Q)).map e.toMonoidHom
    obtain ⟨T, hTH⟩ := projective_preimage_contains_sylow J
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) H (model_sylow_le_product e)
    obtain ⟨C, hC, hframe⟩ := orthogonalFrame_of_representation_steps p hframes horthogonal
      hp ho E J hE hconj (H.comap J.specialToProjective)
      (projective_preimage_solvable J H (model_product_solvable h e))
      (projective_preimage_prime_divisors J H
        (fun _ hr hd => model_product_prime_divisors h e hr hd))
      (projective_preimage_nonabelian_three_subgroup J H (model_nonabelian_three_subgroup h hc e))
      T hTH
    have hC' : J.conjTranspose C.val * J.form * C.val = (identityGram J).form := by
      simpa only [identityGram_form] using hC
    refine Or.inr ⟨E, inferInstance, inferInstance, identityGram J, hE, hconj,
      identityGram_form J, e.trans (projectiveEquiv J C hC'), ?_⟩
    change (R ⊔ (S : Subgroup Q)).map
      ((projectiveEquiv J C hC').toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact projective_map_le_monomial_of_frame H C hC' hframe

/-- The extraspecial pair lies in a concrete orthogonal monomial subgroup
after an actual special or projective unitary change of model. -/
theorem monomialPlacement_of_extraspecial
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    (h : PairInput S R) (hc : Nat.card R = 27) (hmodel : Model p Q) :
    MonomialPlacement p (R ⊔ (S : Subgroup Q)) := by
  apply monomialPlacement_of_representation_steps p hp ho ?_ ?_ h hc hmodel
  · intro E _ _ J hE hconj H hH hprimes hU
    exact frame_or_small_sylow hp ho hlarge hmod J hE hconj H hH hprimes hU
  · intro E _ _ J hE hconj H hU hframe
    exact orthogonalFrame_of_frame p hp ho hlarge hmod E J hE hconj H hU hframe

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial
