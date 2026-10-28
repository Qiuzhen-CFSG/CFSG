module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Construction
public import Theory.Quasithin.CentralThreeLocalRank

/-!
# Local elementary lifts in central three-covers of J₃

The perfect supports in `ThreeCoverLocalConfiguration` split through every
finite central three-extension. Perfect centralizer lifting makes their two
chosen cyclic factors commute. The normalizer-preserving coprime lift of the
nontrivial two-subgroup then gives the required local E₉, with injective
projection through the literal quotient by the ambient center.

The rank theorems apply `CentralThreeLocalRank` with that exact quotient map.
The nontrivial-center hypothesis supplies the additional independent central
three-element. No quasisimplicity hypothesis is needed for the transfer itself.

The final three theorems discharge the configuration premise using the checked
affine construction in the actual degree-6156 model: its marked E₉ normalizes
a nontrivial elementary two-subgroup, and its two perfect supports have orders
1920 and 60. Thus every nontrivial central three-cover has two-local three-rank
at least three and is not quasithin. The ordinary-rank argument of I.2.1 alone
does not give this local conclusion.

Source: Aschbacher--Smith, A.2.19, printed p.41, and I.2.1, printed p.409;
GLS, Number 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3
open Subgroup

/-- Construct the local E₉ lift from the specified concrete model configuration.
The center need not be nontrivial for this lifting statement. -/
public theorem exists_local_e9_lift_of_configuration
    (d : ThreeCoverLocalConfiguration)
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (center G)) (e : (G ⧸ center G) ≃* Model) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
        Function.Injective ((QuotientGroup.mk' (center G)).comp f) ∧
        ∀ a, f a ∈ normalizer (Q : Set G) := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center G := by
    ext x
    change e (QuotientGroup.mk' (center G) x) = 1 ↔ x ∈ center G
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hz : π.ker ≤ center G := hker.le
  have hp : IsPGroup 3 π.ker := hker.symm ▸ hZ
  let : Group.IsPerfect d.leftSupport := d.left_perfect
  let : Group.IsPerfect d.rightSupport := d.right_perfect
  obtain ⟨Q, F, hQne, hQ, hF, hn⟩ :=
    π.exists_local_product_lift_of_perfect_cyclicSylow_subgroups
      (p := 3) (q := 2) (by decide) hπ hz hp d.leftSupport d.rightSupport
      d.left_cyclicSylow d.right_cyclicSylow d.plane d.left_mem d.right_mem
      d.left_centralizes d.twoSubgroup d.two_isPGroup d.two_nontrivial d.normalizes
  let r := MulEquiv.prodMultiplicative (ZMod 3) (ZMod 3)
  let f := F.comp r.toMonoidHom
  refine ⟨Q, f, hQne, hQ, ?_, fun a => hn (r a)⟩
  intro a b hab
  apply r.injective
  apply d.plane_injective
  have he := congrArg e hab
  change π (F (r a)) = π (F (r b)) at he
  change (π.comp F) (r a) = (π.comp F) (r b) at he
  simpa only [hF] using he

/-- A nontrivial three-group center supplies the third local rank.
This uses the actual J₃ quotient equivalence, without a rank premise. -/
public theorem three_le_twoLocalPrimeRank_of_configuration
    (d : ThreeCoverLocalConfiguration)
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (center G)) (hZne : center G ≠ ⊥)
    (e : (G ⧸ center G) ≃* Model) : 3 ≤ twoLocalPrimeRank 3 G := by
  obtain ⟨Q, f, hQne, hQ, hf, hn⟩ := exists_local_e9_lift_of_configuration d hZ e
  apply Theory.Quasithin.three_le_twoLocalPrimeRank_of_injective_central_projection
    hZ hZne Q hQ hQne f hf hn
  · intro a
    change (3 • a.toAdd) = 0
    apply Prod.ext <;> change 3 • (_ : ZMod 3) = 0 <;>
      simp only [nsmul_eq_mul] <;> exact zero_mul _
  · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
    norm_num [Nat.card_zmod]

/-- Every nontrivial central three-cover of the actual J₃ model has a local E₉
whose projection through the literal quotient by its center is injective.
The center's nontriviality is retained for the rank-three application below. -/
public theorem exists_three_cover_local_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (center G)) (_hZne : center G ≠ ⊥)
    (e : (G ⧸ center G) ≃* Model) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
        Function.Injective ((QuotientGroup.mk' (center G)).comp f) ∧
        ∀ a, f a ∈ normalizer (Q : Set G) :=
  exists_local_e9_lift_of_configuration ThreeCoverConfig.configuration hZ e

/-- The J₃ three-cover obstruction used in A.2.19: the concrete local E₉ and
a central cubic element give two-local three-rank at least three. -/
public theorem three_le_twoLocalPrimeRank
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (center G)) (hZne : center G ≠ ⊥)
    (e : (G ⧸ center G) ≃* Model) : 3 ≤ twoLocalPrimeRank 3 G :=
  three_le_twoLocalPrimeRank_of_configuration ThreeCoverConfig.configuration hZ hZne e

/-- A cover of the actual J₃ model with nontrivial three-group center is not
quasithin. The nontrivial-center hypothesis excludes simple J₃. -/
public theorem not_quasithin_of_nontrivial_three_center
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (center G)) (hZne : center G ≠ ⊥)
    (e : (G ⧸ center G) ≃* Model) : ¬ IsQuasithin G := by
  intro h
  have hle := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hge := three_le_twoLocalPrimeRank hZ hZne e
  omega

end Sporadic.Janko3
