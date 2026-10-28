module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Reduction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Nonradical
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Radical

/-!
# Center recognition from two concrete counting estimates

A central element with nontrivial actor forces H into its square-admissible
commuting set. A noncentral radical element instead forces H into a mixed
candidate set, using any element of H with nontrivial actor. Bounds below 64
exclude both possibilities. The trivial-actor branch is proved directly in
`Center.Reduction`.

The two finite estimates are supplied by the concrete `Nonradical` and
`Radical` branches below. Its literal native application is in
`FixedPairQuartic.ModelRestriction.Recognition.Center`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6a),
printed pp.410 and 412 (PDF pp.421 and 423).
-/

@[expose] public section
open Subgroup
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions

/-- Two finite estimates suffice for the exact center calculation. They concern
explicit subsets of the fixed signed extension, with no subgroup recognition premise. -/
theorem center_eq_centralIn_of_counts
    (hnonrad : ∀ x : SplitExtension, x ^ 2 ∈ sign → x.right ≠ 1 →
      Nat.card (squareCommutants x) < 64)
    (hrad : ∀ (m : Model) (x : SplitExtension), m ∉ center Model →
      x ^ 2 ∈ sign → x.right ≠ 1 → Commute (radicalEmbedding m) x →
      Nat.card (mixedCandidates m x) < 64)
    (H : Subgroup SplitExtension) (hcard : Nat.card H = 64)
    (hsq : ∀ x ∈ H, x ^ 2 ∈ sign) :
    center H = centralIn H := by
  classical
  by_cases hact : ∀ x ∈ H, x.right = 1
  · exact center_eq_centralIn_of_actor_trivial H hcard hact
  push Not at hact
  obtain ⟨x, hx, hxr⟩ := hact
  apply le_antisymm ?_ (centralIn_le_center H)
  intro z hz
  have hc (y : SplitExtension) (hy : y ∈ H) : Commute z.val y := by
    exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)).symm
  have hzr : z.val.right = 1 := by
    by_contra hn
    have hlo := card_le_squareCommutants H hsq z.val hc
    have hhi := hnonrad z.val (hsq z.val z.property) hn
    omega
  have hzE : radicalEmbedding z.val.left = z.val := SemidirectProduct.ext rfl hzr.symm
  have hm : z.val.left ∈ center Model := by
    by_contra hn
    have hcm (y : SplitExtension) (hy : y ∈ H) :
        Commute (radicalEmbedding z.val.left) y := hzE.symm ▸ hc y hy
    have hlo := card_le_mixedCandidates H hsq z.val.left x hx hcm
    have hhi := hrad z.val.left x hn (hsq x hx) hxr (hcm x hx)
    omega
  exact ⟨z.val.left, hm, hzE⟩

/-- The center of every order-64 square-admissible restriction is its
distinguished central layer. -/
theorem center_eq_centralIn
    (H : Subgroup SplitExtension) (_hZ : central ≤ H)
    (hcard : Nat.card H = 64)
    (hsq : ∀ x ∈ H, x ^ 2 ∈ sign) :
    center H = centralIn H :=
  center_eq_centralIn_of_counts squareCommutants_card_lt
    mixedCandidates_card_lt H hcard hsq

end EvenCliffordSix.SplitExtension.ElementaryRestrictions
