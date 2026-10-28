module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairSylow

/-!
# The exact binary unitary-four boundary for the Hall Sylow argument

A Sylow two-subgroup of PSU₄(2ᵃ) has Frattini quotient of order 2^(3a).
Thus the original pair's seven-generator inner-action test applies precisely
when a is one or two. The source consumer proves inner action for these two
rows on the unchanged residual and normal component. The larger exponents
require a structural restriction on the Sylow automorphism image.

Source: Aschbacher--Smith 4.4.10, printed p.621, and the unitary Sylow
coordinates in F.1.12(I)(6), printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped Pointwise
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

/-- The exact Sylow Frattini order on the literal source model. -/
theorem binary_unitary_four_sylow_frattini_card
    {S : Type*} [Group S] [Finite S] {a : ℕ} (ha : 0 < a)
    (hm : ClassicalGroup.IsPSU S 4 (2 ^ a)) (P : Sylow 2 S) :
    Nat.card (P ⧸ frattini P) = 2 ^ (3 * a) := by
  obtain ⟨F, hF, hFfin, J, hcard, hconj, ⟨j⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S j.toEquiv
  let P' := P.mapSurjective (f := j.toMonoidHom) j.surjective
  rw [SylowFrattiniBounds.card_congr (P.equivMapOfInjective j.toMonoidHom j.injective)]
  exact UnitaryFourSylow.FrattiniExact.projective_frattini_card F J ha hcard hconj P'

/-- The size premise of the existing pair-Sylow theorem holds exactly for
the two small unitary-four rows. -/
theorem binary_unitary_four_sylow_frattini_card_le_128_iff
    {S : Type*} [Group S] [Finite S] {a : ℕ} (ha : 0 < a)
    (hm : ClassicalGroup.IsPSU S 4 (2 ^ a)) (P : Sylow 2 S) :
    Nat.card (P ⧸ frattini P) ≤ 128 ↔ a ≤ 2 := by
  rw [binary_unitary_four_sylow_frattini_card ha hm P]
  change 2 ^ (3 * a) ≤ 2 ^ 7 ↔ _
  rw [Nat.pow_le_pow_iff_right (by decide)]
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The actual Hall residual acts innerly on both small binary unitary-four
rows, using the exact root-coordinate Frattini calculation. -/
theorem source_a5_oddNormalizer_inner_of_binary_unitary_four_small
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    {a : ℕ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ a)) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  exact source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
    ((binary_unitary_four_sylow_frattini_card_le_128_iff ha hm P).mpr ha2)

end CFSG.Quasithin.Chapter10
