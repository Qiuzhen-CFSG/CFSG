module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison.Proper
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison.Full
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison.Symmetry

/-!
# Tightly embedded Sylow comparison

Write `S₀ = S ∩ Kᵍ` and `S₁ = N_{S₀}(R)`. The full-normalizer branch
identifies `S₀` with `R` through an invariant Sylow extension and I.7.3.
The proper branch embeds a distinct conjugate of `R` into `S₁`, giving
`|R| ≤ |S₁|`. Together these discharge the universal lower-bound premise
of the symmetric comparison: `|S₁| = |R|`, and `S₁` is the exact ambient
image of a Sylow 2-subgroup of `Kᵍ ∩ N_G(K)`.

Equal orders make the proper-branch embedding an actual factor isomorphism.
The opposite projection proves that `R` is abelian when `S₁ < S₀`.
Thus all conclusions of I.7.7(2--4) follow from the source setup alone.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.7, printed p.427 (PDF p.438).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
include h

private theorem card_le_factor :
    Nat.card R ≤ Nat.card ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) := by
  by_cases hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) =
      S ⊓ conjSubgroup K g
  · rw [hfull]
    exact (h.card_eq_of_full hfull).symm.le
  · exact h.card_le_of_proper (lt_iff_le_and_ne.mpr ⟨inf_le_left, hfull⟩)

/-- Symmetric Sylow comparison gives equal orders of the two normalizer factors. -/
theorem factor_card_eq :
    Nat.card ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) = Nat.card R :=
  (symmetric_comparison (fun _ _ _ _ h' => h'.card_le_factor) h).1

/-- The first factor is the exact ambient image of a Sylow subgroup of the
opposite normalizer, with no additional order or conjugacy assumptions. -/
theorem factor_sylow :
    ∃ P : Sylow 2 ↥(conjSubgroup K g ⊓ normalizer (K : Set G)),
      (P : Subgroup _).map (conjSubgroup K g ⊓ normalizer (K : Set G)).subtype =
        (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) :=
  (symmetric_comparison (fun _ _ _ _ h' => h'.card_le_factor) h).2

/-- The two normalizer factors are isomorphic in both source branches. -/
theorem factor_equiv :
    Nonempty (↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) := by
  by_cases hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) =
      S ⊓ conjSubgroup K g
  · rw [hfull]
    exact h.equiv_of_full hfull
  · exact h.equiv_of_proper_of_card_eq
      (lt_iff_le_and_ne.mpr ⟨inf_le_left, hfull⟩) h.factor_card_eq

end TightNormalizerSetup

/-- I.7.7(2): the first normalizer factor is isomorphic to `R`. -/
theorem lemma_I_7_7_2 {K : Subgroup G} {g : G} {R S : Subgroup G}
    (h : TightNormalizerSetup K g R S) :
    Nonempty (↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) :=
  h.factor_equiv

/-- I.7.7(3): the first normalizer factor is Sylow in `N_{Kᵍ}(K)`,
expressed by an actual Sylow subgroup with exactly that ambient image. -/
theorem lemma_I_7_7_3 {K : Subgroup G} {g : G} {R S : Subgroup G}
    (h : TightNormalizerSetup K g R S) :
    ∃ P : Sylow 2 ↥(conjSubgroup K g ⊓ normalizer (K : Set G)),
      (P : Subgroup _).map (conjSubgroup K g ⊓ normalizer (K : Set G)).subtype =
        (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := h.factor_sylow

/-- I.7.7(4): a proper first normalizer factor forces `R` to be abelian. -/
theorem lemma_I_7_7_4 {K : Subgroup G} {g : G} {R S : Subgroup G}
    (h : TightNormalizerSetup K g R S)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    IsMulCommutative R := h.commutative_of_proper hp

end CFSG.Quasithin.ChapterI.Section06To08
