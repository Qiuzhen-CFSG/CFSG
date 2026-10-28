module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Actions
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness

/-!
# The natural-module alternative of Hypothesis 12.8.1

The input retains the actual chosen Irr⁺ member, the dimension, the three
global exclusions, and an equivariant identification of the natural module
for the literal quotient L/O₂(L). These are original source assumptions.
The natural marking used by the existing local proofs is constructed from
that quotient equivalence and those coordinates. No flag or local conclusion
is part of the input.

The rank-two alternative is the existing `RankTwoHypothesis`; its S₃ action
is an action of LT and must not be replaced by a full natural action of L.
The three universal earlier implications are independent inputs to the
conditional construction. The Section 12.8 owner must discharge them using
the full earlier source results.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Hypothesis 12.8.1, printed p.849, and Theorem 1.2.7, printed p.506.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08
open Section02 InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conjugation on the actual ambient seed; this action does not require a flag. -/
def setupSeedAction (J V : Subgroup G) (hJV : J ≤ normalizer (V : Set G)) :
    J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJV)

/-- Exactly the higher-rank alternative, with natural coordinates for the
original L-action on the original V. -/
structure HigherRankHypothesis (K : GroupClass.{u})
    (T : Sylow 2 G) (L V : Subgroup G) (n : ℕ) where
  source : Hypothesis1223 K T L
  chosen : ChosenModule T L V
  rank : 3 ≤ n ∧ n ≤ 5
  quotient_model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2
  natural : letI := chosen.elementary
    ∃ (e : (L ⧸ pCore 2 L) ≃* BinaryLinear.OuterCyclic.LinearGroup n)
      (c : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2)),
      ∀ (l : L) (v : Additive V),
        c (Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
          (mem_normalizer_iff.mp (chosen.normalizes l.property) v.toMul).mp
            v.toMul.property⟩) = e (QuotientGroup.mk' (pCore 2 L) l) (c v)
  no_nextLinear : ¬ ClassicalGroup.IsPSL G (n + 1) 2
  no_A9 : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_M24 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M24)

/-- The genuine universal 1.2.7 implication, retaining its complete output. -/
def Uniqueness127 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSimpleQTKE K X →
    ∀ (T : Sylow 2 X) (L : Subgroup X), L ∈ Chapter1.LStar X (T : Subgroup X) →
      Chapter1.Section02.NonsolvableUniquenessConclusion T L

/-- The three earlier universal implications used by the higher-rank setup.
They concern all source inputs, not conclusions for a chosen Section 12.8 flag. -/
structure EarlierSetupResults (K : GroupClass.{u}) : Prop where
  structural : Structural1222 K
  uniqueness : Uniqueness127 K
  alternatives : Theorem12213 K

namespace HigherRankHypothesis
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
variable (h : HigherRankHypothesis K T L V n)

/-- Construct the marking consumed by NormalL1 and LocalKernel from the
source's quotient equivalence and pointwise natural-module coordinates. -/
noncomputable def naturalMarking : letI := h.chosen.elementary
    AmbientNaturalMarking L h.chosen.normalizes n := by
  letI := h.chosen.elementary
  exact ⟨Classical.choose h.natural,
    Classical.choose (Classical.choose_spec h.natural),
    Classical.choose_spec (Classical.choose_spec h.natural)⟩

/-- Faithful membership already includes O²(L)=L. -/
theorem residual (h : HigherRankHypothesis K T L V n) : pResidual 2 L = ⊤ :=
  (pResidual_eq_top_iff 2 L).mpr h.source.maximal_faithful.2.1.2.1

end HigherRankHypothesis
end CFSG.Quasithin.Chapter12.Section08
