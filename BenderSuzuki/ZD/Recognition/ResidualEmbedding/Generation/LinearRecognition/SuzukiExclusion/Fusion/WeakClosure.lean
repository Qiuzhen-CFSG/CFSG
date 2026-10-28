module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Cardinality
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.HallAdjustment
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ExceptionalArithmetic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Burnside
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OrderTwo
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.ExceptionalOrder
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer

/-!
# Suzuki complements, the order-two factor and quotient weak closure

The invariant complement of Lemma 14.7 gives the order-two conclusion of
Lemma 14.8. Its missing conjugator explanation is
supplied by actual Sylow conjugacy, product disconnection and solvable Hall
conjugacy. All Suzuki subgroup restrictions are discharged using the
specified embedding of J into L.

Lemma 14.9 uses Ω₁(T) = M°U for the involution-contained branch. In the
other branch, Lemma 14.7 makes the literal image of S in M/M° elementary;
the odd-normalizer argument and Burnside fusion give weak closure. At
q = 8 the actual Suzuki model gives |J| = 14 and |D| dividing 294,
discharging the exceptional Frobenius obstruction.

The concluding theorem proves |U| = 2 and QuotientFusion from the original
context, local geometry, semiregularity, embedding, supplied Sylow geometry
and precisely the allowed earlier Lemma 12.11 premise. The parent source
assembly constructs that premise and the Sylow geometry.

Source: GLS4, Chapter 2, Lemmas 14.7–14.9,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- GLS4, Chapter 2, Lemma 14.9, after Lemma 14.8. Both the
involution-contained and elementary-quotient branches use the literal M/M°.
At q = 8 the actual model embedding proves |J| = 14 and |D| divides 294,
discharging the exceptional Frobenius obstruction. -/
public theorem Context.quotientFusion_of_U_card_two
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) : QuotientFusion d g := by
  by_contra hn
  have he := d.elementaryQuotient_of_involution g s hsemi
    (exists_involution_outside_T_of_not_quotientFusion d g hn)
  apply hn
  apply d.quotientFusion_of_odd_normalizer g hsemi f hf s hU he
  intro hm
  subst m
  exact d.pair_card_dvd_294_of_U_card_two g s f hf hU

/-- The complete conditional output of GLS4, Chapter 2, Lemmas 14.8–14.9.
The only earlier-source premise beyond the supplied Sylow geometry is the
specified Lemma 12.11 involution-fusion statement. The enclosing source
assembly constructs both of those inputs. -/
public theorem Context.U_card_eq_two_and_quotientFusion
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (h12 : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w) :
    Nat.card g.U = 2 ∧ QuotientFusion d g := by
  have hU := d.U_card_eq_two g hsemi f hf s h12
  exact ⟨hU, d.quotientFusion_of_U_card_two g hsemi f hf s hU⟩

end BenderSuzuki.ZD.SuzukiExclusion
