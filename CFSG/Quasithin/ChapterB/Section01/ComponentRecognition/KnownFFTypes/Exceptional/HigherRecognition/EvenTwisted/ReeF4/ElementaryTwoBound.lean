module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.ReeF4
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound

/-!
# Applying the Ree root calculation to the Chapter B elementary-rank bound

The lower-layer source assembly supplies exactly the `horder` premise of
`elementary_rank_le_of_model_bound`. That existing theorem retains the actual
central quotient and proves order preservation using the faithful irreducible
characteristic-two representation. Thus no new assumption about central
kernels or placement in the original component is introduced here.

The literal replacement and root calculations now prove that order premise.
The theorem `elementary_rank_le` has no additional root-calculation hypotheses;
the earlier conditional interface is retained. The parent Ree exclusion
separately owns the involution representation estimate.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Table 13 and
Lemma 8.8, internal pp.53,57–58; GLS3 Lemma 3.3.9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
universe u v

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H)
  [N.Normal] [IsQuasisimple N]

/-- The exact Chapter B consumer of the two independent GLS3 root calculations.
Placement in N and injectivity through its actual central quotient are inherited
from `elementary_rank_le_of_model_bound`. -/
theorem elementary_rank_le_of_root_calculations {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    (hreplace : ∀ E : Subgroup (_root_.ReeF4.Model m),
      E ≤ _root_.ReeF4.Parabolics.unipotent m → IsElementaryAbelian 2 E →
      ∃ F : Subgroup (_root_.ReeF4.Model m),
        F ≤ _root_.ReeF4.ElementaryTwoBound.D m ∧ IsElementaryAbelian 2 F ∧
          Nat.card E ≤ Nat.card F)
    (hroot : _root_.ReeF4.ElementaryTwoBound.RootCalculationFacts m)
    {E W : Type v} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) [IsIrreducible (σ.comp N.subtype)]
    (hf : Function.Injective σ) (A : Subgroup H) [IsElementaryAbelian 2 A] :
    rank A ≤ 5 * (2 * m + 1) :=
  elementary_rank_le_of_model_bound N hm hF e
    (_root_.ReeF4.ElementaryTwoBound.card_le_of_root_calculations hm hreplace hroot)
    σ hf A

/-- The sharp elementary-rank bound for the original ambient group, using the
proved order bound on its actual Ree central quotient. -/
theorem elementary_rank_le {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    {E W : Type v} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) [IsIrreducible (σ.comp N.subtype)]
    (hf : Function.Injective σ) (A : Subgroup H) [IsElementaryAbelian 2 A] :
    rank A ≤ 5 * (2 * m + 1) :=
  elementary_rank_le_of_model_bound N hm hF e
    (_root_.ReeF4.ElementaryTwoBound.card_le m hm) σ hf A

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
