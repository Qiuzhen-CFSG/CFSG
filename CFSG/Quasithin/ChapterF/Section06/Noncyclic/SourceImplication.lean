module

public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.OddNormalImage
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeClass
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ActionKernel
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ContainedAction
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.OuterAction
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.MarkedRecognition

/-!
# The conditional source implication F.6.16

In the three-group branch, the actual cross-core involutions invert the
marked cubic generators. The precise A.1.31(1) implication on the SQTK
cover and coprime fixed-point lifting discharge all quotient fixed-point
bounds. The marked lower-central-series argument gives class at most two,
and A.1.24 supplies actual elementary-nine or Heisenberg residual models.

For the other branch, construct an actual supercritical subgroup and its
literal Frattini representation in GL₂(3). The full F.6.13 implication
settles containment of a local residual. Otherwise the rank-two outer-action
argument makes both local images nontrivial. The kernel is a three-group,
and the quaternion-core preimage contradiction forces the entire residual
to be a three-group. The marked recognition then reconstructs G, including
the actual residual lines and the action of its Sylow four-group.

`source_lemma_F_6_16_of_inputs` proves both source conclusions with precisely
two earlier-source parameters: the complete F.6.13 implication
`GoldschmidtRigidityInput`, and A.1.31(1)'s complete cyclic-centralizer
implication `SectionCentralizerInput`. A.1.24 and the supercritical facts
used from A.1.25 are proved imports. No three-group, model, action, or
branch-exclusion premise remains. The marked companion retains the
compatible actions, not just the ambient group isomorphism.

The unconditional source theorem and discharge of the two universal
parameters belong to `qt-f06-noncyclic` and the original source owners
`qt-f06-rigidity` and `qt-a-01-section-rank`. The class K remains explicit;
the argument only uses the strongly quasithin part of the SQTK cover.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.16, printed pp.308–309 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The noncyclic three-core and rank bound construct the supercritical
witness internally. The only earlier-source premise is complete F.6.13. -/
theorem residual_isThreeGroup_of_rank_two
    (rigidity : GoldschmidtRigidityInput.{u})
    (h : IsGoldschmidtTriple G₁ G₂) (hprime : pPrimeCore 3 G = ⊥)
    (hr : primeRank 3 G ≤ 2) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) := by
  obtain ⟨X, hX, _, hm⟩ := exists_three_core_supercritical hr hn
  exact residual_isThreeGroup_of_supercritical_models rigidity h
    (twoCore_eq_bot_of_primeToThreeCore_eq_bot hprime) hprime hr X hX hm

variable {Ghat : Type u} [Group Ghat] [Finite Ghat] {K : GroupClass.{u}}

/-- The original SQTK cover supplies every rank and core hypothesis needed
to prove that the two-residual is a three-group. -/
theorem residual_isThreeGroup_of_cover
    (rigidity : GoldschmidtRigidityInput.{u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) :=
  residual_isThreeGroup_of_rank_two rigidity h
    (primeToThreeCore_eq_bot_of_quotient e) (three_rank_le_two_of_cover hhat e) hn

/-- The native F.6.16 implication, conditional only on the stated earlier
source results. The last alternative is the fixed Heisenberg semidirect
product whose two distinguished involutions act by `(a,-b,-c)` and
`(-a,b,-c)`, rather than an unspecified extraspecial extension. -/
theorem source_lemma_F_6_16_of_inputs
    (rigidity : GoldschmidtRigidityInput.{u})
    (centralizers : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) ∧
      ((Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2)) ∧
        (pCore 2 G₁).map G₁.subtype = ⊥ ∧ (pCore 2 G₂).map G₂.subtype = ⊥) ∨
      Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      Nonempty (G ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  have hL := residual_isThreeGroup_of_cover rigidity hhat e h hn
  exact ⟨hL, MarkedRecognition.three_group_alternatives_of_cover
    centralizers hhat e h hL hn⟩

/-- In the four-group case, the same original hypotheses construct marked
coordinates for the residual, the full complement, and the ambient group.
Their compatibility is exactly `MarkedModel.equivariant`, together with
the two literal inclusion identities and both marked residual lines. -/
theorem source_marked_models_of_inputs
    (rigidity : GoldschmidtRigidityInput.{u})
    (centralizers : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ MarkedCubicRecognition.Nine
      MarkedCubicRecognition.nineAction
      (MonoidHom.inl MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range
      (MonoidHom.inr MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range) ∨
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ (HeisenbergPrime 3)
      MarkedCubicRecognition.heisenbergAction
      MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range) :=
  MarkedRecognition.marked_models_of_cover centralizers hhat e h
    (residual_isThreeGroup_of_cover rigidity hhat e h hn) hn hnot

end CFSG.Quasithin.ChapterF.Noncyclic
