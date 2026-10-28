module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.FrattiniGeneration
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.CanonicalRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.LiftFamily
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.CanonicalFactors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.OffenderReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.Faithfulness
public import Theory.GroupTheory.QuasithinBasic

/-!
# Assembly of the canonical five-primary factors

For a faithful action on the literal quotient UH/V₁, consider the canonical
order-five subgroups of F(H*) contained in P*, with moved support of order
sixteen. D.2.12 gives their mutual commutation and independence, including
independence of their actual supports. Their product embeds into P*, so
the source bound m₅(H) ≤ 2 limits the number of factors to two. The lift
P* → P then gives the required factors in the supplied P.

The second assembly theorem reduces generation to containment of
[P*,Vα*] in the canonical subgroup. Coprime action and the irreducibility
already in `ReducedFive` discharge the generation step. In particular,
no small-order shape for P is an additional hypothesis.

`factorization_of_critical_pair` now constructs the factorization from the
actual source Q-member Uγ* and its conjugate-core placement in 13.8.8(2).
The universal D.2.13(1–2) implication remains an explicit earlier-source input.
It supplies a single canonical commutator with a two-actor moving P*;
normality of the canonical family and Frattini irreducibility then prove
canonical generation. Thus the factor-only conclusion has a direct D.2.13
route, without needing the additional indecomposable reduction of D.2.17.
No local canonical-generation or commutator-containment hypothesis remains
in that source application. The subsequent actor and rank-one calculations
remain separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.12–13,
printed pp.183–185, and the five-primary paragraph of 13.8.13, p.951.

-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup ChapterD
variable {G : Type*} [Group G] [Finite G]
variable {H UH V₁ L₁ T M Vα : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

/-- A generated canonical family gives all fields of the actual factorization.
The canonical-generation input remains a separate proof obligation. -/
theorem factorization_of_canonical_generation (a : StarAction H UH V₁)
    (hfaith : Function.Injective a.action) (r : ReducedFive H L₁ T M Vα)
    (hrank : primeRank 5 H ≤ 2)
    (hgen : a.canonicalFiveGroup r.P = Source.starImage H r.P) :
    Nonempty (Factorization a r.P) := by
  classical
  let := a.starMulAction
  let := a.starMulAction_faithful hfaith
  let C := a.canonicalFiveFactors r.P
  let : Fintype C := Fintype.ofFinite C
  let e := (Fintype.equivFin C).symm
  let X : Fin (Fintype.card C) → Subgroup (Source.Hstar H) := fun i => (e i).val
  have hXC (i) : X i ∈ a.canonicalFiveFactors r.P := (e i).property
  have hXP (i) : X i ≤ Source.starImage H r.P := (hXC i).1
  have hXS (i) : X i ∈ smallSupportFactors (Source.Hstar H)
      (UH ⧸ V₁.subgroupOf UH) 2 :=
    ((a.canonicalFiveFactors_iff r.P (X i)).mp (hXC i)).2
  have hinj : Function.Injective X := Subtype.val_injective.comp e.injective
  have hpos : 0 < Fintype.card C := by
    apply Nat.pos_of_ne_zero
    intro he
    let : IsEmpty C := Fintype.card_eq_zero_iff.mp he
    have hbot : a.canonicalFiveGroup r.P = ⊥ := by
      rw [a.canonicalFiveGroup_eq_iSup]
      exact iSup_of_empty _
    exact r.star_ne_bot (hgen.symm.trans hbot)
  have hbound : Fintype.card C ≤ 2 := by
    have hn := canonicalFive_count_le_subgroup_rank X hXS hinj
      (Source.starImage H r.P) hXP
    rw [Fintype.card_fin] at hn
    have hrP : primeRank 5 r.P ≤ 2 :=
      (Theory.GroupTheory.primeRank_le_of_injective 5 (inclusion r.P_le)
        (inclusion_injective r.P_le)).trans hrank
    rw [Theory.GroupTheory.primeRank_equiv 5 (fiveStarEquiv r.P_le r.P_isPGroup)] at hrP
    exact hn.trans hrP
  have hXgen : (⨆ i, X i) = Source.starImage H r.P := by
    calc
      (⨆ i, X i) = ⨆ Y : C, Y.val := e.surjective.iSup_comp _
      _ = a.canonicalFiveGroup r.P := (a.canonicalFiveGroup_eq_iSup r.P).symm
      _ = Source.starImage H r.P := hgen
  let f : Fin (Fintype.card C) → smallSupportFactors (Source.Hstar H)
      (UH ⧸ V₁.subgroupOf UH) 2 := fun i => ⟨X i, hXS i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply hinj
    exact congrArg (fun Y : smallSupportFactors (Source.Hstar H)
      (UH ⧸ V₁.subgroupOf UH) 2 => Y.val) he
  have hd := smallSupport_decomposition (G := Source.Hstar H)
    (V := UH ⧸ V₁.subgroupOf UH) (k := 2) (Or.inr rfl)
  refine ⟨{
    count := Fintype.card C
    count_pos := hpos
    count_le_two := hbound
    factor := fun i => liftFiveFactor r.P_le r.P_isPGroup (X i)
    factor_le := fun i => liftFiveFactor_le r.P_le r.P_isPGroup (X i)
    factor_card := ?_
    star_card := ?_
    generated := (liftFiveFactor_iSup r.P_le r.P_isPGroup X hXP hXgen).symm
    commute := ?_
    disjoint := ?_
    support_card := ?_
    support_disjoint := ?_ }⟩
  · intro i
    rw [liftFiveFactor_card r.P_le r.P_isPGroup (X i) (hXP i)]
    exact (hXC i).2.2.1
  · intro i
    rw [starImage_liftFiveFactor r.P_le r.P_isPGroup (X i) (hXP i)]
    exact (hXC i).2.2.1
  · intro i j _
    apply liftFiveFactor_commutator r.P_le r.P_isPGroup (hXP i) (hXP j)
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (smallSupportFactors_commutingFamily (Or.inr rfl) (X i) (hXS i) (X j) (hXS j))
  · intro i j hij
    apply liftFiveFactor_disjoint r.P_le r.P_isPGroup
    exact hd.1.pairwiseDisjoint (i := f i) (j := f j) (fun he => hij (hf he))
  · intro i
    change Nat.card (commutatorAction
      ((Source.starImage H (liftFiveFactor r.P_le r.P_isPGroup (X i))).map a.action)
      (UH ⧸ V₁.subgroupOf UH)) = 16
    rw [starImage_liftFiveFactor r.P_le r.P_isPGroup (X i) (hXP i)]
    exact (hXC i).2.2.2
  · intro i j hij
    change Disjoint (commutatorAction
      ((Source.starImage H (liftFiveFactor r.P_le r.P_isPGroup (X i))).map a.action)
      (UH ⧸ V₁.subgroupOf UH)) (commutatorAction
      ((Source.starImage H (liftFiveFactor r.P_le r.P_isPGroup (X j))).map a.action)
      (UH ⧸ V₁.subgroupOf UH))
    rw [starImage_liftFiveFactor r.P_le r.P_isPGroup (X i) (hXP i),
      starImage_liftFiveFactor r.P_le r.P_isPGroup (X j) (hXP j),
      ← a.star_support_eq, ← a.star_support_eq]
    exact hd.2.2.1.pairwiseDisjoint (i := f i) (j := f j) (fun he => hij (hf he))

/-- Frattini irreducibility reduces factor existence to canonical containment
of the nontrivial commutator with the source two-actor. That containment
must still be constructed by the source offender reduction. -/
theorem factorization_of_canonical_commutator_control (a : StarAction H UH V₁)
    (hfaith : Function.Injective a.action) (r : ReducedFive H L₁ T M Vα)
    (hrank : primeRank 5 H ≤ 2) (hA : IsPGroup 2 (Source.starImage H Vα))
    (hcontrol : ⁅Source.starImage H r.P, Source.starImage H Vα⁆ ≤
      a.canonicalFiveGroup r.P) : Nonempty (Factorization a r.P) := by
  let := r.Pstar_normal
  exact factorization_of_canonical_generation a hfaith r hrank
    (r.normal_eq_of_contains_commutator (a.canonicalFiveGroup r.P)
      (Source.starImage H Vα) (a.canonicalFiveGroup_le r.P) hA r.moved hcontrol)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end

public section
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Three.Supercritical.Offenders ChapterD
universe u
variable {G : Type u} [Group G] [Finite G]
variable {H UH V₁ L₁ T M Vα : Subgroup G}

/-- A source quadratic offender acting faithfully on P* constructs all the
five-factors. The global D.2.13 input is applied inside P*A; normality and
Frattini irreducibility discharge canonical generation in H*. -/
theorem factorization_of_offender [(V₁.subgroupOf UH).Normal]
    [IsElementaryAbelian 2 UH] [Group.IsSolvable H]
    (src : SourceD213PrimeInput.{u}) (a : StarAction H UH V₁)
    (ha : Function.Injective a.action) (r : ReducedFive H L₁ T M Vα)
    (hrank : primeRank 5 H ≤ 2)
    (A : Subgroup (Source.Hstar H)) (hA : A ∈ Q (linearAction a))
    (hf : A ⊓ centralizer (Source.starImage H r.P : Set _) = ⊥) :
    Nonempty (Factorization a r.P) := by
  obtain ⟨B, hB, hm, hD⟩ := exists_canonical_five_commutator src a ha r A hA hf
  let _ := r.Pstar_normal
  exact factorization_of_canonical_generation a ha r hrank
    (r.normal_eq_of_contains_commutator (a.canonicalFiveGroup r.P) B
      (a.canonicalFiveGroup_le r.P) hB hm (le_sSup hD))

/-- The factor existence assertion in the five-primary paragraph of 13.8.13,
conditional on universal D.2.13(1–2) and the genuine earlier source conclusions.
The two actor hypotheses are exactly Q-membership and conjugate-core placement
from 13.8.8(2). Faithfulness of Uγ* on the supplied P* is proved here.
The source minimality has already supplied the Frattini irreducibility in r;
no additional small-order shape, factorization or rank-one premise is used. -/
theorem factorization_of_critical_pair {L V V₃ : Subgroup G}
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.UH H V₃)] [Group.IsSolvable H]
    (src : SourceD213PrimeInput.{u}) (r : ReducedFive H L₁ T M Vα)
    (c : CriticalGeometry.CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action)
    (hrank : primeRank 5 H ≤ 2) (hV₃ : V₃ ≤ V)
    (hQ : Source.starImage H (c.Ugamma V₃) ∈ Q (linearAction a))
    (h : H) (hplace : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) : Nonempty (Factorization a r.P) := by
  apply factorization_of_offender src a ha r hrank _ hQ
  have hle : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃ le_rfl)
  apply bot_unique
  exact (inf_le_inf_right _ (Three.starImage_mono H hle)).trans_eq
    (Localization.SecondActor.star_faithful_on_P_of_core_placement r h hplace)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
