module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Classification
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup

/-!
# Passing from the original natural quotient to the original natural module

In the L₃(2) row of 12.2.2, the projection of the chosen module onto the
natural three-space has exactly the fixed space as kernel. The original
12.4.2(1) makes this kernel zero. Its inverse therefore gives natural
coordinates on V itself, intertwining the original L/O₂(L) projection.
No quotient of V is substituted for V in the Chapter 14 setup.

The two earlier implications below deliberately separate the marked row
of 12.2.2 from the fixed-space exclusion of 12.4.2. In particular the
former permits the genuine four-dimensional indecomposable extension.
The latter must be proved by the original fusion argument; it does not
follow from a cohomology dimension bound. The universal 13.3.2 list supplies
maximality through faithful upward closure and local rigidity.

Source: Aschbacher–Smith, 12.2.2(3b), p.795; 12.4.2(1), pp.812–816;
13.3.2(3), p.885; 14.3.4(3), p.990.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.Noncentrality.SupercriticalSource
open FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal marked L₃(2) row of 12.2.2, before the fixed space is
eliminated. Both the natural module and its indecomposable extension are allowed. -/
def SLThreeMarkedQuotient1222 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A W : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple S A → (D : ChosenModule S A W) →
    ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2 → Nonempty (SLThreeExtension D)

/-- Precisely the L₃(2) implication of original 12.4.2(1), with the
unchanged ambient hypotheses and original chosen subgroup. -/
def SLThreeFixedSpace1242 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X) (A W : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple S A → ChosenModule S A W →
    ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2 → fixedSubgroup A W = ⊥

/-- Vanishing of the actual fixed subgroup makes the original marked
projection an equivalence, with precisely the required conjugation equation. -/
noncomputable def naturalMarking_of_fixed_eq_bot (D : ChosenModule T L V)
    (E : SLThreeExtension D) (hfixed : fixedSubgroup L V = ⊥) :
    letI := D.elementary
    AmbientNaturalMarking L D.normalizes 3 := by
  letI := D.elementary
  have hk : E.projection.toLinearMap.ker = ⊥ := by
    rw [E.kernel]
    apply bot_unique
    intro v hv
    have hc : (v.toMul : G) ∈ fixedSubgroup L V :=
      ⟨v.toMul.property, (E.mem_fixed_iff v).mp hv⟩
    rw [hfixed] at hc
    change v = 0
    apply Additive.toMul.injective
    exact Subtype.ext hc
  let e := LinearEquiv.ofBijective E.projection.toLinearMap
    ⟨LinearMap.ker_eq_bot.mp hk, E.surjective⟩
  refine {
    quotientEquiv := E.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3)
    coordinates := e
    equivariant := ?_ }
  intro l v
  have hc : Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
      (mem_normalizer_iff.mp (D.normalizes l.property) v.toMul).mp v.toMul.property⟩ =
      E.action (E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (E.conjugation l v).symm
  rw [hc]
  exact LinearMap.congr_fun (E.projection.isIntertwining' _) v

omit [Finite G] in
/-- The concrete binary quotient is quasisimple independently of its module. -/
theorem quotient_quasisimple (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hq
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let e' := e.trans (Atlas.fieldEquivPSL 3 eF)
  let : IsQuasisimple Matrix.PSL3Two.SL := {
    toIsPerfect := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact IsQuasisimple.of_mulEquiv (Matrix.PSL3Two.equiv.trans e'.symm)

/-- Assemble the exact universal input used by CaseOneSource. Its naturality
comes from 12.4.2 on the whole chosen module, not just its quotient. -/
theorem earlier1332CaseOne_of_sources
    (source1332 : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X)
      (A : Subgroup X), Counterexample S A → Source1332OneTwo S)
    (marked : SLThreeMarkedQuotient1222.{u}) (fixed : SLThreeFixedSpace1242.{u}) :
    Earlier1332CaseOne.{u} := by
  intro X _ _ S A d hq
  have ha := (faithfulLocalComponents_iff A).mp d.local_component
  have hm := normal_maximal_of_source1332 d (source1332 X S A d) ha.1 ha.2
  have hmax : FaithfulMaximalLocal S A := ⟨hm.2, ha.2⟩
  have hqs := quotient_quasisimple hq
  refine ⟨hmax, hqs, ?_⟩
  intro W D
  let h := hypothesis1223 d hmax hqs
  obtain ⟨E⟩ := marked X S A W h D hq
  exact ⟨naturalMarking_of_fixed_eq_bot D E (fixed X S A W h D hq)⟩

/-- Apply the assembled earlier implication to the original 12.8.1 setup.
The output contains the actual flag-compatible natural marking of V. -/
noncomputable def higherRankHypothesis_of_sources (d : Counterexample T L)
    (source1332 : ∀ (X : Type u) [Group X] [Finite X] (S : Sylow 2 X)
      (A : Subgroup X), Counterexample S A → Source1332OneTwo S)
    (marked : SLThreeMarkedQuotient1222.{u}) (fixed : SLThreeFixedSpace1242.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (D : ChosenModule T L V) :
    Chapter12.Section08.HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 :=
  higherRankHypothesis d (earlier1332CaseOne_of_sources source1332 marked fixed) hq D

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
