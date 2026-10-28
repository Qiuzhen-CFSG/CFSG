module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalPreparation
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# Source inputs for natural recognition in the solvable H-star branch

The full-axis obligation concerns the original binary action of L joined with
T. Reducedness of the actual chosen module kills the two-core of this exact
faithful image. The size bound gives dimension at least three. These facts
also apply with Structural1222At on the same ambient group and Sylow subgroup.

Independently, movement of V outside O₂(H) excludes normality of T in H.
H-star geometry therefore gives intrinsic minimal parabolicity, and solvable
B.6.8 supplies its odd-prime residual, actual Frattini kernel and irreducible
star action. This does not use NaturalLocalAnalysis. Lifting the odd subgroup,
constructing the conjugate TI pair and filling ChosenFullAxis remain explicit
source obligations.

Source: Aschbacher--Smith, B.6.8(2), pp.113--114, and the construction preceding
12.2.20, p.802. The original O₂ and O² quotients are kept distinct.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The full axis needed by dual G.3.1, on the original join action. Its
construction is a separate TI-pair obligation, not a natural-action assumption. -/
def ChosenFullAxis (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) : Prop :=
  letI := D.elementary
  ∃ f : Module.Dual (ZMod 2) (Additive V), f ≠ 0 ∧
    BinaryLinear.radical f.ker ≤ (chosenJoinLinearAction D hT).range

omit [Finite G] in
/-- Reducedness suffices at the actual chosen module; a universal structural
source implication is unnecessary for this action-kernel calculation. -/
theorem chosenJoinLinearAction_twoCore_eq_bot_of_reduced
    (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hr : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G)))) :
    letI := D.elementary
    pCore 2 (chosenJoinLinearAction D hT).range = ⊥ := by
  let := D.elementary
  let J := L ⊔ (T : Subgroup G)
  let W := V.subgroupOf J
  let := hr.normal
  let a := (chosenJoinAction D hT).asGroupHom
  let b := chosenJoinLinearAction D hT
  let e : (J ⧸ centralizer (W : Set J)) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq (chosenJoinAction_ker D hT).symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  have he := pCore_map_iso 2 e
  rw [hr.quotient_pCore_eq_bot, Subgroup.map_bot] at he
  have hk : a.ker = b.ker := by
    ext x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).map_eq_one_iff.symm
  let E : a.range ≃* b.range := (QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange b))
  have hE := pCore_map_iso 2 E
  rw [he.symm, Subgroup.map_bot] at hE
  exact hE.symm

/-- Local structural input discharges the original full actor's two-core guard. -/
theorem chosenJoinLinearAction_twoCore_eq_bot_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    letI := D.elementary
    pCore 2 (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊥ :=
  chosenJoinLinearAction_twoCore_eq_bot_of_reduced D _ (((structural L h).2.2 V D).2.1)

/-- The actual binary space has dimension at least three before recognition. -/
theorem chosen_finrank_ge_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    letI := D.elementary
    3 ≤ Module.finrank (ZMod 2) (Additive V) := by
  let := D.elementary
  have hc := chosen_card_gt_four h D
  have he : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [he] at hc
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show Module.finrank (ZMod 2) (Additive V) ≤ 2 by omega)
  omega

/-- Movement alone excludes a normal Sylow subgroup in the original H-star
member, supplying the intrinsic B.6.8 hypotheses before natural recognition. -/
theorem chosen_hstar_minimalParabolic_of_movement (D : ChosenModule T L V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : ¬ V ≤ H.pCoreIn 2) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hn : ¬ ((T : Subgroup G).subgroupOf H).Normal := by
    intro hN
    have hNT : H ≤ normalizer (T : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hTH).mp hN
    exact hm (D.le_sylow.trans (le_pCoreIn_of_normalizes T.isPGroup' hTH hNT))
  have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hH (Or.inr hn)
  obtain ⟨hTB, hBH, _⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component hH
  exact (ChapterB.intrinsic_minimalParabolic T H
    (H ⊓ normalizer (L : Set G)) hp hTB hBH).1

/-- The solvable odd-prime quotient and its actual Frattini kernel, obtained
without using NaturalLocalAnalysis or a natural module. -/
theorem chosen_hstar_solvable_structure_of_movement (D : ChosenModule T L V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    let S := T.subtype hH.1.1.2
    let hp := chosen_hstar_minimalParabolic_of_movement D hH hm
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H) ∧
      IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H)) ∧
      ChapterB.minimalParabolicCoreImage S hp =
        Stellmacher.frattiniAmbient (pCore p (H ⧸ pCore 2 H)) ∧
      pResidual 2 (ChapterB.minimalParabolicStarQuotient S hp) =
        pCore p (ChapterB.minimalParabolicStarQuotient S hp) ∧
      Stellmacher.IsIrreducibleSection (ChapterB.minimalParabolicStarSylow S hp) ⊥
        (pCore p (ChapterB.minimalParabolicStarQuotient S hp)) :=
  ChapterB.minimalParabolic_solvable_structure (T.subtype hH.1.1.2)
    (chosen_hstar_minimalParabolic_of_movement D hH hm) hs

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
