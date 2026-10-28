module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Residual
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedLocals
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Large constrained families excluded on the original doubled-binary witness

The actual intersection residual LH is normal in the original local M and
has its marked quotient SL₃(2). An explicit upper-unitriangular element of
this quotient has order four, so its two-subgroups do not all have exponent
two. The constrained local theorems retain the original radical intersection
and exclude the large SL₃, Sp₄ and G₂ star models through this exact quotient.

The binary SL₃ endpoint, the small derived G₂ and alternating models, and
the binary degree-five model are separate source duties. No parabolic
residual marking or classification of the fixed-space commutator is assumed.
Source: Aschbacher--Smith C.2.7, C.4.5--8 and 12.1.11, pp.145--154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private instance : IsSimpleGroup BinaryLinearThree.Group :=
  Atlas.Comparisons.Exceptional.sl3Two_simple
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

private def binaryThreeFour : BinaryLinearThree.Group :=
  ⟨!![1,1,0;0,1,1;0,0,1], by decide⟩

private theorem binary_three_not_two_exponent :
    ¬ ∀ P : Subgroup BinaryLinearThree.Group, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  have hfour : binaryThreeFour ^ 4 = 1 := by decide
  have hsquare : binaryThreeFour ^ 2 ≠ 1 := by decide
  have hp : IsPGroup 2 (zpowers binaryThreeFour) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hfour
  intro he
  exact hsquare (congrArg Subtype.val
    (he (zpowers binaryThreeFour) hp ⟨binaryThreeFour,mem_zpowers _⟩))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- No large linear-three star model occurs for this literal constrained witness. -/
theorem sourceOrbit_binary_witness_constrained_not_linear_three_large
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (E : BinaryField) (hE : 1 < E.degree) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      SL(3,E.Carrier)) := by
  rintro ⟨e⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  exact no_constrained_normalized_linear_three hc hn
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) binary_three_not_two_exponent
    q (a.surjective.comp (QuotientGroup.mk'_surjective _)) K hK hq hout hfK E hE e

/-- No large symplectic-four star model occurs for this literal constrained witness. -/
theorem sourceOrbit_binary_witness_constrained_not_sp4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (E : BinaryField) (hE : 1 < E.degree) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Matrix.symplecticGroup (Fin 2) E.Carrier) := by
  rintro ⟨e⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  apply no_constrained_normalized_symplectic hc hn
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) binary_three_not_two_exponent
    q (a.surjective.comp (QuotientGroup.mk'_surjective _)) K hK hq hout hfK e
  rw [E.card_eq]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)

/-- No large G₂ star model occurs for this literal constrained witness. -/
theorem sourceOrbit_binary_witness_constrained_not_g2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (E : BinaryField) (hE : 1 < E.degree) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      Atlas.G2.Model E.Carrier) := by
  rintro ⟨e⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  apply no_constrained_normalized_g2 hc hn
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) binary_three_not_two_exponent
    q (a.surjective.comp (QuotientGroup.mk'_surjective _)) K hK hq hout hfK e
  rw [E.card_eq]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
