module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Centralizer.Residual
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Quasisimple

/-!
# E₂ structure of the inner-involution residual supplement

For an odd field of order greater than three, the actual centralizer residual
is SL₂ and has center of order two. Its Sylow supplement has two-group
quotient and equal two- and solvable residuals. An inner four-group survives
the radical: otherwise it centralizes the perfect core and embeds into the
cyclic scalar centralizer on the inner side. The quasisimple two-extension
constructor now supplies every E₂ clause, including the orbit under local tau.

This proves the matrix input to the inner-family generation argument. No
generation-geometry hypothesis is used. Source: Aschbacher--Smith E.1.2(E2),
E.1.5 and E.1.14(7), pp.210,214; A.3.21(a), p.55; Asc82a, Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

private theorem radical_le_centralizer_residual {H : Type*} [Group H] [Finite H]
    [IsQuasisimple (solvableResidual H)] :
    solvableRadical H ≤ centralizer (solvableResidual H : Set H) := by
  let D := solvableResidual H
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hc : IsComponent H D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  rcases hc.normal_dichotomy (solvableRadical H) with h | h
  · let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := inclusion h) (inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- An inner four-group has nontrivial image in the actual radical quotient. -/
theorem inner_actor_not_le_supplement_radical
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F))
    (hA : IsElementaryAbelian 2 A) (hfour : Nat.card A = 4)
    (hAT : A ≤ (T : Subgroup (graphExtension F))) (hAI : A ≤ innerPart F)
    (z : graphExtension F) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    ¬ A.subgroupOf (innerCentralizerSupplement F T z) ≤
      solvableRadical (innerCentralizerSupplement F T z) := by
  let K := innerCentralizerSupplement F T z
  let C := centralizer ({z} : Set (graphExtension F))
  let N := innerCentralizer F z
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv F ho hlarge z (hAI hzA) hz
  let e := (innerCentralizerSupplement_residualEquiv F hTz).trans ec
  let : IsQuasisimple (solvableResidual K) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  let : Group.IsNilpotent (C ⧸ N) := (innerCentralizer_quotient F z).isNilpotent
  let : IsCyclic (centralizer (solvableResidual N : Set N)) :=
    innerCentralizer_residual_centralizer_cyclic F ho hlarge z (hAI hzA) hz
  have hAK : A ≤ K := hAT.trans le_sup_right
  intro hAR
  change A.subgroupOf K ≤ solvableRadical K at hAR
  have hcomm : A ≤ centralizer ((solvableResidual K).map K.subtype : Set (graphExtension F)) := by
    have hm := (map_mono (f := K.subtype) (hAR.trans radical_le_centralizer_residual)).trans
      (map_centralizer_le_centralizer_image (solvableResidual K : Set K) K.subtype)
    rw [map_subgroupOf_eq_of_le hAK] at hm
    exact hm
  have hmap : ((solvableResidual N).map N.subtype).map C.subtype =
      (solvableResidual K).map K.subtype := by
    rw [map_solvableResidual_eq_of_solvable_quotient N]
    exact (innerCentralizerSupplement_residual_map F hTz).symm
  let f : A →* N :=
    { toFun := fun a => ⟨⟨a.val, hTz (hAT a.property)⟩, hAI a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : ∀ a : A, f a ∈ centralizer (solvableResidual N : Set N) := by
    intro a
    rw [mem_centralizer_iff]
    intro d hd
    have hdG : d.val.val ∈ (solvableResidual K).map K.subtype := by
      rw [← hmap]
      exact ⟨d.val, ⟨d, hd, rfl⟩, rfl⟩
    exact Subtype.ext (Subtype.ext (mem_centralizer_iff.mp (hcomm a.property) _ hdG))
  let j := f.codRestrict (centralizer (solvableResidual N : Set N)) hf
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (congrArg (fun x => x.val.val.val) h)
  let : IsElementaryAbelian 2 A := hA
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hfour
    (isCyclic_of_injective j hj)

/-- Every clause of the published intrinsic component predicate is satisfied. -/
theorem innerCentralizerStructure_of_odd_card
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F) : InnerCentralizerStructure F := by
  intro T A hA hfour hAT hAI z hz hzA hTz
  let K := innerCentralizerSupplement F T z
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv F ho hlarge z (hAI hzA) hz
  let e := (innerCentralizerSupplement_residualEquiv F hTz).trans ec
  let : IsQuasisimple (solvableResidual K) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge e
  have hzSL : IsPGroup 2 (center SL(2,F)) :=
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F ho).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker F))
  have hzD : IsPGroup 2 (center (solvableResidual K)) := hzSL.of_equiv (centerCongr e).symm
  have hq : IsPGroup 2 (K ⧸ solvableResidual K) :=
    (isPGroup_quotient_pResidual (G := K) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (innerCentralizerSupplement_pResidual_eq F hTz))
  exact PSUThreeGeneration.eCaseComponent_of_quasisimple_two_quotient
    (T : Subgroup (graphExtension F)) A K (solvableResidual K) hzD hq
      (inner_actor_not_le_supplement_radical F ho hlarge T A hA hfour hAT hAI z hz hzA hTz)

/-- The requested odd-prime specialization, with no additional model or geometry premise. -/
theorem innerCentralizerStructure {p : ℕ} (_hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p) (hF : Nat.card F = p) : InnerCentralizerStructure F :=
  innerCentralizerStructure_of_odd_card F (by simpa only [hF] using ho)
    (by simpa only [hF] using hlarge)

/-- Application to the literal E₁ member consumed by the generation argument. -/
theorem innerCentralizerSupplement_isEMemberAt_of_odd_card
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F))
    (hA : IsElementaryAbelian 2 A) (hfour : Nat.card A = 4)
    (hAT : A ≤ (T : Subgroup (graphExtension F))) (hAI : A ≤ innerPart F)
    (z : graphExtension F) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    IsEMemberAt 1 (T : Subgroup (graphExtension F)) A (innerCentralizerSupplement F T z) :=
  innerCentralizerSupplement_isEMemberAt F T A hA hfour hAT z hz hzA hTz
    (innerCentralizerStructure_of_odd_card F ho hlarge T A hA hfour hAT hAI z hz hzA hTz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
