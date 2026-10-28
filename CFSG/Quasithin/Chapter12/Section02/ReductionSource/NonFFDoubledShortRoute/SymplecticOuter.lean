module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticHallReduction
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement
import all CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterSymplectic
import all CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterField

/-!
# The symplectic residual has no outer image

The full Theorem B catalogue has no nonbinary Sp4 section in a component's
outer automorphism group. Sylow restriction bounds its order by |GL8(2)|,
leaving only Sp4(4). Its factors 17 and 25 exclude the smaller Frattini
quotients and the two invariant flag quotients of PSU5(4), respectively.
The original quasisimple covering center is retained throughout.

The proof-only imports reuse the generic Sylow and section lemmas of the
natural-module owner without assuming that owner's T-invariant seed.
SymplecticPlacement applies this result to the actual odd fixed residual
on the doubled source orbit, discharging the inner-action premise of 4.4.10.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.NonFFDoubledShortRoute
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups
open ChapterA.Section03.SourceComponents
open Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem symplectic_degree_two_of_outer_order
    (F : BinaryField) (hn : 1 < F.degree)
    (hd : Nat.card (SymplecticFour.Sp F.Carrier) ∣ 5348063769211699200) : F.degree = 2 := by
  rw [SymplecticFour.card_sp,F.card_eq] at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 5348063769211699200) hd
  have hf : F.degree ≤ 6 := by
    by_contra! hf
    have hq : 128 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
    have hl := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
    norm_num at hl
    omega
  interval_cases he : F.degree <;> first | rfl | norm_num [he] at hd

private theorem unitary_four_no_seventeen_section
    {Q R : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ¬ Group.IsSolvable R) (h17 : 17 ∣ Nat.card R)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* R) (hf : Function.Surjective f) : False := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := Classical.choice inferInstance
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let j : P ≃* P' := P.equivMapOfInjective e.toMonoidHom e.injective
  by_cases hn1 : n = 1
  · apply no_seventeen_small_sylow_outer_section h17 hR P _ U f hf
    rw [SylowFrattiniBounds.card_congr j,
      ClassicalUnitary.UnitaryFourSylow.FrattiniExact.projective_frattini_card
        F J (by omega) hcard hconj P', hn1]
    norm_num
  · let : Group.IsSolvable (MulAut P') :=
      ClassicalUnitary.FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega : 1 < n) hcard hconj P'
    let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
      (f := (MulAut.congr j.symm).toMonoidHom) (MulAut.congr j.symm).surjective
    let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    let : Group.IsSolvable (MulAut.Outer Q) := MulAut.outer_isSolvable_of_sylow_aut P
    exact hR (Group.isSolvable_of_surjective hf)

/-- No nonbinary symplectic simple quotient survives in the outer group of an
actual Theorem B component cover. Full central covers and the entire B catalogue
are retained. -/
theorem symplectic_no_outer_section
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (F : BinaryField) (hn : 1 < F.degree)
    [IsSimpleGroup (SymplecticFour.Sp F.Carrier)]
    (hS : ¬ Group.IsSolvable (SymplecticFour.Sp F.Carrier))
    (U : Subgroup (MulAut.Outer K)) (f : U →* SymplecticFour.Sp F.Carrier)
    (hf : Function.Surjective f) : False := by
  have hn2 := symplectic_degree_two_of_outer_order F hn (cover_outer_section_order hm hS U f hf)
  have hc : Nat.card (SymplecticFour.Sp F.Carrier) = 979200 := by
    rw [SymplecticFour.card_sp,F.card_eq,hn2]
    norm_num
  have h17 : 17 ∣ Nat.card (SymplecticFour.Sp F.Carrier) := by rw [hc]; decide
  have h25 : 25 ∣ Nat.card (SymplecticFour.Sp F.Carrier) := by rw [hc]; decide
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  have hsol (hs : Group.IsSolvable (MulAut.Outer (K ⧸ center K))) : False := by
    let := hs
    exact hS (Group.isSolvable_of_surjective hg)
  have hC (h : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) : False :=
    hsol (TheoremBOuter.of_theoremC (Group.IsPerfect.not_isMulCommutative _) h)
  have hsmall (P : Sylow 2 (K ⧸ center K))
      (hP : Nat.card (P ⧸ frattini P) ≤ 128) : False :=
    no_seventeen_small_sylow_outer_section h17 hS P hP (U.map j) g hg
  cases hm with
  | alternating n _ he => exact hsol (TheoremBOuter.alternating (Group.IsPerfect.not_isMulCommutative _) he)
  | odd h => obtain ⟨P,hP⟩ := odd_model_frattini_small h; exact hsmall P hP
  | bender h => exact hC (.bender h)
  | linear_binary n hn h => exact hC (.linear_binary n hn h)
  | symplectic_binary h =>
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := h
    let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
    exact hsmall P (SymplecticSix.BinarySylowFrattini.frattini_card_le_of_equiv hE e P)
  | rank_two n h =>
    cases h with
    | linear hn h => exact hC (.rank_two n (.linear hn h))
    | unitary_four hn h => exact unitary_four_no_seventeen_section hS h17 hn h (U.map j) g hg
    | unitary_five hn h =>
      subst n
      obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := h
      let : CharP E 2 := UnitaryFive.charP_two_of_card_sixteen hcard
      obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hcard hconj
      let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
      have hpair := UnitaryFive.Flag.sylow_solvableQuotientPair_four
        (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
        hcard hconj rfl (e.trans a) P
      exact no_outer_section_of_quotient_pair h25 hS P hpair (U.map j) g hg
    | symplectic hn h => exact hC (.rank_two n (.symplectic hn h))
    | g2 hn h => exact hC (.rank_two n (.g2 hn h))
    | triality hn h => exact hC (.rank_two n (.triality hn h))
    | ree_f4 m hm hn h => exact hC (.rank_two n (.ree_f4 m hm hn h))
    | symplectic_derived hn h => exact hC (.rank_two n (.symplectic_derived hn h))
    | g2_derived hn h => exact hC (.rank_two n (.g2_derived hn h))
    | tits hn h => exact hC (.rank_two n (.tits hn h))
  | sporadic h =>
    rcases h with ⟨name,he⟩ | he | he
    · by_cases hj : name = .j3
      · subst name
        let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
        exact hsmall P ((FiniteModelSylowFrattini.j3_card_le_thirtytwo he.some P).trans (by decide))
      · exact hC (.sporadic (.inl ⟨name,hj,he⟩))
    · exact hC (.sporadic (.inr he))
    · let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
      exact hsmall P (FiniteModelSylowFrattini.mcl_card_le_128 he.some P)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule.NonFFDoubledShortRoute
