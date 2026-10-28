module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Representation.DegreeThreeFrattini
public import Theory.GroupTheory.FrattiniFlagPrimeOrder
public import Theory.SpecificGroups.OddClassicalSylowFrattini
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow
public import Theory.GroupTheory.SylowOuterFrattiniSections
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms

/-!
# Further exclusions for the actual exterior outer section

The marked PSL₅(2) quotient has order divisible by 31. Odd-characteristic
PSL₃ and PSU₃ have Sylow Frattini quotients of order at most sixteen, by
the three-dimensional weight argument. The binary PSU₄ Sylow action is
solvable above the smallest field and has Frattini order eight there.
The two order-sixteen Frattini flag factors of PSU₅(4) make its full Sylow
automorphism order prime to 31. The source S₂ theorem detects a nonsolvable
simple outer section on these Sylow automorphism groups.

Perfect central descent preserves the full component cover throughout.
The final theorem applies these exclusions to the literal component selected
in N(A); the remaining outer models and both J₄ endgames remain explicit.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, and I.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels
open Theory.SpecificGroups BenderSuzuki.MatrixGroups
local notation "Target" => Representation.SL5TenDimensional.Group
local instance targetSimple : IsSimpleGroup Target := by
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  exact Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
local instance targetPerfect : Group.IsPerfect Target := Atlas.sl_perfect 5 (by decide)

private theorem thirtyOne_dvd_target : 31 ∣ Nat.card Target := by
  have hc : Nat.card PSL(5, ZMod 2) = 9999360 := by
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    calc
      _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
        simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hh
      _ = 9999360 := by decide
  rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv, hc]
  decide

private theorem no_small_frattini_section
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (P : Sylow 2 Q) (hP : Nat.card (P ⧸ frattini P) ≤ 16)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) (hf : Function.Surjective f) : False := by
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := thirtyOne_dvd_target.trans
    (MulAut.simple_outer_section_card_dvd_frattini_aut P
      (Group.IsPerfect.not_isSolvable Target) U f hf)
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn4 : n ≤ 4 := by
    by_contra! h
    have hpow : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    rw [←hn] at hpow
    norm_num at hpow
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at hd

private theorem no_solvable_outer_section
    {Q : Type*} [Group Q] [Group.IsSolvable (MulAut.Outer Q)]
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) (hf : Function.Surjective f) : False :=
  Group.IsPerfect.not_isSolvable Target (Group.isSolvable_of_surjective hf)

/-- Odd linear-three models have no actual PSL₅(2) outer section. -/
theorem linear_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 := OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF)
  let P : Sylow 2 Q := Classical.choice inferInstance
  apply no_small_frattini_section P ?_ U f hf
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _) ?_
    (P.mapSurjective e.surjective)
  intro R
  let j := Matrix.SpecialLinearGroup.toGL.comp (R : Subgroup SL(3,F)).subtype
  apply Representation.card_frattini_quotient_le_sixteen_of_faithful_degree_three R.isPGroup'
    ((Representation.generalLinearNatural 3).comp j)
    ((Representation.generalLinearNatural_injective 3).comp
      (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective)) h2
  simp

/-- Odd unitary-three models have no actual PSL₅(2) outer section. -/
theorem unitary_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 := OddThreeRank.two_ne_zero_of_odd_card ho hF
  let P : Sylow 2 Q := Classical.choice inferInstance
  apply no_small_frattini_section P ?_ U f hf
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply OddClassicalSylowFrattini.card_le_of_surjective
    (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_
    (P.mapSurjective e.surjective)
  intro R
  let j := J.specialSubgroup.subtype.comp (R : Subgroup J.specialSubgroup).subtype
  apply Representation.card_frattini_quotient_le_sixteen_of_faithful_degree_three R.isPGroup'
    ((Representation.generalLinearNatural 3).comp j)
    ((Representation.generalLinearNatural_injective 3).comp
      (Subtype.val_injective.comp Subtype.val_injective)) h2
  simp

/-- The whole binary unitary-four family has no PSL₅(2) outer section. -/
theorem unitary_four_binary
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := Classical.choice inferInstance
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* P' := P.equivMapOfInjective e.toMonoidHom e.injective
  by_cases hn1 : n = 1
  · apply no_small_frattini_section P ?_ U f hf
    rw [SylowFrattiniBounds.card_congr a,
      ClassicalUnitary.UnitaryFourSylow.FrattiniExact.projective_frattini_card
        F J (by omega) hcard hconj P', hn1]
    norm_num
  · let : Group.IsSolvable (MulAut P') :=
      ClassicalUnitary.FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega) hcard hconj P'
    let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
      (f := (MulAut.congr a.symm).toMonoidHom) (MulAut.congr a.symm).surjective
    let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    let : Group.IsSolvable (MulAut.Outer Q) := MulAut.outer_isSolvable_of_sylow_aut P
    exact no_solvable_outer_section U f hf

/-- The two intrinsic flag factors exclude PSL₅(2) from Out(PSU₅(4)). -/
theorem unitary_five_four
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSU Q 5 4)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hcard hconj
  let P : Sylow 2 Q := Classical.choice inferInstance
  obtain ⟨B,hB,hBcard,hquot⟩ := UnitaryFive.Flag.sylow_invariant_frattini_flag_four
    (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl (e.trans a) P
  have hfree := FrattiniFlagPrimeOrder.not_dvd_aut_of_invariant_flag
    P.isPGroup' B hB hBcard hquot (by decide : Nat.Prime 31) (by decide)
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact hfree (thirtyOne_dvd_target.trans (MulAut.simple_outer_section_card_dvd_sylow_aut
    P (Group.IsPerfect.not_isSolvable Target) U f hf))

/-- Central descent excludes all four model families while retaining every
central kernel of the original quasisimple component. -/
theorem cover_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 q) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 q) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) ∧
    ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  exact ⟨fun _ hq hm => linear_three_odd hq hm _ g hg,
    fun _ hq hm => unitary_three_odd hq hm _ g hg,
    fun _ hn hm => unitary_four_binary hn hm _ g hg,
    fun hm => unitary_five_four hm _ g hg⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterA.Section02 ClassificationModels

/-- The actual B-model rows still requiring an outer-section argument.
Every row retains a literal group equivalence and all source parameters. -/
inductive ExteriorRemainingOuterModel (Q : Type*) [Group Q] : Prop
  | symplectic (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp Q 2 p)
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- Inspect the complete B-list using the actual PSL₅(2) outer section.
Both binary unitary families and all odd linear/unitary three-space rows
are now excluded, as well as the previously excluded source C-list. -/
theorem exterior_remaining_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* Representation.SL5TenDimensional.Group, Function.Surjective f) :
    ExteriorRemainingOuterModel (K ⧸ center K) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  have hna := Group.IsPerfect.not_isMulCommutative (K ⧸ center K)
  have hns : ¬ Group.IsSolvable (MulAut.Outer (K ⧸ center K)) := by
    intro hs
    let := hs
    let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
    obtain ⟨U,f,hf⟩ := ho
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
      Atlas.psl_simple_high_rank 5 (by decide)
    let : IsSimpleGroup Representation.SL5TenDimensional.Group :=
      Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
    let : Group.IsPerfect Representation.SL5TenDimensional.Group := Atlas.sl_perfect 5 (by decide)
    exact Group.IsPerfect.not_isSolvable Representation.SL5TenDimensional.Group
      (Group.isSolvable_of_surjective hf)
  have hC (hc : IsTheoremCModel (K ⧸ center K)) : False :=
    hns (ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC hna hc)
  obtain ⟨hlin,huni,hfour,hfive⟩ := ExteriorOuterModels.cover_exclusions ho
  cases hm with
  | alternating n _ e =>
    exact (hns (ChapterA.Section03.SourceComponents.TheoremBOuter.alternating hna e)).elim
  | odd h =>
    cases h with
    | linear_two q hq e =>
      exact (hns (ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd hna hq e)).elim
    | linear_three p a _ hq _ e => exact (hlin _ hq.pow e).elim
    | unitary_three p a _ hq _ e => exact (huni _ hq.pow e).elim
    | symplectic p hp hq e => exact .symplectic p hp hq e
    | g2 p hp hq e => exact .g2 p hp hq e
    | linear_four p hp hf e => exact .linear_four p hp hf e
    | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | bender h => exact (hC (.bender h)).elim
  | linear_binary n hn h => exact (hC (.linear_binary n hn h)).elim
  | symplectic_binary h => exact .symplectic_binary h
  | rank_two n h =>
    cases h with
    | linear hn h => exact (hC (.rank_two n (.linear hn h))).elim
    | unitary_four hn h => exact (hfour n hn h).elim
    | unitary_five hn h => exact (hfive (by simpa [hn] using h)).elim
    | symplectic hn h => exact (hC (.rank_two n (.symplectic hn h))).elim
    | g2 hn h => exact (hC (.rank_two n (.g2 hn h))).elim
    | triality hn h => exact (hC (.rank_two n (.triality hn h))).elim
    | ree_f4 m hm hn h => exact (hC (.rank_two n (.ree_f4 m hm hn h))).elim
    | symplectic_derived hn h => exact (hC (.rank_two n (.symplectic_derived hn h))).elim
    | g2_derived hn h => exact (hC (.rank_two n (.g2_derived hn h))).elim
    | tits hn h => exact (hC (.rank_two n (.tits hn h))).elim
  | sporadic h =>
    rcases h with ⟨name,e⟩ | e | e
    · by_cases hj : name = .j3
      · subst name; exact .janko_three e
      · exact (hC (.sporadic (.inl ⟨name,hj,e⟩))).elim
    · exact (hC (.sporadic (.inr e))).elim
    · exact .mcl e

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
