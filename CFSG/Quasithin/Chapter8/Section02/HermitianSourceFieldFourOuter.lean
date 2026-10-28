module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPushingUp
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.SpecificGroups.OddThreeFrattini
public import Theory.SpecificGroups.SymplecticFour.OddFrattiniEight
public import Theory.SpecificGroups.PSL4.FermatFrattini
public import Theory.SpecificGroups.ClassicalUnitary.MersenneFrattini
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow
public import Theory.SpecificGroups.G2.OddFrattiniEight
public import Theory.SpecificGroups.Janko3.Model.FrattiniEight
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniEight
public import Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
public import Theory.GroupTheory.SylowOuterFrattiniSections
public import Theory.GroupTheory.FrattiniFlagSimpleSections
public import Theory.ElementaryAbelian.AutomorphismLinearModel
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPushingUp

/-!
# Field-four Hermitian quotients are not component outer sections

Every actual Theorem B component is inspected. Small Sylow Frattini
quotients and the binary symplectic Sylow automorphism bound exclude the
additional B rows. The PSU₅(4) Sylow flag detects a simple section on one
of two order-sixteen factors; their automorphism groups are PSL₄(2).
The actual PSL₃(4)/PSL₄(2) carrier separation excludes this last case.
Perfect central descent retains the full center of the original component.

The proof-only import reuses the internal field and carrier comparisons
from FieldFourPushingUp. The Chapter 12 FieldFourOuter consumer applies
this result to the original odd fixed residual and its selected component.
Source: Aschbacher--Smith 4.4.10--11 and Remark 4.4.2, printed pp.619,621,
as used in 8.2.7, printed p.718, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ClassificationModels Theory.SpecificGroups BenderSuzuki.MatrixGroups
open ChapterA.Section02
local notation "Target" => Matrix.PSL3Four.PSL
private instance : IsSimpleGroup Target := Atlas.psl_simple_high_rank 3 (by decide)
private theorem target_card : Nat.card Target = 20160 :=
  field_four_card Matrix.PSL3Four.card_F

private theorem no_small_frattini_section
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (P : Sylow 2 Q) (hP : Nat.card (P ⧸ frattini P) ≤ 8)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_frattini_aut P
    (Group.IsPerfect.not_isSolvable Target) U f hf
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn3 : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [←hn] using hP
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn,
    target_card] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ,Nat.factorial] at hd


private theorem linear_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact OddThreeFrattini.projective_linear
    (OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))
    (P.mapSurjective e.surjective)


private theorem unitary_three_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 3 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact OddThreeFrattini.projective_unitary J
    (OddThreeRank.two_ne_zero_of_odd_card ho hF) (P.mapSurjective e.surjective)


private theorem unitary_four_binary
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
  let P : Sylow 2 Q := default
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
    exact Group.IsPerfect.not_isSolvable Target (Group.isSolvable_of_surjective hf)


private theorem symplectic_four_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSp Q 2 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact SymplecticFour.OddFrattiniEight.projective_frattini_card_le
    ho hF (P.mapSurjective e.surjective)


private theorem linear_four_fermat
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) (hm : ClassicalGroup.IsPSL Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply PSL4.FermatFrattini.projective_frattini_le ?_ (P.mapSurjective e.surjective)
  obtain ⟨k,hk⟩ := hp
  exact ⟨k,hF.trans hk⟩


private theorem unitary_four_mersenne
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (hm : ∃ k : ℕ, p+1 = 2^k)
    (hmodel : ClassicalGroup.IsPSU Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k,hk⟩ := hm
    have hk2 : k < 2 := by
      by_contra! h
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) h
      omega
    interval_cases k <;> norm_num at hk
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hmodel
  let P : Sylow 2 Q := default
  apply no_small_frattini_section P ?_ U f
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  exact ClassicalUnitary.MersenneFrattini.projective_frattini_le J
    (hp.odd_of_ne_two hp2) hm hF hconj (P.mapSurjective e.surjective)


private theorem symplectic_six_binary
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSp Q 3 2)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup Target := inferInstance
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable (Target)) U f hf
  apply SymplecticSix.BinarySylowAutomorphisms.not_five_dvd_sylow_aut_of_equiv hF e P
  apply dvd_trans ?_ hd
  rw [target_card]
  norm_num [Nat.factorial]


private theorem janko_three
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.Janko3.Model)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) :
    ¬ Function.Surjective f :=
  no_small_frattini_section (default : Sylow 2 Q)
    (Sporadic.Janko3.TwoLocal.FrattiniEight.sylow_frattini_card_le_eight e _) U f


private theorem mcl
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.LeechRelated.McL.Carrier)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) :
    ¬ Function.Surjective f :=
  no_small_frattini_section (default : Sylow 2 Q)
    (Sporadic.LeechRelated.McL.FrattiniEight.sylow_frattini_card_le_eight_of_equiv e _) U f


private theorem g2_odd
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : IsG2At Q p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) :
    ¬ Function.Surjective f := by
  intro hf
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  have hP : Nat.card (P ⧸ frattini P) ≤ 8 := by
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Atlas.G2.OddFrattiniEight.frattini_card_le_eight ho hF (P.mapSurjective e.surjective)
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup Target := inferInstance
  have hd := MulAut.simple_outer_section_card_dvd_frattini_aut P
    (Group.IsPerfect.not_isSolvable (Target)) U f hf
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn3 : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [←hn] using hP
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn,
    target_card] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ,Nat.factorial] at hd


private theorem no_four_automorphism_section
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (U : Subgroup (MulAut A)) (f : U →* Target)
    (hf : Function.Surjective f) : False := by
  let a := IsElementaryAbelian.mulAutLinearEquivOfCard (p := 2) (n := 4) A (by simpa using hA)
  let b := BinaryLinear.OuterCyclic.matrixEquivLinear 4
  let c := (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).symm
  let e := a.trans (b.trans c)
  let j := U.equivMapOfInjective e.toMonoidHom e.injective
  exact field_four_no_binary_four_section Matrix.PSL3Four.card_F (U.map e.toMonoidHom)
    (f.comp j.symm.toMonoidHom) (hf.comp j.symm.surjective)

private theorem unitary_five_four
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSU Q 5 4)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hcard hconj
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  obtain ⟨W,g,hg⟩ := MulAut.simple_outer_section_in_sylow_aut P
    (Group.IsPerfect.not_isSolvable Target) U f hf
  obtain ⟨R,hR,hcardR,hquot⟩ := UnitaryFive.Flag.sylow_invariant_frattini_flag_four
    (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl (e.trans a) P
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_injective R.subtype R.subtype_injective
  rcases simple_section_invariant_frattini_flag P.isPGroup'
    (Group.IsPerfect.not_isSolvable Target) R hR W g hg with ⟨W,g,hg⟩ | ⟨W,g,hg⟩
  · exact no_four_automorphism_section hcardR W g hg
  · exact no_four_automorphism_section hquot W g hg

/-- Every actual simple Theorem B model has no PSL₃(4) outer section. -/
theorem field_four_simple_no_outer_section
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ¬ IsMulCommutative Q) (hm : IsTheoremBModel Q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  have hns : ¬ Group.IsSolvable (MulAut.Outer Q) := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable Target (Group.isSolvable_of_surjective hf)
  have hC (hc : IsTheoremCModel Q) : False :=
    hns (ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC hna hc)
  cases hm with
  | alternating n hn e =>
    exact hns (ChapterA.Section03.SourceComponents.TheoremBOuter.alternating hna e)
  | odd h =>
    cases h with
    | linear_two q hq e =>
      exact hns (ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd hna hq e)
    | linear_three p a _ hq _ e => exact linear_three_odd hq.pow e U f hf
    | unitary_three p a _ hq _ e => exact unitary_three_odd hq.pow e U f hf
    | symplectic p hp hq e => exact symplectic_four_odd hp hq e U f hf
    | g2 p hp hq e => exact g2_odd hp hq e U f hf
    | linear_four p _ hh e => exact linear_four_fermat hh e U f hf
    | unitary_four p hp hh e => exact unitary_four_mersenne hp hh e U f hf
  | bender h => exact hC (.bender h)
  | linear_binary n hn h => exact hC (.linear_binary n hn h)
  | symplectic_binary h => exact symplectic_six_binary h U f hf
  | rank_two n h =>
    cases h with
    | linear hn h => exact hC (.rank_two n (.linear hn h))
    | unitary_four hn h => exact unitary_four_binary hn h U f hf
    | unitary_five hn h => exact unitary_five_four (by simpa [hn] using h) U f hf
    | symplectic hn h => exact hC (.rank_two n (.symplectic hn h))
    | g2 hn h => exact hC (.rank_two n (.g2 hn h))
    | triality hn h => exact hC (.rank_two n (.triality hn h))
    | ree_f4 m hm hn h => exact hC (.rank_two n (.ree_f4 m hm hn h))
    | symplectic_derived hn h => exact hC (.rank_two n (.symplectic_derived hn h))
    | g2_derived hn h => exact hC (.rank_two n (.g2_derived hn h))
    | tits hn h => exact hC (.rank_two n (.tits hn h))
  | sporadic h =>
    rcases h with ⟨name,e⟩ | e | e
    · by_cases hj : name = .j3
      · subst name; exact janko_three e.some U f hf
      · exact hC (.sporadic (.inl ⟨name,hj,e⟩))
    · exact hC (.sporadic (.inr e))
    · exact mcl e.some U f hf

/-- The full component center and the original field marking are retained. -/
theorem field_four_no_outer_section
    {K E : Type*} [Group K] [Finite K] [IsQuasisimple K] [Field E] [Finite E]
    (hm : IsTheoremBModel (K ⧸ center K)) (hc : Nat.card E = 4)
    (U : Subgroup (MulAut.Outer K)) (f : U →* PSL(3,E)) : ¬ Function.Surjective f := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (K ⧸ center K)
  let j := MulAut.centralQuotientOuter e
  let a := U.equivMapOfInjective j (MulAut.centralQuotientOuter_injective e)
  let b := Atlas.fieldEquivPSL 3 (fieldFourEquiv hc)
  intro hf
  exact field_four_simple_no_outer_section (Group.IsPerfect.not_isMulCommutative _) hm
    (U.map j) (b.toMonoidHom.comp (f.comp a.symm.toMonoidHom))
    (b.surjective.comp (hf.comp a.symm.surjective))

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
