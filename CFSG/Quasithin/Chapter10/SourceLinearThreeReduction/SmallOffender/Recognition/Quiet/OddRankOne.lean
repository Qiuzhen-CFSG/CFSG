module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.BinaryRankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.BinaryThree
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.SpecificGroups.PSL2.PrimeCubicRank

/-!
# The quiet odd-prime rank-one branch is the natural binary-three survivor

The actual prime-field PSL₂ automorphism group has two-rank at most two.
The TI offender bound therefore puts the moved quotient in binary degree
at most five. The established faithful odd-characteristic degree bounds
force the prime below ten. Perfection excludes three and the actual A₅
comparison excludes five, leaving seven. The checked PSL₂(7) ≃ SL₃(2)
isomorphism invokes the completed quiet binary-three recognition, including
the literal natural action, crossed centralization and w≥2.

Source: Aschbacher--Smith 1.2.1(3), 10.1.1 and 10.2.12, pp.504,741,754--755.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE PointControl.Selection
open Matrix.ProjectiveSpecialLinearGroup ChapterG.Section07.OddCharacteristic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The group identification is proved before imposing any module marking. -/
theorem quiet_odd_prime_binary_three_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := D.quasisimple
  have hp3 : 3 < p := by
    have hne : p ≠ 3 := by
      intro he
      exact not_perfect_of_card_three (hF.trans he)
        (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
    have hp2 := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
  have hr : primeRank 2 (MulAut (L ⧸ pCore 2 L)) ≤ 2 :=
    psl2_prime_automorphism_two_rank_le_two hp hp3 ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
  have hthree := Theory.PSL2.prime_model_three_dvd_card hp ho hF e
  have hu := quiet_moved_card_le_of_automorphism_rank D c hJ hNL hthree hr
  let := source_full_moved_elementary D
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)
  obtain ⟨ρ,s,hf,_⟩ := exists_moved_quotient_action D c.nonnormal e
  have hc : Nat.card Q ≤ 2 ^ 5 :=
    (Nat.card_le_card_of_surjective s.coordinates s.onto).trans hu
  have hd : Module.finrank (ZMod 2) Q ≤ 5 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hp9 : p ≤ 9 := by
    by_contra! hn
    have hh := (psl2_degree_bounds ρ hf hp ho (e := 1) (by decide)
      (by simpa only [pow_one] using hn)
      ⟨F,inferInstance,inferInstance,by simpa only [pow_one] using hF,⟨MulEquiv.refl _⟩⟩).1
    change 6 < Module.finrank (ZMod 2) Q at hh
    omega
  have hcases : p = 5 ∨ p = 7 := by
    interval_cases p <;> norm_num at hp <;> omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := equiv_alternatingGroup_of_card_four
      (show Nat.card (GaloisField 2 2) = 4 from GaloisField.card 2 2 (by decide))
    exact (c.notA5 ⟨e.trans ((cardFiveEquivFour hF).trans a)⟩).elim
  · exact ⟨e.trans ((Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hF).trans
      Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm)⟩

/-- The literal geometry and weak-closure lower bound in every quiet odd-prime row. -/
theorem survivor_of_quiet_odd_prime
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    Nonempty (SourceLinearThreeGeometry T D) ∧
      2 ≤ globalW D.fullModule (T : Subgroup G) := by
  obtain ⟨e⟩ := quiet_odd_prime_binary_three_equiv D c hJ hNL hp ho hm
  exact survivor_of_quiet_binary_three D c hJ hNL e

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
