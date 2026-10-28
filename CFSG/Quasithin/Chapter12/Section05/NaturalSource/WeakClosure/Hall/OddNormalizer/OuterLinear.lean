module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterG2
public import Theory.SpecificGroups.PSL4.OddFrattiniSixteen

/-!
# Excluding the odd linear-four outer section

The determinant-one subgroup of the two-block GL₂ wreath product has odd
index in SL₄ over every odd finite field. Its Sylow Frattini quotient has
at most sixteen elements. The actual PSL₅(2) outer section would therefore
have order dividing GL₄(2), contrary to its divisor 31. Projective descent
and perfect central descent retain the original full component cover.

The final theorem removes the Fermat-prime linear row from the literal Hall
counterexample. Source: Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels
open ClassificationModels
local notation "Target" => Representation.SL5TenDimensional.Group

/-- An odd linear-four model has no marked PSL₅(2) outer section. -/
theorem linear_four_odd {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 4 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Target := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Target := Atlas.sl_perfect 5 (by decide)
  let P : Sylow 2 Q := default
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hP : Nat.card (P ⧸ frattini P) ≤ 16 := by
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Theory.SpecificGroups.PSL4.OddFrattiniSixteen.projective_frattini_le
      (by simpa only [hF] using ho)
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))
      (P.mapSurjective e.surjective)
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have h31 : 31 ∣ Nat.card Target := by
    rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
      calc
        _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
          simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hh
        _ = 9999360 := by decide
    rw [hc]
    decide
  have hd := h31.trans (MulAut.simple_outer_section_card_dvd_frattini_aut P
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

/-- The exclusion preserves the full perfect central cover of the component. -/
theorem linear_four_odd_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 q := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro q hq hm
  exact linear_four_odd hq hm _ (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterA.Section02 ClassificationModels

/-- Only the unitary degree-four family remains in the outer branch. -/
def ExteriorUnitaryOuterModel (Q : Type*) [Group Q] : Prop :=
  ∃ p : ℕ, p.Prime ∧ (∃ k : ℕ, p + 1 = 2 ^ k) ∧ ClassicalGroup.IsPSU Q 4 p

/-- Eliminate the linear-four row while retaining its actual central cover. -/
theorem exterior_unitary_outer_model
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* Representation.SL5TenDimensional.Group, Function.Surjective f) :
    ExteriorUnitaryOuterModel (K ⧸ center K) := by
  rcases exterior_two_outer_models hm ho with ⟨p,hp,⟨k,hk⟩,hg⟩ | h
  · have hodd : Odd p := by
      apply hp.odd_of_ne_two
      have h : 2 ≤ 2 ^ (2 ^ k) := Nat.le_pow (by positivity)
      omega
    exact (ExteriorOuterModels.linear_four_odd_cover_exclusion ho p hodd hg).elim
  · exact h

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
