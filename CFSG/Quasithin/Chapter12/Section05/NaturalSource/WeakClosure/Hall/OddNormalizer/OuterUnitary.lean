module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterLinear
public import Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen

/-!
# Closing the exterior outer-section branch

The actual odd-prime PSU₄ Sylow Frattini quotient has order at most sixteen,
including the prime-three endpoint. Its automorphism group has order prime
to 31, excluding the marked PSL₅(2) outer section. Descent to the simple
central quotient retains the original full quasisimple cover.

Together with the preceding model exclusions, this eliminates the entire
outer-action branch of the literal Hall counterexample. Pushing-up uniqueness
and the two separate J₄ endgames remain to be established by the source owner.
Source: Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels
open ClassificationModels
local notation "Target" => Representation.SL5TenDimensional.Group

/-- An odd-prime unitary-four model has no marked PSL₅(2) outer section. -/
theorem unitary_four_odd {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {q : ℕ} (hq : q.Prime) (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 4 q)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Target := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Target := Atlas.sl_perfect 5 (by decide)
  let P : Sylow 2 Q := default
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hP : Nat.card (P ⧸ frattini P) ≤ 16 := by
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.projective_frattini_le
      J ho hF hconj
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF)
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
theorem unitary_four_odd_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 q := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro q hq ho hm
  exact unitary_four_odd hq ho hm _ (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels


public section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterA.Section02

/-- No Theorem B component cover admits the actual marked PSL₅(2) outer section. -/
theorem exterior_no_outer_section
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* Representation.SL5TenDimensional.Group, Function.Surjective f) : False := by
  obtain ⟨p,hp,⟨k,hk⟩,hu⟩ := exterior_unitary_outer_model hm ho
  have hpodd : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    cases k with
    | zero => norm_num at hk
    | succ k => simp only [pow_succ] at hk; omega)
  exact ExteriorOuterModels.unitary_four_odd_cover_exclusion ho p hp hpodd hu

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
