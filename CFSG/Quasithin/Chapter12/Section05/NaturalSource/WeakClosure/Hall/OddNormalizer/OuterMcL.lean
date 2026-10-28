module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterSmallSylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniSixteen

/-!+# Excluding the actual McL outer section

The certified McL Sylow Frattini quotient has at most sixteen elements.
The source S₂ theorem detects a nonsolvable simple outer section on its
automorphism group, which therefore has order prime to 31. The marked
PSL₅(2) quotient has order divisible by 31. Perfect central descent applies
the contradiction to the full original component cover.

The remaining model theorem feeds the literal Hall counterexample in
`OddNormalizer`; it leaves the four odd classical rows and both separate
J₄ source arguments explicit. Source: Aschbacher--Smith 4.4.10--11, p.621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels
local notation "Target" => Representation.SL5TenDimensional.Group

/-- The literal McL model cannot have the marked PSL₅(2) outer section. -/
theorem mcl {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.LeechRelated.McL.Carrier)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Target := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Target := Atlas.sl_perfect 5 (by decide)
  let P : Sylow 2 Q := default
  have hP := Sporadic.LeechRelated.McL.FrattiniSixteen.sylow_frattini_card_le_sixteen_of_equiv e P
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
theorem mcl_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.McL.Carrier) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  rintro ⟨e⟩
  exact mcl e _ (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterA.Section02 ClassificationModels

/-- Only the four actual odd classical families remain in the outer branch. -/
def ExteriorFourOuterModels (Q : Type*) [Group Q] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp Q 2 p) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsG2At Q p) ∨
  (∃ p : ℕ, p.Prime ∧ (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) ∧ ClassicalGroup.IsPSL Q 4 p) ∨
  (∃ p : ℕ, p.Prime ∧ (∃ k : ℕ, p + 1 = 2 ^ k) ∧ ClassicalGroup.IsPSU Q 4 p)

/-- Eliminate McL from the literal remaining B-model alternatives. -/
theorem exterior_four_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* Representation.SL5TenDimensional.Group, Function.Surjective f) :
    ExteriorFourOuterModels (K ⧸ center K) := by
  rcases exterior_five_outer_models hm ho with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (ExteriorOuterModels.mcl_cover_exclusion ho h).elim

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
