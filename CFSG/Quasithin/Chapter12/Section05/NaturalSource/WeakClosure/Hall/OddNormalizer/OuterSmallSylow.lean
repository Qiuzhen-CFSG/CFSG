module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterModels
public import Theory.SpecificGroups.Janko3.Model.FrattiniSixteen
public import Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen

/-!
# Small Sylow exclusions for the exterior outer section

The actual J₃ and binary Sp₆ models have Sylow Frattini quotients of order
at most sixteen. The source S₂ theorem detects a nonsolvable simple outer
section on a Sylow Frattini quotient. Its automorphism group is GLₙ(2),
with n at most four, whose order is prime to 31. This contradicts the
actual PSL₅(2) section supplied by the marked exterior residual.

Injectivity of the outer map from a perfect central cover preserves the
full original component. The final theorem removes these two rows from
the literal remaining B-model list. The consumer in `OddNormalizer`
applies it to the selected component in the normalizer of the Hall actor.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, using I.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels
local notation "Target" => Representation.SL5TenDimensional.Group
local instance smallSylowTargetSimple : IsSimpleGroup Target := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  exact Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
local instance smallSylowTargetPerfect : Group.IsPerfect Target := Atlas.sl_perfect 5 (by decide)

private theorem thirtyOne_dvd_target : 31 ∣ Nat.card Target := by
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
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

/-- The actual J₃ carrier cannot support the marked PSL₅(2) outer section. -/
theorem janko_three {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (e : Q ≃* Sporadic.Janko3.Model)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  exact no_small_frattini_section P
    (Sporadic.Janko3.TwoLocal.sylow_frattini_card_le_sixteen e P) U f hf

/-- The actual binary projective symplectic six-space is excluded as well. -/
theorem symplectic_six {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSp Q 3 2)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* Target) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  exact no_small_frattini_section P
    (Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen.frattini_card_le_sixteen_of_equiv
      hF e P) U f hf

/-- Both exclusions descend through the full original perfect central cover. -/
theorem small_sylow_cover_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Target, Function.Surjective f) :
    ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) ∧
      ¬ ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp a.symm.surjective
  exact ⟨fun ⟨e⟩ => janko_three e _ g hg, fun hm => symplectic_six hm _ g hg⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.ExteriorOuterModels

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open ChapterA.Section02 ClassificationModels

/-- The outer branch now retains only four odd classical families and McL. -/
def ExteriorFiveOuterModels (Q : Type*) [Group Q] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp Q 2 p) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsG2At Q p) ∨
  (∃ p : ℕ, p.Prime ∧ (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) ∧ ClassicalGroup.IsPSL Q 4 p) ∨
  (∃ p : ℕ, p.Prime ∧ (∃ k : ℕ, p + 1 = 2 ^ k) ∧ ClassicalGroup.IsPSU Q 4 p) ∨
  Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Eliminate the two small Sylow rows from the full original B-model list. -/
theorem exterior_five_outer_models
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* Representation.SL5TenDimensional.Group, Function.Surjective f) :
    ExteriorFiveOuterModels (K ⧸ center K) := by
  obtain ⟨hj,hs⟩ := ExteriorOuterModels.small_sylow_cover_exclusions ho
  cases exterior_remaining_outer_models hm ho with
  | symplectic p hp ho he => exact Or.inl ⟨p,hp,ho,he⟩
  | g2 p hp ho he => exact Or.inr (Or.inl ⟨p,hp,ho,he⟩)
  | linear_four p hp hf he => exact Or.inr (Or.inr (Or.inl ⟨p,hp,hf,he⟩))
  | unitary_four p hp hf he => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p,hp,hf,he⟩)))
  | symplectic_binary he => exact (hs he).elim
  | janko_three he => exact (hj he).elim
  | mcl he => exact Or.inr (Or.inr (Or.inr (Or.inr he)))

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
