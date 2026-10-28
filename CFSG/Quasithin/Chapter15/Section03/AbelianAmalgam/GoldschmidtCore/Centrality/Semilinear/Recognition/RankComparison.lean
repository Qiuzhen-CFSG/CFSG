module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.PrimeRankZero

/-!
# Cubic-rank exclusions in the complete B.5.6 alternatives

The factors in B.5.6(3) and (5) each contain a cubic subgroup. Their actual
internal product supplies independent commuting cubic subgroups, forcing
three-rank at least two. The alternating-six factor already excludes (4).
Odd-prime rank one passes to sections by cyclic Sylow transport, so it also
excludes triple alternating covers. Symplectic and G₂ exclusions use their
checked binary cubic witnesses, and even-degree SL₃ uses the cubic torus.

The results consume the full source alternatives and retain their action data.
They do not assume any reduced classification list.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and B.5.6,
pp.99–105; F.6.18, pp.309–310, in the repaired 15.3.68 comparison.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- Rank one at three passes to all sections, including odd central covers. -/
theorem three_rank_section {C : Type*} [Group C] (hr : primeRank 3 D ≤ 1)
    (A : Subgroup D) (q : A →* C) (hq : Function.Surjective q) : primeRank 3 C ≤ 1 := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := A)
  exact P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide)
      ((primeRank_le_of_injective 3 A.subtype A.subtype_injective).trans hr)) q hq

private theorem three_dvd_linear {F : Type*} [Field F] [Finite F] [CharP F 2]
    {d : ℕ} (hd : 2 ≤ d) : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) F) := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) hij).trans
      ((commutator (Matrix.ProjectiveSpecialLinearGroup (Fin d) F)).card_subgroup_dvd_card.trans
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _)
          (QuotientGroup.mk'_surjective (center (Matrix.SpecialLinearGroup (Fin d) F)))))

private theorem binary_four_rank :
    2 ≤ primeRank 3 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rw [← primeRank_equiv 3 alternatingEightLinearEquiv]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

private theorem binary_five_rank :
    2 ≤ primeRank 3 (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  let e : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] ((Fin 4 → ZMod 2) × ZMod 2) :=
    LinearEquiv.ofFinrankEq (R := ZMod 2) _ _ (by simp)
  let f : BinaryLinear.OuterCyclic.LinearGroup 4 →* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    { toFun := fun g => e.trans ((g.prodCongr (LinearEquiv.refl _ _)).trans e.symm)
      map_one' := by ext x; simp
      map_mul' := by intros; ext x; simp }
  have hf : Function.Injective f := by
    intro a b h
    apply LinearEquiv.ext
    intro v
    have hh := congrArg (fun g : BinaryLinear.OuterCyclic.LinearGroup 5 =>
      (e (g (e.symm (v, 0)))).1) h
    simpa [f] using hh
  let g := (BinaryLinear.OuterCyclic.slEquivLinear 5).symm.toMonoidHom.comp
    (f.comp (BinaryLinear.OuterCyclic.slEquivLinear 4).toMonoidHom)
  exact binary_four_rank.trans (primeRank_le_of_injective 3 g
    ((BinaryLinear.OuterCyclic.slEquivLinear 5).symm.injective.comp
      (hf.comp (BinaryLinear.OuterCyclic.slEquivLinear 4).injective)))

/-- The full ten-model component list reduces to the two linear families
under the three-rank bound. The even-degree diagonal torus forces odd degree
in the degree-three family. All identifications remain actual isomorphisms. -/
theorem quasisimple_model_rank_one (hr : primeRank 3 D ≤ 1) (h : QuasisimpleModel D) :
    (∃ F : BinaryField, Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
      ∃ F : BinaryField, Odd F.degree ∧
        Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  cases h with
  | linearTwo F e => exact Or.inl ⟨F, ⟨e⟩⟩
  | linearThree F e =>
    refine Or.inr ⟨F, ?_, ⟨e⟩⟩
    by_contra hn
    have hl := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq
      (Nat.not_odd_iff_even.mp hn)
    rw [primeRank_equiv 3 e] at hr
    omega
  | symplecticFour F e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
      (F := F.Carrier)).trans (primeRank_le_of_injective 3
        (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype Subtype.val_injective)
    rw [primeRank_equiv 3 e] at hr
    omega
  | g2 F e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
      (F := F.Carrier)).trans (primeRank_le_of_injective 3
        (commutator (Atlas.G2.Model F.Carrier)).subtype Subtype.val_injective)
    rw [primeRank_equiv 3 e] at hr
    omega
  | alternatingSix e =>
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    rw [primeRank_equiv 3 e] at hr
    omega
  | alternatingSeven e =>
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 7) (by decide)
    rw [primeRank_equiv 3 e] at hr
    omega
  | tripleSix _ e =>
    obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := D)
    have hu := P.primeRank_quotient_le_one
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) (center D)
    rw [primeRank_equiv 3 e] at hu
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  | g2DerivedTwo e =>
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := ZMod 2)
    rw [primeRank_equiv 3 e] at hr
    omega
  | linearFourTwo e =>
    rw [primeRank_equiv 3 e] at hr
    have hl := binary_four_rank
    omega
  | linearFiveTwo e =>
    rw [primeRank_equiv 3 e] at hr
    have hl := binary_five_rank
    omega

/-- Every group factor in B.5.6(3) or (5) has an actual element of order three. -/
theorem factor_has_cubic (h : FactorModel D) : ∃ x : D, orderOf x = 3 := by
  have hd : 3 ∣ Nat.card D := by
    cases h with
    | linearTwo F e =>
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_linear (by decide)
    | symmetricFive e =>
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    | linearThree F _ e =>
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_linear (by decide)
  exact exists_prime_orderOf_dvd_card' 3 hd

private theorem factor_rank_pos {A : Type*} [Group A] [Finite A]
    (h : FactorModel A) : 1 ≤ primeRank 3 A := by
  obtain ⟨x, hx⟩ := factor_has_cubic h
  have hd : 3 ∣ Nat.card A := hx ▸ orderOf_dvd_natCard x
  have hn : primeRank 3 A ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  omega

/-- The literal product in B.5.6 contributes two independent cubic factors. -/
theorem product_three_rank (A B : Subgroup D) (p : InternalProduct A B)
    (hA : FactorModel A) (hB : FactorModel B) : 2 ≤ primeRank 3 D := by
  have ha := factor_rank_pos hA
  have hb := factor_rank_pos hB
  rw [← primeRank_equiv 3 p.equiv, primeRank_prod_eq_add]
  omega

/-- B.5.6(3) is impossible when the actual actor has three-rank at most one. -/
theorem not_twoFactors (ρ : Representation (ZMod 2) D W) (hr : primeRank 3 D ≤ 1) :
    ¬ Nonempty (SourceTwoFactorCase ρ) := by
  rintro ⟨c⟩
  have h := product_three_rank c.first c.second c.product
    (c.firstCase.factorModel ρ) (c.secondCase.factorModel ρ)
  omega

/-- B.5.6(4) is excluded by its actual alternating-six subgroup. -/
theorem not_outerSixThree (ρ : Representation (ZMod 2) D W) (hr : primeRank 3 D ≤ 1) :
    ¬ Nonempty (OuterSixThreeCase ρ) := by
  rintro ⟨c⟩
  have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  have hu := (primeRank_le_of_injective 3 c.first.subtype c.first.subtype_injective).trans hr
  rw [primeRank_equiv 3 c.firstEquiv] at hu
  omega

/-- B.5.6(5) is excluded by the two actual cubic factors, irrespective of
its nonsplit hyperplane module. -/
theorem not_hyperplane (ρ : Representation (ZMod 2) D W) (hr : primeRank 3 D ≤ 1) :
    ¬ Nonempty (HyperplaneCase ρ) := by
  rintro ⟨c⟩
  have h := product_three_rank c.first c.second c.product
    (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel ρ)
  omega

/-- Exhaust the nonquasisimple alternatives without discarding any source
module premise: only the trivial and symmetric-three cases remain. -/
theorem source_alternative_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (h : SourceAlternative ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧
        Nonempty (QuasisimpleSourceConclusion ρ (generalizedFitting D))) ∨
      Nonempty (SymmetricThreeCase ρ) := by
  cases h with
  | trivial h => exact Or.inl h
  | quasisimple h c => exact Or.inr (Or.inl ⟨h, ⟨c⟩⟩)
  | symmetricThree c => exact Or.inr (Or.inr ⟨c⟩)
  | twoFactors c => exact (not_twoFactors ρ hr ⟨c⟩).elim
  | outerSixThree c => exact (not_outerSixThree ρ hr ⟨c⟩).elim
  | hyperplane c => exact (not_hyperplane ρ hr ⟨c⟩).elim

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
