module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.PrimeOrder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.OuterBranch

/-!
# Fitting-commutator generation in the small FF branches

The trivial two-core makes the Fitting subgroup odd. In the S₃ branch its
order therefore divides three. In the outer A₆–C₃ branch, oddness puts it
in O²(N)=A₆×C₃, and the component centralizes it, so it lies in C₃.
The prime-order argument then applies to the actual Thompson marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(2),(4), printed p.105; paragraph after 13.6.13, printed p.929.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
variable {D : Type*} [Group D] [Finite D]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) D V)

theorem fitting_coprime_two (hcore : pCore 2 D = ⊥) :
    Nat.Coprime 2 (Nat.card (fittingSubgroup D)) :=
  (pPrimeCore_coprime_card (p := 2) (G := D)).of_dvd_right
    (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))

theorem symmetric_fitting_card (c : SymmetricThreeCase ρ)
    (hcore : pCore 2 D = ⊥) : Nat.card (fittingSubgroup D) ∣ 3 := by
  have hc : Nat.card D = 2 * 3 := by
    rw [Nat.card_congr c.equiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  apply (fitting_coprime_two hcore).symm.dvd_of_dvd_mul_left
  exact hc ▸ (fittingSubgroup D).card_subgroup_dvd_card

theorem outer_fitting_le (c : OuterSixThreeCase ρ)
    (hg : offenderSubgroup ρ = ⊤) (hcore : pCore 2 D = ⊥) :
    fittingSubgroup D ≤ c.second := by
  have hFP : fittingSubgroup D ≤ c.first ⊔ c.second := by
    rw [← OuterBranch.residual_eq_product c hg]
    intro x hx
    exact mem_pResidual_of_orderOf_coprime
      ((fitting_coprime_two hcore).of_dvd_right ((fittingSubgroup D).orderOf_dvd_natCard hx))
  have hCF : c.first ≤ centralizer (fittingSubgroup D : Set D) :=
    component_centralizes_of_le_normalizer _ _ (OuterBranch.first_component c)
      (by rw [normalizer_eq_top]; exact le_top)
  have hFC : fittingSubgroup D ≤ centralizer (c.first : Set D) :=
    le_centralizer_iff.mp hCF
  intro x hx
  let xP : ↥(c.first ⊔ c.second : Subgroup D) := ⟨x, hFP hx⟩
  let a : c.first := (c.product.symm xP).1
  let b : c.second := (c.product.symm xP).2
  have he : (a : D) * (b : D) = x := by
    simpa only [a, b, c.product_apply] using congrArg Subtype.val (c.product.apply_symm_apply xP)
  have ha : a ∈ center c.first := by
    apply mem_center_iff.mpr
    intro y
    have hc := mem_centralizer_iff.mp (hFC hx) (y : D) y.property
    have hyp : c.product (y, 1) = (⟨y, (le_sup_left : c.first ≤ c.first ⊔ c.second) y.property⟩ : ↥(c.first ⊔ c.second : Subgroup D)) := by
      apply Subtype.ext
      simp only [c.product_apply, Subgroup.coe_one, mul_one]
    have hh : xP * c.product (y, 1) = c.product (y, 1) * xP := by
      apply Subtype.ext
      simpa only [hyp, Subgroup.coe_mul] using hc.symm
    have hh' := congrArg (fun u => (c.product.symm u).1) hh
    simpa only [map_mul, Prod.fst_mul, c.product.symm_apply_apply, a] using hh'.symm
  have haz : a = 1 := by
    have hz := (centerCongr c.firstEquiv ⟨a, ha⟩).property
    change c.firstEquiv a ∈ center (alternatingGroup (Fin 6)) at hz
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
    exact c.firstEquiv.map_eq_one_iff.mp hz
  rw [haz, Subgroup.coe_one, one_mul] at he
  exact he ▸ b.property

theorem outer_fitting_card (c : OuterSixThreeCase ρ)
    (hg : offenderSubgroup ρ = ⊤) (hcore : pCore 2 D = ⊥) :
    Nat.card (fittingSubgroup D) ∣ 3 := by
  have hc : Nat.card c.second = 3 := by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    exact Nat.card_zmod 3
  exact hc ▸ card_dvd_of_le (outer_fitting_le ρ c hg hcore)

variable {G : Type*} [Group G] [Finite G]

/-- The symmetric-three source branch, applied to the actual Thompson image. -/
theorem thompson_generation_of_symmetricThree
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : SymmetricThreeCase (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) :=
  thompson_generation_of_fitting_card_dvd_prime T z v (by exact hSyl) (by decide : Nat.Prime 3)
    (symmetric_fitting_card _ c (JGstar_twoCore z v hcore))

/-- The nonsplit outer source branch, with offender generation proved for
this action rather than assumed as an extra premise. -/
theorem thompson_generation_of_outerSixThree
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : OuterSixThreeCase (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) :=
  thompson_generation_of_fitting_card_dvd_prime T z v hSyl (by decide : Nat.Prime 3)
    (outer_fitting_card _ c (thompsonRepresentation_generated z v hz)
      (JGstar_twoCore z v hcore))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
