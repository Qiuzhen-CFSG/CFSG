module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.SourceThompson

/-!
# Excluding singleton selections in the original 13.6.13 products

A selected singleton is a normal S₃ with a plane as its actual moved
space. The marked A₅ seed then makes that S₃ the whole star group. This
contradicts the nontrivial complementary factor in either native product
alternative. Thus the ordinary product case selects both S₃ residuals,
and the hyperplane alternative is impossible.

The source hypotheses retain the original Sylow, cubic quotient, and
marked action. The plane is constructed from the Sylow-fixed seed, not
assumed from the quotient-module list.
Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
open NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse

private theorem sourceFactor_nontrivial {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {A : Subgroup D} {U : Subrepresentation ρ} (h : SourceFactorCase ρ A U) :
    Nontrivial A := by
  rcases CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches.factor_structure (sourceFactor_model ρ h) with he | hq
  · obtain ⟨e⟩ := he
    exact e.surjective.nontrivial
  · let := hq.1.simple
    let : Nontrivial (solvableResidual A) :=
      (QuotientGroup.mk'_surjective (center (solvableResidual A))).nontrivial
    exact (solvableResidual A).subtype_injective.nontrivial

private theorem mapped_factor_ne_top {D : Type*} [Group D] [Finite D]
    (I : Subgroup D) (A B : Subgroup I) (h : InternalProduct A B)
    [Nontrivial B] : A.map I.subtype ≠ ⊤ := by
  intro he
  have hlt : Nat.card A < Nat.card I := by
    rw [h.card_eq]
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left
      (Finite.one_lt_card (α := B)) (Nat.card_pos (α := A))
  have hcard : Nat.card A = Nat.card D := by
    rw [← card_map_of_injective (K := A) I.subtype_injective, he]
    exact Nat.card_congr topEquiv.toEquiv
  have hle := Nat.card_le_card_of_injective I.subtype I.subtype_injective
  omega

private def swappedProduct {D : Type*} [Group D] {A B : Subgroup D}
    (h : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans h.equiv
  apply_eq b a := by
    change h.equiv (a, b) = (b : D) * a
    have hc := congrArg h.equiv (show (a, (1 : B)) * (1, b) = (1, b) * (a, 1) by simp)
    rw [map_mul, map_mul, h.apply_eq, h.apply_eq] at hc
    simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hc

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)

include S hS hfix hL hcubic hX

/-- In the source two-factor case, both factors are S₃ and the selected
minimal solvable group is their full two-residual. -/
theorem source_twoFactor_both_residuals
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    Nonempty (c.first ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (c.second ≃* Equiv.Perm (Fin 3)) ∧
      X.subgroupOf (FFFactors.offenderActor
        (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))) =
          pResidual 2 (FFFactors.offenderActor
            (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))) := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let I := FFFactors.offenderActor (starRepresentation z v)
  have hz := A5Module.markedZ_mem_Gv s
  rcases minimalSolvable_twoFactor_choice L T z v hz S hS hX c with
    ⟨⟨e⟩, hF⟩ | ⟨⟨e⟩, hF⟩ | hboth
  · let H := c.first.map I.subtype
    let : H.Normal := minimalSolvable_twoFactor_first_normal L T z v hz S hS hfix hX c e hF
    have hR := minimalSolvable_selected_residual L T z v hz S hS hX c.first hF
    have hXH : X ≤ H := hR.symm.le.trans (map_subtype_le _)
    have he := marked_normal_s3_eq_top s T S hS hfix hL hcubic hX.1 H
      ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hXH
      (Supports.minimalSolvable_twoFactor_first_moved_card L T z v hz S hS hfix hX c e hF)
    let : Nontrivial c.second := sourceFactor_nontrivial _ c.secondCase
    exact (mapped_factor_ne_top I c.first c.second c.product he).elim
  · let H := c.second.map I.subtype
    let : H.Normal := minimalSolvable_twoFactor_second_normal L T z v hz S hS hfix hX c e hF
    have hR := minimalSolvable_selected_residual L T z v hz S hS hX c.second hF
    have hXH : X ≤ H := hR.symm.le.trans (map_subtype_le _)
    have he := marked_normal_s3_eq_top s T S hS hfix hL hcubic hX.1 H
      ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hXH
      (Supports.minimalSolvable_twoFactor_second_moved_card L T z v hz S hS hfix hX c e hF)
    let : Nontrivial c.first := sourceFactor_nontrivial _ c.firstCase
    exact (mapped_factor_ne_top I c.second c.first (swappedProduct c.product) he).elim
  · exact hboth

/-- The native hyperplane case cannot occur in the original marked source
setup; its cubic selection would make the proper S₃ factor the whole actor. -/
theorem source_hyperplane_excluded
    (c : HyperplaneCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) : False := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let I := FFFactors.offenderActor (starRepresentation z v)
  let H := c.second.map I.subtype
  have hz := A5Module.markedZ_mem_Gv s
  obtain ⟨⟨e⟩, hF⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  let : H.Normal := minimalSolvable_hyperplane_second_normal L T z v hz S hS hfix hX c e hF
  have hR := minimalSolvable_selected_residual L T z v hz S hS hX c.second hF
  have hXH : X ≤ H := hR.symm.le.trans (map_subtype_le _)
  have he := marked_normal_s3_eq_top s T S hS hfix hL hcubic hX.1 H
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hXH
    (Supports.minimalSolvable_hyperplane_moved_card L T z v hz S hS hfix hX c)
  let : Nontrivial c.first := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_congr c.firstEquiv.toEquiv, Matrix.PSL3Two.card_SL]
    decide)
  exact mapped_factor_ne_top I c.second c.first (swappedProduct c.product) he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
