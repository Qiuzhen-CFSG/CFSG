module

public import Stellmacher.SectionOne.TwoFactorWreathRecognition
public import Stellmacher.LaterDefs
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Counting canonical factors above an order-nine odd core

If the odd core and the canonical one-seven product both supplement the
same Sylow two-subgroup, their cardinality formulas force exactly two
canonical factors. Unique maximality then gives the literal SL₂(2) wreath
product through the proved two-factor recognition theorem.

Canonical generation remains an explicit prerequisite here. No nontrivial
offender is inferred from the order-sixteen module or a relative double-SL₂
subgroup. This separates the counting step from that representation problem
in Stellmacher (9.1)(8), printed p.47, PDF page 37 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

open RankOneThreeGroupAssembly

private theorem canonical_product_card
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K) :
    Nat.card (oneSevenGenerated (G := K) (V := V)) =
      6 ^ (oneSevenFactors (G := K) (V := V)).card := by
  classical
  let F := oneSevenFactors (G := K) (V := V)
  let I := {D : Subgroup K // D ∈ F}
  let _ : Fintype I := Fintype.ofFinite I
  let D : I → Subgroup K := fun factor => factor.val
  have hprod := (oneSeven_global_product h R).2.1
  have hcomm : Pairwise fun first second =>
      ∀ x y : K, x ∈ D first → y ∈ D second → Commute x y := by
    intro first second hne x y hx hy
    exact hprod.2.2.2 first first.property second second.property
      (fun heq => hne (Subtype.ext heq)) x hx y hy
  have hD (factor : I) : IsSL2Two (D factor) :=
    ((mem_oneSevenFactors_iff _).mp factor.property).1
  have hind : iSupIndep D := Subgroup.iSupIndep_of_centerless_of_pairwise_commute D
    (fun factor => center_eq_bot_of_isSL2Two (hD factor)) hcomm
  rw [hprod.1]
  have hcard := Subgroup.natCard_iSup_of_iSupIndep D hcomm hind
  simpa [D, show Fintype.card I = F.card from Fintype.card_coe F,
    show ∀ factor : I, Nat.card (D factor) = 6 from
      fun factor => isSL2Two_card (hD factor)] using hcard

public theorem nineCore_two_factors_of_canonical_generation
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hoddcard : Nat.card (oddCore K) = 9)
    (hcanonical : oneE (V := V) (R : Subgroup K) ⊔ (R : Subgroup K) = ⊤) :
    (oneSevenFactors (G := K) (V := V)).card = 2 := by
  classical
  let W := oddCore K
  let E := oneSevenGenerated (G := K) (V := V)
  let F := oneSevenFactors (G := K) (V := V)
  let _ : W.Normal := pPrimeCore_normal
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h R
  let _ : E.Normal := hEnormal
  have hEgen : E ⊔ (R : Subgroup K) = ⊤ := by
    rwa [(oneSeven_global_identification h R).2] at hcanonical
  have hdis : Disjoint W (R : Subgroup K) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) W R
      (IsPGroup.of_card (p := 3) (n := 2) hoddcard) R.isPGroup'
  have hKcard : 9 * Nat.card R = Nat.card K := by
    have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes W
      (R : Subgroup K) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rw [show W ⊓ (R : Subgroup K) = ⊥ from hdis.eq_bot,
      hgen, hoddcard, Subgroup.card_bot,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toEquiv,
      one_mul] at hcard
    exact hcard
  have hEcard : Nat.card E = 6 ^ F.card := canonical_product_card h R
  have hcoord : Nat.card ((R : Subgroup K) ⊓ E : Subgroup K) = 2 ^ F.card :=
    (sl2_product_sylow_coordinates R E hEnormal F hprod
      (fun D hD => ((mem_oneSevenFactors_iff D).mp hD).1)).2.2.1
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes E
    (R : Subgroup K) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  rw [hEcard, inf_comm E, hcoord, hEgen,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toEquiv,
    ← hKcard, ← mul_assoc] at hcard
  have hnum : 6 ^ F.card = 2 ^ F.card * 9 :=
    Nat.mul_right_cancel (Nat.card_pos (α := R)) hcard
  have hthree : 3 ^ F.card = 9 := by
    rw [show 6 = 2 * 3 by norm_num, mul_pow] at hnum
    exact Nat.mul_left_cancel (pow_pos (by decide : 0 < 2) _) hnum
  exact Nat.pow_right_injective (by decide : 1 < 3)
    (hthree.trans (by norm_num : 9 = 3 ^ 2))

public theorem nineCore_wreath_of_canonical_generation
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hoddcard : Nat.card (oddCore K) = 9)
    (hcanonical : oneE (V := V) (R : Subgroup K) ⊔ (R : Subgroup K) = ⊤) :
    Nonempty (K ≃* Later.SL2TwoWreathC2) := by
  exact oneSeven_wreath_of_two_factors h R hcanonical hunique
    (nineCore_two_factors_of_canonical_generation h R hgen hoddcard hcanonical)

end Stellmacher.SectionOne
