module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.CommonCenter
public import Theory.GroupTheory.CentralBinaryCentralizerCard
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The order-four equality case on the source quotient

The full fixed index sixteen is bounded above by the product of the two
centralizer indices. The first is at most four by the selected critical-pair
rank comparison. Binary commutator duality bounds the second by the order-four
actor. Equality therefore forces both indices to be four and identifies
C_{Uγ}(D_H) with Dγ. A nonzero commutator also puts the common center in U_H;
that containment is not an extra assumption.

This is the numerical equality calculation in F.9.16(2) at the actual
13.8.13 consumer. It reuses the proved universal binary pairing theorem;
the other F.9 geometry and offender-existence results remain upstream.
The literal quotient and relative centralizers are retained throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.16(2),
printed pp.323–324, and its five-primary application in 13.8.13, p.951.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]

/-- A centralizing subgroup lifts into the fixed-point preimage. -/
theorem StarAction.fixed_index_le_of_centralizes (a : StarAction H U Z)
    (B X : Subgroup G) (_hB : B ≤ H) (_hX : X ≤ U)
    (hc : ⁅X, B⁆ = ⊥) :
    (FixedPoints.subgroup (a.actors B) (U ⧸ Z.subgroupOf U)).index ≤ X.relIndex U := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let F := FixedPoints.subgroup (a.actors B) (U ⧸ Z.subgroupOf U)
  have hle : X.subgroupOf U ≤ F.comap q := by
    intro x hx b
    obtain ⟨s, hs, he⟩ := b.property
    change (b : MulAut _) (q x) = q x
    rw [← he]
    obtain ⟨h, hh, rfl⟩ := hs
    change a.action (QuotientGroup.mk' (pCore 2 H) h) (q x) = q x
    rw [a.conjugation]
    congr 1
    apply Subtype.ext
    have hcomm := (commutator_eq_bot_iff_le_centralizer.mp hc) hx (h : G) hh
    change (h : G) * (x : G) * (h : G)⁻¹ = x
    change (h : G) * (x : G) = (x : G) * (h : G) at hcomm
    rw [hcomm, mul_inv_cancel_right]
  have hi := Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := X.subgroupOf U)))
    (Subgroup.index_dvd_of_le hle)
  rw [F.index_comap_of_surjective (QuotientGroup.mk'_surjective _)] at hi
  exact hi

private theorem pairing_index (D B A : Subgroup G)
    [IsMulCommutative D] [IsMulCommutative A]
    (hAD : A ≤ D) (hc : ⁅D, B⁆ ≤ A) (hz : ⁅A, B⁆ ≤ ⊥)
    (hA : Nat.card A = 2) :
    (centralizer (B : Set G)).relIndex D = (centralizer (D : Set G)).relIndex B := by
  have hc := card_mul_card_centralizer_restrict_of_central_binary_pairing D B A hAD hc hz hA
  have hd := ((centralizer (B : Set G)).subgroupOf D).index_mul_card
  have hb := ((centralizer (D : Set G)).subgroupOf B).index_mul_card
  rw [← hd, ← hb] at hc
  have hp : 0 < Nat.card ((centralizer (B : Set G)).subgroupOf D) *
      Nat.card ((centralizer (D : Set G)).subgroupOf B) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hp
  change ((centralizer (B : Set G)).subgroupOf D).index * _ =
    ((centralizer (D : Set G)).subgroupOf B).index * _
  nlinarith only [hc]

/-- The F.9.16 equality calculation for the order-four source actor.
The fixed index is on the whole quotient. The centralizer equality and
placement of the center are conclusions, not inputs. -/
theorem rank_two_equality_case [IsElementaryAbelian 2 U]
    (a : StarAction H U Z) (B A : Subgroup G) [IsElementaryAbelian 2 B]
    (hB : B ≤ H) (hz : H ≤ normalizer (Z : Set G))
    (hk : Source.QH H = commutatorPreimage H U Z)
    (hAB : A ≤ B) (hA : Nat.card A = 2)
    (hnA : U ≤ normalizer (A : Set G))
    (hcross : ⁅Source.DH U B A, Source.Dgamma B U Z⁆ = ⊥)
    (hcomp : (Source.DH U B A).relIndex U ≤ (Source.Dgamma B U Z).relIndex B)
    (hactor : Nat.card (Source.starImage H B) = 4)
    (hfixed : (FixedPoints.subgroup (a.actors B) (U ⧸ Z.subgroupOf U)).index = 16) :
    A ≤ U ∧
    (Source.DH U B A).relIndex U = (Source.Dgamma B U Z).relIndex B ∧
    B ⊓ centralizer (Source.DH U B A : Set G) = Source.Dgamma B U Z := by
  let D := Source.DH U B A
  let K := Source.Dgamma B U Z
  have hDU : D ≤ U := commutatorPreimage_le _ _ _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDU
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAB
  have hK4 : K.relIndex B = 4 :=
    (dgamma_index_eq_star_card B hB hz hk).trans hactor
  have hD4 : D.relIndex U ≤ 4 := hcomp.trans_eq hK4
  have hcomm : ⁅D, B⁆ ≤ A := commutator_commutatorPreimage_le U B A hnA
  have hnD : B ≤ normalizer (D : Set G) :=
    commutatorPreimage_normalized U B A B hnA (hB.trans a.normalizes)
      le_normalizer ((hAB.trans B.le_centralizer |> le_centralizer_iff.mp).trans
        (centralizer_le_normalizer _))
  have hne : ⁅D, B⁆ ≠ ⊥ := by
    intro he
    have hi := a.fixed_index_le_of_centralizes B D hB hDU he
    rw [hfixed] at hi
    omega
  have hEA : ⁅D, B⁆ = A := by
    apply eq_of_le_of_card_ge hcomm
    have hd := card_dvd_of_le hcomm
    rw [hA] at hd
    have hp := (one_lt_card_iff_ne_bot _).mpr hne
    have he := (Nat.dvd_prime Nat.prime_two).mp hd
    omega
  have hAD : A ≤ D := hEA ▸ le_normalizer_iff_commutator_le_left.mp hnD
  have hAC : ⁅A, B⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    exact hAB.trans B.le_centralizer
  have hrec := pairing_index D B A hAD hcomm hAC hA
  let C := D ⊓ centralizer (B : Set G)
  let E := B ⊓ centralizer (D : Set G)
  have hKE : K ≤ E := le_inf (commutatorPreimage_le _ _ _)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross))
  have hE4 : E.relIndex B ≤ 4 :=
    (relIndex_le_of_le_left hKE (by omega)).trans_eq hK4
  have hCE : C.relIndex D = E.relIndex B := by
    rw [inf_relIndex_left, inf_relIndex_left]
    exact hrec
  have hi : 16 ≤ C.relIndex U := by
    rw [← hfixed]
    exact a.fixed_index_le_of_centralizes B C hB (inf_le_left.trans hDU)
      (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right)
  have hprod := relIndex_mul_relIndex C D U inf_le_left hDU
  rw [hCE] at hprod
  have hDexact : D.relIndex U = 4 := by nlinarith
  have hEexact : E.relIndex B = 4 := by nlinarith
  refine ⟨hAD.trans hDU, hDexact.trans hK4.symm, ?_⟩
  apply le_antisymm ?_ hKE
  apply relIndex_eq_one.mp
  have he := relIndex_mul_relIndex K E B hKE inf_le_left
  rw [hEexact, hK4] at he
  omega

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
