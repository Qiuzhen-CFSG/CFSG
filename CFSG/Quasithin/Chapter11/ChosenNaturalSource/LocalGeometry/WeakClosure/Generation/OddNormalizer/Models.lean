module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry
public import Theory.Quasithin.CoprimeRank
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order

/-!
# Exclusion of the actual exceptional odd-normalizer quotients

A prime dividing q-1 has rank two in the actual source Cartan, and quotienting
by O2(L) preserves this odd rank. This excludes every binary PSL2 group.
The full natural groups have order at least 60480; the remaining exceptional
quotients in 4.4.3 have smaller orders. The calculation includes SL3(4) with
its center, the triple cover of A6 with center of order three, and the literal
projective unitary group with arbitrary Hermitian form. The equivalence
version applies directly to the inclusion-induced covering quotients.

Source: Aschbacher--Smith, 4.4.3(2), printed p.619, with 11.0.2, p.759.
The imported classical-group order proofs retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem exists_odd_rank_two : ∃ p : ℕ, p.Prime ∧ Odd p ∧
    2 ≤ primeRank p (L ⧸ pCore 2 L) := by
  have hq : 4 ≤ 2 ^ S.field.degree := Nat.pow_le_pow_right (n := 2) (by decide) S.nonbinary
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ S.field.degree - 1 ≠ 1 by omega)
  have ho : Odd p := by
    apply hp.odd_of_ne_two
    rintro rfl
    have he : 2 ∣ 2 ^ S.field.degree :=
      dvd_pow_self 2 (Nat.ne_of_gt S.field.degree_pos)
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨X,hX⟩ := exists_cartan D
  have hr := (coordinates D S).cartan_primeRank hX hp hd
  have hi := Theory.GroupTheory.primeRank_le_of_injective p (inclusion (hX.1.trans inf_le_left))
    (inclusion_injective (hX.1.trans inf_le_left))
  refine ⟨p,hp,ho,?_⟩
  rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup]
  exact hr.ge.trans hi

theorem not_binary_rank_one (n : ℕ) :
    ¬ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) := by
  obtain ⟨p,hp,ho,hr⟩ := exists_odd_rank_two D S
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨F,hF,hfin,hcard,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hle : primeRank p (L ⧸ pCore 2 L) ≤ 1 := by
    rw [primeRank_equiv p (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)]
    exact Matrix.SL2.binary_odd_primeRank_le_one ho
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem card_sl_three {F : Type*} [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  have hs : Nat.card SL(3,F) = Nat.card PSL(3,F) * Nat.gcd 3 (q - 1) := by
    simpa only [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] using
      card_eq_card_quotient_mul_card_subgroup (center SL(3,F))
  rw [← hs] at hc
  simp only [Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    Nat.reduceAdd, pow_one, Fin.prod_univ_zero, mul_one] at hc
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_succ]
  have he : Nat.card SL(3,F) * (q - 1) =
      (q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) := by
    calc
      _ = (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := hc
      _ = _ := by rw [h1,h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega) he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The full SL3 center is retained in the least order, 60480 at q=4. -/
theorem quotient_card_ge : 60480 ≤ Nat.card (L ⧸ pCore 2 L) := by
  have hq : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (n := 2) (by decide) S.nonbinary
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv, card_sl_three]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  | sp4 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp]
    have hb := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
    exact le_trans (by decide : 60480 ≤ 4 ^ 4 * (4 ^ 2 - 1) * (4 ^ 4 - 1)) hb
  | g2 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv, Atlas.G2.card_Model]
    have hb := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    exact le_trans (by decide : 60480 ≤ 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1)) hb

/-- The quotient list in 4.4.3(2), including the actual triple covering group. -/
@[expose] def ExceptionalQuotient (Q : Type*) [Group Q] : Prop :=
  (∃ n : ℕ, ClassicalGroup.IsPSL Q 2 (2 ^ n)) ∨
  ClassicalGroup.IsPSL Q 3 2 ∨ ClassicalGroup.IsPSL Q 4 2 ∨
  Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
  (IsQuasisimple Q ∧ Nat.card (center Q) = 3 ∧
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6))) ∨
  ClassicalGroup.IsPSU Q 3 3

theorem not_exceptional_of_equiv {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* (L ⧸ pCore 2 L)) : ¬ ExceptionalQuotient Q := by
  have hsize : 60480 ≤ Nat.card Q := by
    rw [Nat.card_congr e.toEquiv]
    exact quotient_card_ge D S
  rintro (⟨n,hn⟩ | h3 | h4 | h6 | h7 | hhat | hu)
  · obtain ⟨F,hF,hfin,hcard,⟨f⟩⟩ := hn
    exact not_binary_rank_one D S n ⟨F,hF,hfin,hcard,⟨e.symm.trans f⟩⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h3
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [Nat.card_congr e.toEquiv,hc] at hsize
    omega
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h4
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [Nat.card_congr e.toEquiv,hc] at hsize
    omega
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hsize
    norm_num at hsize
  · obtain ⟨e⟩ := h7
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hsize
    norm_num at hsize
  · obtain ⟨_,hz,⟨e⟩⟩ := hhat
    rw [card_eq_card_quotient_mul_card_subgroup (center Q),hz,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hsize
    norm_num at hsize
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hu
    rw [Nat.card_congr e.toEquiv,
      BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
        J hF hconj] at hsize
    norm_num at hsize

/-- No exceptional quotient from 4.4.3 occurs in the nonbinary natural rows. -/
theorem not_exceptional : ¬ ExceptionalQuotient (L ⧸ pCore 2 L) :=
  not_exceptional_of_equiv D S (MulEquiv.refl _)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
