module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Inputs
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Removing the paired F.9.18 alternative for derived binary G₂

The six paired carriers have orders distinct from the already proved order
6048 of the actual derived G₂(2) group. The generic classical order formulas
suffice; no new finite enumeration or simplicity certificate is needed.

Source: Aschbacher–Smith F.9.18(4iii), printed p.325, used in 13.8.27, p.963.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

private theorem sl_card_mul (F : Type*) [Field F] [Finite F] (n : ℕ) [NeZero n] :
    Nat.card SL(n,F) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(n,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul n

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card SL(3,F) * (q-1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q^3-q = q*(q^2-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
  rw [h, h1, h2]
  ring

/-- The paired natural alternative of F.9.18(4iii) has no derived binary G₂ carrier. -/
theorem not_pairCarrier {D : Type*} [Group D]
    (e : D ≃* commutator (Atlas.G2.Model (ZMod 2))) : ¬ PairCarrier D := by
  have hc : Nat.card D = 6048 := (Nat.card_congr e.toEquiv).trans
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))
  intro h
  rcases h with ⟨n, _, ⟨f⟩⟩ | ⟨n, _, ⟨f⟩⟩ | ⟨f⟩ | ⟨f⟩ | ⟨f⟩ | ⟨f⟩
  · have hh := (Nat.card_congr f.toEquiv).symm.trans hc
    rw [sl_three_card] at hh
    let q := Nat.card (GaloisField 2 n)
    change q^3 * (q^3-1) * (q^2-1) = 6048 at hh
    by_cases hq : q ≤ 3
    · interval_cases q <;> norm_num at hh
    · have hle : 4^3 * (4^3-1) * (4^2-1) ≤ q^3 * (q^3-1) * (q^2-1) := by
        gcongr <;> omega
      omega
  · have hh := (Nat.card_congr f.toEquiv).symm.trans hc
    rw [Theory.SpecificGroups.SymplecticFour.card_sp] at hh
    let q := Nat.card (GaloisField 2 n)
    change q^4 * (q^2-1) * (q^4-1) = 6048 at hh
    by_cases hq : q ≤ 2
    · interval_cases q <;> norm_num at hh
    · have hle : 3^4 * (3^2-1) * (3^4-1) ≤ q^4 * (q^2-1) * (q^4-1) := by
        gcongr <;> omega
      omega
  · obtain ⟨f⟩ := f
    have hh := (Nat.card_congr f.toEquiv).symm.trans hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh
  · obtain ⟨f⟩ := f
    have hh := sl_card_mul (ZMod 2) 4
    rw [← Nat.card_congr f.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · obtain ⟨f⟩ := f
    have hh := sl_card_mul (ZMod 2) 5
    rw [← Nat.card_congr f.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · obtain ⟨f⟩ := f
    have hh := (Nat.card_congr f.toEquiv).symm.trans hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
