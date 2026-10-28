module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import Theory.GroupAction.NormalTwoSubgroupInversion
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Inversion on the odd residual of the star quotient

For a solvable minimal parabolic, a Sylow-normalized subgroup whose image
modulo the two-core has order two has the same image size in H/J. Its
nonidentity image inverts the elementary odd residual: its fixed subgroup
is invariant under the Sylow, so irreducibility and the trivial two-core
force that fixed subgroup to be trivial. Pullback retains the actual
normal-core kernel J.

This supplies the inversion step of Aschbacher–Smith 12.2.21, printed
p.802, using B.6.8. LocalConfigurationCyclicConstructionSelectionInversion
transports the result to the original odd subgroup and its Frattini quotient.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- Every element outside O₂(H) in the specified order-two image inverts
the literal residual of H/J. No invariant odd Sylow is assumed. -/
theorem minimalParabolic_solvable_inverts_star_residual
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (V : Subgroup H) (hVT : V ≤ T) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hc : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 2)
    (v : H) (hv : v ∈ V) (hvQ : v ∉ pCore 2 H) :
    ∀ x ∈ pResidual 2 H, v * x * v⁻¹ * x ∈ minimalParabolicCore T hP := by
  let J := minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let R := pResidual 2 (H ⧸ J)
  let E := V.map q
  let T' := minimalParabolicStarSylow T hP
  obtain ⟨p, hp, ho, he, hir, _⟩ := minimalParabolic_solvable_star_structure T hP hs
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p R := he
  have hJQ : J ⊓ V = pCore 2 H ⊓ V := by
    calc
      J ⊓ V = ((T : Subgroup H) ⊓ J) ⊓ V := by
        rw [inf_assoc, inf_eq_right.mpr (inf_le_right.trans hVT)]
      _ = pCore 2 H ⊓ V := by rw [minimalParabolic_sylow_inf_core]
  have hEcard : Nat.card E = 2 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', ← inf_relIndex_right (H := J) (K := V),
      hJQ, inf_relIndex_right]
    rw [← relIndex_ker, QuotientGroup.ker_mk'] at hc
    exact hc
  have hEV : q v ≠ 1 := by
    intro hh
    have hvJ := (QuotientGroup.eq_one_iff v).mp hh
    have hh' : v ∈ pCore 2 H ⊓ V := hJQ ▸ (show v ∈ J ⊓ V from ⟨hvJ, hv⟩)
    exact hvQ hh'.1
  have hT'E : (T' : Subgroup (H ⧸ J)) ≤ normalizer (E : Set (H ⧸ J)) := by
    rw [minimalParabolicStarSylow_coe]
    rintro _ ⟨t, ht, rfl⟩
    exact (V.le_normalizer_map q) (mem_map_of_mem q (hTV ht))
  have hcore : pCore 2 (H ⧸ J) = ⊥ :=
    minimalParabolic_quotient_twoCore_eq_bot_of_kernel T hP J
      (normalCore_le _) (minimalParabolicTwoCore_le_core T hP)
  have hir' : ∀ B : Subgroup (H ⧸ J), B ≤ R →
      (T' : Subgroup (H ⧸ J)) ≤ normalizer (B : Set (H ⧸ J)) → B = ⊥ ∨ B = R := by
    intro B hBR hTB
    apply hir.2.2 B bot_le hBR
    intro t b hb
    exact (mem_normalizer_iff.mp (hTB t.property) b).mp hb
  obtain ⟨w, hw⟩ := exists_inverter_of_card_two R T' E
    (pResidual_sup_sylow_eq_top T') hT'E hEcard hcore hir'
  have hw1 : (w : H ⧸ J) ≠ 1 := by
    intro hw1
    apply hir.2.1
    apply le_antisymm bot_le
    intro a ha
    have hi : a = a⁻¹ := by simpa only [hw1, one_mul, inv_one, mul_one] using hw a ha
    have hsquare : a ^ 2 = 1 := by
      calc a ^ 2 = a⁻¹ * a := by rw [pow_two]; exact congrArg (fun b => b * a) hi
           _ = 1 := inv_mul_cancel a
    have hao : Odd (orderOf a) := by
      have hh := (IsElementaryAbelian.isPGroup p R).orderOf_coprime ho.coprime_two_right
        (⟨a, ha⟩ : R)
      rw [← Subgroup.orderOf_coe] at hh
      exact Nat.coprime_two_right.mp hh
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hao.coprime_two_right
      dvd_rfl (orderOf_dvd_of_pow_eq_one hsquare))
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hEcard
  have hvw : q v = (w : H ⧸ J) := congrArg Subtype.val
    ((hz ⟨q v, mem_map_of_mem q hv⟩ (fun hh => hEV (congrArg Subtype.val hh))).trans
      (hz w (fun hh => hw1 (congrArg Subtype.val hh))).symm)
  intro x hx
  have hxR : q x ∈ R := map_pResidual_le 2 q (mem_map_of_mem q hx)
  apply (QuotientGroup.eq_one_iff _).mp
  change q (v * x * v⁻¹ * x) = 1
  simp only [map_mul, map_inv, hvw, hw _ hxR, inv_mul_cancel]
end CFSG.Quasithin.ChapterB
