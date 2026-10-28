module

public import Theory.Representation.BinaryPermutation.FiveCentralExtension.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
import Mathlib.Tactic


/-!
# Offenders on a genuine natural S₅ quotient

The class-sum section gives additive fixed codimensions for the quotient and
kernel. The natural core has no strong offenders, so an offender fixes the
whole kernel. Every natural offender contains an odd permutation; together
with its prescribed A₅ fixation this makes the kernel trivial as an S₅-module.
Thus every fixed codimension and best-offender condition is the one on the
literal five-letter core, without assuming the original module has dimension four.

Source: Aschbacher–Smith, C.1.24 and E.2.3, printed pp.130–131 and 216–217.
-/

public section

namespace CFSG.Quasithin.ChapterC.SymmetricFive
open BinaryPermutation BinaryPermutation.FiveCentralExtension Representation.BinaryOffender
open ChapterB.Offenders
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
variable (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v)

private theorem core_rank_le {A : Subgroup Sym} (hA : IsElementaryTwo A) :
    rank A ≤ fixedCodim (coreRepresentation (Fin 5)) A :=
  Nat.le_of_not_gt (fun h => Odd.not_isStrongOffender_core (Or.inl rfl) A ⟨hA, h⟩)

private theorem caseAFamily_has_odd {A : Subgroup Sym} (hA : CaseAFamily 5 A) :
    ∃ a ∈ A, a.sign = -1 := by
  obtain ⟨m, hm, _, g, rfl⟩ := hA
  refine ⟨(MulAut.conj g) (pairSwap 5 0), Subgroup.mem_map_of_mem _ (pairSwap_mem 0 hm), ?_⟩
  change (g * (Equiv.swap (0 : Fin 5) 1) * g⁻¹).sign = -1
  simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1), mul_comm]

include hp he hk

theorem offender_kernel_fixed {A : Subgroup Sym} (hA : IsOffender ρ A) :
    (∀ v, p v = 0 → ∀ a ∈ A, ρ a v = v) ∧ CaseAFamily 5 A := by
  have hd := fixedCodim_split ρ p he hp hk A
  have hr := core_rank_le hA.1
  have ha := hA.2
  have hz : fixedCodim (kernelRepresentation ρ p he) A = 0 := by omega
  have heq : fixedCodim (coreRepresentation (Fin 5)) A = rank A := by omega
  have hbest := (isBestOffender_iff_of_not_strong (coreRepresentation (Fin 5))
    (fun h => by obtain ⟨B, hb⟩ := h; exact Odd.not_isStrongOffender_core (Or.inl rfl) B hb) A).mpr
      ⟨hA.1, heq⟩
  refine ⟨?_, (Odd.isBestOffender_core_iff_caseAFamily (Or.inl rfl) A).mp hbest⟩
  intro v hv a ha
  have hfix := (fixedCodim_eq_zero_iff (kernelRepresentation ρ p he) A).mp hz
  have hvfix : (⟨v, hv⟩ : p.ker) ∈ fixedSpace (kernelRepresentation ρ p he) A := by
    rw [hfix]; trivial
  exact congrArg Subtype.val (hvfix ⟨a, ha⟩)

/-- One offender forces the entire S₅ action to fix the prescribed kernel. -/
theorem kernel_fixed_of_ff (hff : IsFFModule ρ) :
    ∀ v, p v = 0 → ∀ g : Sym, ρ g v = v := by
  obtain ⟨A, hA⟩ := hff
  obtain ⟨hfix, hcase⟩ := offender_kernel_fixed ρ p hp he hk hA
  obtain ⟨a, ha, hasign⟩ := caseAFamily_has_odd hcase
  intro v hv g
  rcases Int.units_eq_one_or g.sign with hsg | hsg
  · exact hk v hv g (Equiv.Perm.mem_alternatingGroup.mpr hsg)
  · have hga : g * a⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsg, hasign]
      decide
    have hx := hk v hv (g * a⁻¹) hga
    calc
      ρ g v = ρ (g * a⁻¹) (ρ a v) := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      _ = v := by rw [hfix v hv a ha, hx]

theorem fixedCodim_eq_core_of_ff (hff : IsFFModule ρ) (A : Subgroup Sym) :
    fixedCodim ρ A = fixedCodim (coreRepresentation (Fin 5)) A := by
  rw [fixedCodim_split ρ p he hp hk]
  have hz : fixedCodim (kernelRepresentation ρ p he) A = 0 := by
    apply (fixedCodim_eq_zero_iff _ _).mpr
    apply top_unique
    intro v _ a
    exact Subtype.ext (kernel_fixed_of_ff ρ p hp he hk hff v v.property a)
  rw [hz, add_zero]

theorem isBestOffender_iff_caseA (hff : IsFFModule ρ) (A : Subgroup Sym) :
    IsBestOffender ρ A ↔ CaseAFamily 5 A :=
  (OddTransport.isBestOffender_iff_of_fixedCodim_eq ρ (coreRepresentation (Fin 5))
    (fixedCodim_eq_core_of_ff ρ p hp he hk hff) A).trans
      (Odd.isBestOffender_core_iff_caseAFamily (Or.inl rfl) A)
end CFSG.Quasithin.ChapterC.SymmetricFive
