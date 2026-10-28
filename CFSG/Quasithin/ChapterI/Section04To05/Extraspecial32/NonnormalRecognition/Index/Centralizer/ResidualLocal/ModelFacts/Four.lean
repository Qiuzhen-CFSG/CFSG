module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelFacts.Blocks

/-!
# The four-point residual and marked centralizer

Every even permutation of four points is a product of two elements whose
cubes are one. Thus A₄ has no nontrivial two-group quotient. Direct checks
on its twelve elements give its single involution class and the exponent-two
centralizer of order four. These checks use kernel reduction, and feed the
actual supported A₄ inside the marked eight-point centralizer.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38.
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel
abbrev Four := alternatingGroup (Fin 4)
def fourInvolution : Four := ⟨fourMark, by simp [fourMark, mem_alternatingGroup]⟩

theorem four_card : Nat.card Four = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem four_odd_factorization : ∀ a : Four, ∃ b c : Four,
    b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ b * c = a := by decide +kernel

theorem four_residual : pResidual 2 Four = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨b, c, hb, hc, rfl⟩ := four_odd_factorization a
  exact (pResidual 2 Four).mul_mem
    (mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hb)))
    (mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc)))

theorem four_involution_order : orderOf fourInvolution = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem four_involution_fusion (a : Four) (ha : orderOf a = 2) :
    IsConj a fourInvolution := by
  have hall : ∀ a : Four, a ^ 2 = 1 → a ≠ 1 →
      ∃ b : Four, b * a * b⁻¹ = fourInvolution := by decide +kernel
  apply isConj_iff.mpr
  exact hall a (ha ▸ pow_orderOf_eq_one a) (fun h => by simp [h] at ha)

abbrev FourCentralizer := centralizer ({fourInvolution} : Set Four)
instance fourCentralizerDecidable : DecidablePred (· ∈ FourCentralizer) := fun a =>
  decidable_of_iff (a * fourInvolution = fourInvolution * a)
    mem_centralizer_singleton_iff.symm

theorem fourCentralizer_card : Nat.card FourCentralizer = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem fourCentralizer_squares : ∀ a : FourCentralizer, a ^ 2 = 1 := by decide +kernel

theorem fourCentralizer_equiv : Nonempty (FourCentralizer ≃* DihedralGroup 2) := by
  let a : FourCentralizer := ⟨fourInvolution, mem_centralizer_singleton_iff.mpr rfl⟩
  have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans four_involution_order
  let : IsKleinFour FourCentralizer :=
    ⟨fourCentralizer_card, Nat.dvd_antisymm
      (Monoid.exponent_dvd_of_forall_pow_eq_one fourCentralizer_squares)
      (ha ▸ Monoid.order_dvd_exponent a)⟩
  exact IsKleinFour.nonempty_mulEquiv
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.ResidualModel

end
