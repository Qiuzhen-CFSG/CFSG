module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Odd prime-power symplectic actors are inner times field actors

An odd prime-power actor acts trivially on the two parabolic classes.
The proved semilinear classification then gives an inner–field expression.
The field action injects into the actual outer quotient, so its order is
itself a power of the same prime. This is the concrete reduction required
by Aschbacher–Smith A.3.18, printed pp.51–53.
-/

public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.OddFieldActors
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {p : ℕ}

theorem inner_field_of_primePower (hF : 2 < Nat.card F) (ho : Odd p)
    (a : MulAut (Sp F)) {m : ℕ} (ha : a ^ (p^m) = 1) :
    ∃ (g : Sp F) (σ : F ≃+* F), a = MulAut.conj g * fieldAutomorphism σ ∧ σ ^ (p^m) = 1 := by
  let ρ := parabolicClassAction hF
  have hc : Nat.card (Equiv.Perm (parabolicClasses hF)) ∣ 2 := by
    let := Fintype.ofFinite (parabolicClasses hF)
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    have hh : Fintype.card (parabolicClasses hF) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF
    simpa using Nat.factorial_dvd_factorial hh
  have hd2 : orderOf (ρ a) ∣ 2 := (_root_.orderOf_dvd_natCard _).trans hc
  have hdp : orderOf (ρ a) ∣ p^m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,ha,map_one])
  have hρ : ρ a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr ho).pow_right m) hd2 hdp)
  have hpres : PreservesDiagram a := (mem_parabolicClassAction_ker_iff hF a).mp hρ
  obtain ⟨g,σ,he⟩ := SemilinearClassification.inner_field_of_preservesDiagram a hpres
  refine ⟨g,σ,he,?_⟩
  let π := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  have hi : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  have hs : outerFieldHom σ = π a := by
    change π (fieldAutomorphism σ) = π a
    rw [he,map_mul,hi,one_mul]
  apply InvolutionNormalForms.outerFieldHom_injective
  rw [map_pow,hs,← map_pow,ha,map_one,map_one]

end Theory.SpecificGroups.SymplecticFour.OddFieldActors
