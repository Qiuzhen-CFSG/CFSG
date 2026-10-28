module
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.InvertedPrimeLift
public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.AllPrimes
public import Theory.SpecificGroups.PSU3.OddInvolutionRoot

/-!
# Inverted defining-prime roots in odd unitary central covers

The marked Sylow fixer descends through the literal central quotient to
PSU₃(p). Its pointwise Sylow fixation forces innerness for every odd prime,
and an inner involution inverts a root of order p. Pointwise fixation of
the original covering center lifts that root without changing its order
or its prescribed inverter.

This supplies the unitary parameter restriction in the original component
argument of Aschbacher--Smith 12.6.26, printed p.832; the root calculation
is E.2.17, printed p.230. No splitting of the covering center is assumed.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
variable {B F : Type*} [Group B] [Finite B] [Group.IsPerfect B]
  [IsSimpleGroup (B ⧸ center B)] [Field F] [Finite F]

/-- The same Sylow fixer inverts an element of defining-prime order upstairs. -/
theorem sylow_fixer_inverts_prime_of_fixes_center
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : B ⧸ center B ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (a : MulAut B) (ha : orderOf a = 2)
    (P : Sylow 2 B) (hP : ∀ x ∈ P, a x = x)
    (hZ : ∀ x ∈ center B, a x = x) :
    ∃ x : B, orderOf x = p ∧ a x = x⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv _ e.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (center B)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
      (by decide) (by simpa using hF) (by simpa using hc)
  let b := MulAut.centralQuotientAction e a
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans ha
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e a P hP
  obtain ⟨t,ht⟩ := inner_of_involutive_fixing_sylow J hp ho hF hfixed Q b
    (hb ▸ pow_orderOf_eq_one b) hQ
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top with hz|hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  have htc : orderOf t = 2 := by
    have hi := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
    exact (orderOf_injective MulAut.conj hi t).symm.trans (ht ▸ hb)
  have hp2 : p ≠ 2 := by
    have := Nat.odd_iff.mp ho
    omega
  obtain ⟨y,hy,hi⟩ := OddInvolutionRoot.exists_inverted_root J hp hp2 hF hc t htc
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  apply MulAut.exists_inverted_prime_of_fixed_kernel a b f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun x => (MulAut.centralQuotientAction_apply e a x).symm)
    (ha ▸ pow_orderOf_eq_one a) ?_ hp ho y hy ?_
  · intro x hx
    apply hZ x
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    exact hx.trans e.map_one.symm
  · rw [ht]
    exact hi
end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
