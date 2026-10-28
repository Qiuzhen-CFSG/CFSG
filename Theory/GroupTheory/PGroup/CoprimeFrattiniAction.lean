module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupAction.Quotient

/-!
# Faithful coprime actions on Frattini quotients

An actor whose finite order is coprime to p acts faithfully on a finite
p-group's Frattini quotient whenever it acts faithfully on the group.
The automorphism-kernel theorem makes the kernel on the quotient a p-group;
its order also divides the actor order, so the kernel is trivial.

This is the coprime form of the Burnside basis-kernel theorem. Both the
supplied homomorphism and the canonical quotient action have interfaces.
-/

namespace MonoidHom

/-- A faithful coprime automorphism action remains faithful on the Frattini quotient. -/
public theorem injective_frattini_action_of_coprime
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    {p : ℕ} (hK : IsPGroup p K) (action : A →* MulAut K)
    (hfaith : Function.Injective action) (hcop : Nat.Coprime (Nat.card A) p) :
    Function.Injective ((Subgroup.quotientAut (frattini K)).comp action) := by
  let f := (Subgroup.quotientAut (frattini K)).comp action
  have hker : IsPGroup p f.ker :=
    (Subgroup.isPGroup_quotientAut_frattini_kernel hK).comap_of_injective action hfaith
  obtain ⟨n, hn⟩ := hker.exists_card_dvd_pow
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply Subgroup.card_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes (hcop.pow_right n)
    f.ker.card_subgroup_dvd_card hn

/-- The canonical quotient action of a faithful coprime actor is faithful. -/
public theorem faithfulSMul_frattini_of_coprime
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K] [FaithfulSMul A K]
    {p : ℕ} (hK : IsPGroup p K) (hcop : Nat.Coprime (Nat.card A) p) :
    letI : MulDistribMulAction A (K ⧸ frattini K) :=
      quotientMulDistribMulAction (frattini K) (isInvariant_of_characteristic (frattini K))
    FaithfulSMul A (K ⧸ frattini K) := by
  let : MulDistribMulAction A (K ⧸ frattini K) :=
    quotientMulDistribMulAction (frattini K) (isInvariant_of_characteristic (frattini K))
  let : MulAction.QuotientAction A (frattini K) :=
    quotientAction_of_isInvariant (frattini K) (isInvariant_of_characteristic (frattini K))
  have hi : Function.Injective (MulDistribMulAction.toMulAut A K) := by
    intro a b hab
    exact FaithfulSMul.eq_of_smul_eq_smul (fun k => DFunLike.congr_fun hab k)
  have hquot := injective_frattini_action_of_coprime hK _ hi hcop
  constructor
  intro a b hab
  apply hquot
  ext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (frattini K) q
  simp only [MonoidHom.comp_apply, Subgroup.quotientAut_apply_mk]
  change QuotientGroup.mk (a • k) = QuotientGroup.mk (b • k)
  exact hab (QuotientGroup.mk k)

end MonoidHom
