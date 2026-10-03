module

public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# Involution points of a Frattini quotient

The nonidentity Frattini cosets admitting square-one representatives are
invariant under every automorphism. Restricting an automorphism action to
these points preserves its kernel whenever the points generate the quotient.
For a self-centralizing two-core this kernel is the core itself.

This isolates the action-theoretic part of the five-point outer action of
an extraspecial group of minus type and order 32, used in Janko–Thompson,
Math. Z. 113 (1970), printed p.389.
-/

namespace Subgroup

/-- Nonidentity Frattini cosets represented by elements whose square is one. -/
public def frattiniInvolutionPoints (P : Type*) [Group P] : Set (P ⧸ frattini P) :=
  {v | v ≠ 1 ∧ ∃ x : P, x ^ 2 = 1 ∧ QuotientGroup.mk' (frattini P) x = v}

@[simp] public theorem mem_frattiniInvolutionPoints
    {P : Type*} [Group P] (v : P ⧸ frattini P) :
    v ∈ frattiniInvolutionPoints P ↔
      v ≠ 1 ∧ ∃ x : P, x ^ 2 = 1 ∧ QuotientGroup.mk' (frattini P) x = v := Iff.rfl

/-- Every automorphism preserves the intrinsic involution points. -/
public theorem quotientAut_mem_frattiniInvolutionPoints_iff
    {P : Type*} [Group P] (a : MulAut P) (v : P ⧸ frattini P) :
    quotientAut (frattini P) a v ∈ frattiniInvolutionPoints P ↔
      v ∈ frattiniInvolutionPoints P := by
  have forward (a : MulAut P) (v : P ⧸ frattini P)
      (hv : v ∈ frattiniInvolutionPoints P) :
      quotientAut (frattini P) a v ∈ frattiniInvolutionPoints P := by
    obtain ⟨hne, x, hx, rfl⟩ := hv
    refine ⟨fun h => hne ((quotientAut (frattini P) a).map_eq_one_iff.mp h),
      a x, ?_, ?_⟩
    · rw [← map_pow, hx, map_one]
    · exact (quotientAut_apply_mk (frattini P) a x).symm
  refine ⟨fun hv => ?_, forward a v⟩
  have h := forward a⁻¹ _ hv
  simpa only [map_inv, MulAut.inv_apply_self] using h

/-- The permutation action induced on the intrinsic involution points. -/
public def frattiniInvolutionPointAction
    {A P : Type*} [Group A] [Group P] (action : A →* MulAut P) :
    A →* Equiv.Perm (frattiniInvolutionPoints P) where
  toFun a := Equiv.Perm.subtypePerm (quotientAut (frattini P) (action a)).toEquiv
    (quotientAut_mem_frattiniInvolutionPoints_iff (action a))
  map_one' := by
    apply Equiv.Perm.ext
    intro v
    apply Subtype.ext
    change quotientAut (frattini P) (action 1) v = v
    simp
  map_mul' a b := by
    apply Equiv.Perm.ext
    intro v
    apply Subtype.ext
    change quotientAut (frattini P) (action (a * b)) v =
      quotientAut (frattini P) (action a) (quotientAut (frattini P) (action b) v)
    rw [map_mul, map_mul]
    rfl

@[simp] public theorem frattiniInvolutionPointAction_apply
    {A P : Type*} [Group A] [Group P] (action : A →* MulAut P)
    (a : A) (v : frattiniInvolutionPoints P) :
    (frattiniInvolutionPointAction action a v : P ⧸ frattini P) =
      quotientAut (frattini P) (action a) v := by rfl

/-- Fixing generating involution points is equivalent to fixing the quotient. -/
public theorem frattiniInvolutionPointAction_kernel
    {A P : Type*} [Group A] [Group P] (action : A →* MulAut P)
    (hgen : closure (frattiniInvolutionPoints P) = ⊤) :
    (frattiniInvolutionPointAction action).ker =
      ((quotientAut (frattini P)).comp action).ker := by
  ext a
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro v hv
    exact congrArg (fun e : Equiv.Perm (frattiniInvolutionPoints P) =>
      (e ⟨v, hv⟩ : P ⧸ frattini P)) h
  · intro h
    apply Equiv.Perm.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun h (v : P ⧸ frattini P)

/-- A generating set of n involution points gives an n-point action whose
kernel is the self-centralizing two-core. -/
public theorem pCore_exists_perm_action_of_frattiniInvolutionPoints
    {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (frattiniInvolutionPoints (pCore 2 K)) = n)
    (hgen : closure (frattiniInvolutionPoints (pCore 2 K)) = ⊤) :
    ∃ f : K →* Equiv.Perm (Fin n), f.ker = pCore 2 K := by
  let action := frattiniInvolutionPointAction
    (MulAut.conjNormal : K →* MulAut (pCore 2 K))
  let e := Finite.equivFinOfCardEq hcard
  refine ⟨e.permCongrHom.toMonoidHom.comp action, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective]
  exact (frattiniInvolutionPointAction_kernel _ hgen).trans
    (pCore_frattini_action_kernel 2 hcentral)

end Subgroup
