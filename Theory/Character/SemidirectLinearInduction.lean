module

public import Theory.Character.AbelianLinearCharacters
public import Theory.Character.NilpotentBrauerIdeal
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Inducing linear characters of a semidirect factor

For finite groups `N` and `H`, a linear character of `N` induces an actual
character of `N ⋊[α] H`. Its values on `N` are the sum of its `H`-orbit and
its values outside `N` vanish. Frobenius reciprocity and linear-character
orthogonality identify the inner product of two induced characters with the
number of matching orbit elements. Thus a free orbit gives an irreducible
character, and distinct free orbits give distinct induced characters.

No commutativity or elementwise fixed-point-free hypothesis is needed.
Source: standard character induction and Frobenius reciprocity; the application
motivating this interface is Lyons (1972), Lemma 4, p. 381
(`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`).
-/

public section
noncomputable section
open scoped BigOperators
namespace SemidirectLinearInduction
variable {N H : Type*} [Group N] [Group H] (α : H →* MulAut N)

/-- The embedded normal factor, from which the character is induced. -/
abbrev kernel : Subgroup (N ⋊[α] H) := (SemidirectProduct.inl : N →* N ⋊[α] H).range

/-- The canonical isomorphism from `N` onto the range of `inl`. -/
def kernelEquiv : N ≃* kernel α := MonoidHom.ofInjective SemidirectProduct.inl_injective

/-- The inverse of the canonical isomorphism extracts the left coordinate. -/
lemma kernelEquiv_symm_apply (x : kernel α) : (kernelEquiv α).symm x = x.val.left := by
  have h := MonoidHom.apply_ofInjective_symm SemidirectProduct.inl_injective x
  exact congrArg SemidirectProduct.left h

/-- Membership in the normal factor is detected by the right coordinate. -/
lemma mem_kernel (x : N ⋊[α] H) : x ∈ kernel α ↔ x.right = 1 := by
  rw [kernel, SemidirectProduct.range_inl_eq_ker_rightHom]
  rfl

/-- Transport a linear character to the embedded normal factor. -/
def kernelCharacter (θ : N →* ℂ) : kernel α →* ℂ :=
  θ.comp (kernelEquiv α).symm.toMonoidHom

/-- The transported character evaluates on the left coordinate. -/
lemma kernelCharacter_apply (θ : N →* ℂ) (x : kernel α) :
    kernelCharacter α θ x = θ x.val.left := by
  simp [kernelCharacter, kernelEquiv_symm_apply]

variable [Finite N] [Finite H]
local instance finiteSemidirectProduct : Finite (N ⋊[α] H) :=
  Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm
attribute [local instance] Fintype.ofFinite Classical.propDecidable

/-- The genuine character induced from the transported linear character of `N`. -/
def induced (θ : N →* ℂ) : ConjClassFunction (N ⋊[α] H) :=
  toConjClassFunction (inducedClassFunction (kernel α) (kernelCharacter α θ))
    (inducedClassFunction_isClassFunction _ _)

/-- The construction is ordinary induction from `inl.range`. -/
lemma induced_eq_induction (θ : N →* ℂ) (x : N ⋊[α] H) :
    induced α θ (ConjClasses.mk x) =
      inducedClassFunction (kernel α) (kernelCharacter α θ) x := by
  rfl

omit [Finite N] [Finite H] in
private lemma conj_mem (x y : N ⋊[α] H) :
    y⁻¹ * x * y ∈ kernel α ↔ x.right = 1 := by
  rw [mem_kernel]
  simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  simpa using (conj_eq_one_iff (a := y.right⁻¹) (b := x.right))

omit [Finite N] [Finite H] in
private lemma conj_value (θ : N →* ℂ) (x y : N ⋊[α] H) (hx : x.right = 1) :
    θ (y⁻¹ * x * y).left = θ (α y.right⁻¹ x.left) := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    SemidirectProduct.mul_right, SemidirectProduct.inv_right, hx, mul_one,
    map_mul]
  have hn : θ (α y.right⁻¹ y.left) ≠ 0 := by
    exact (isUnit_iff_ne_zero.mp ((Group.isUnit _).map θ))
  simp only [map_inv] at hn ⊢
  rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]

/-- The induced character is the orbit sum on `N` and vanishes outside `N`. -/
lemma induced_apply [Fintype H] [DecidableEq H] (θ : N →* ℂ) (x : N ⋊[α] H) :
    induced α θ (ConjClasses.mk x) =
      if x.right = 1 then ∑ a : H, θ (α a x.left) else 0 := by
  rw [induced_eq_induction]
  by_cases hx : x.right = 1
  · rw [if_pos hx]
    unfold inducedClassFunction
    trans (Nat.card (kernel α) : ℂ)⁻¹ * ∑ y : N ⋊[α] H, θ (α y.right⁻¹ x.left)
    · congr 1
      apply Finset.sum_congr
      · congr 1
      · intro y _
        rw [dif_pos ((conj_mem α x y).mpr hx), kernelCharacter_apply]
        exact conj_value α θ x y hx
    · rw [Nat.card_congr (kernelEquiv α).symm.toEquiv]
      have hs : (∑ y : N ⋊[α] H, θ (α y.right⁻¹ x.left)) =
          (Nat.card N : ℂ) * ∑ a : H, θ (α a x.left) := by
        rw [← (SemidirectProduct.equivProd (φ := α)).symm.sum_comp]
        rw [Fintype.sum_prod_type]
        change (∑ _n : N, ∑ a : H, θ (α a⁻¹ x.left)) = _
        rw [← Equiv.sum_comp (Equiv.inv H) (fun a => θ (α a x.left))]
        simp [Nat.card_eq_fintype_card]
      rw [hs, inv_mul_cancel_left₀]
      exact_mod_cast Nat.card_pos (α := N) |>.ne'
  · rw [if_neg hx]
    exact inducedClassFunction_supportedOn _ _ x (fun y hy => hx ((conj_mem α x y).mp hy))

/-- The degree of an induced linear character is the order of the complement. -/
lemma induced_degree (θ : N →* ℂ) :
    induced α θ (ConjClasses.mk 1) = (Nat.card H : ℂ) := by
  simp [induced_apply, Nat.card_eq_fintype_card]

/-- The induced class function is afforded by an actual finite-dimensional representation. -/
lemma induced_isCharacter (θ : N →* ℂ) : IsConjCharacter (induced α θ) := by
  obtain ⟨n, ρ, _, hρ⟩ := (kernelCharacter α θ).isLinearCharacter.1
  have hc := BrauerInduction.inducedClassFunction_isCharacter (kernel α) ⟨n, ρ, hρ⟩
  obtain ⟨m, σ, hσ⟩ := hc
  refine ⟨m, σ, ?_⟩
  ext c
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
  exact congrFun hσ x

private lemma scalarProduct_sum_right {A I : Type*} [Group A] [Finite A] [Fintype I]
    (f : A → ℂ) (g : I → A → ℂ) :
    scalarProduct A f (fun x => ∑ i, g i x) = ∑ i, scalarProduct A f (g i) := by
  simp only [scalarProduct, star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Reciprocity counts coincidences between linear-character orbits. -/
lemma inner_induced [Fintype H] (θ η : N →* ℂ) :
    classFunctionInner (induced α θ) (induced α η) =
      ∑ a : H, if θ = η.comp (α a).toMonoidHom then (1 : ℂ) else 0 := by
  rw [induced, classFunctionInner_toConjClassFunction_right,
    scalarProduct_inducedClassFunction _ _ (ofConjClassFunction_isClassFunction _)]
  have ht := scalarProduct_comp_mulEquiv (kernelEquiv α)
    (kernelCharacter α θ) (fun x => ofConjClassFunction (induced α η) x)
  trans scalarProduct N (fun n => kernelCharacter α θ (kernelEquiv α n))
        (fun n => ofConjClassFunction (induced α η) (kernelEquiv α n))
  · convert ht.symm using 1
    congr 1
    exact Subsingleton.elim _ _
  · have hleft : (fun n : N => kernelCharacter α θ (kernelEquiv α n)) = θ := by
      ext n
      simp [kernelCharacter]
    have hright : (fun n : N => ofConjClassFunction (induced α η) (kernelEquiv α n)) =
        (fun n => ∑ a : H, (η.comp (α a).toMonoidHom) n) := by
      ext n
      change induced α η (ConjClasses.mk (SemidirectProduct.inl n)) = _
      simp [induced_apply]
    rw [hleft, hright, scalarProduct_sum_right]
    exact Finset.sum_congr rfl fun a _ => AbelianLinearCharacters.orthogonal _ _

/-- A free character orbit gives norm one. -/
lemma induced_norm (θ : N →* ℂ)
    (hθ : Function.Injective (fun a : H => θ.comp (α a).toMonoidHom)) :
    classFunctionInner (induced α θ) (induced α θ) = 1 := by
  rw [inner_induced]
  have hiff (a : H) : θ = θ.comp (α a).toMonoidHom ↔ a = 1 := by
    have hone : θ.comp (α 1).toMonoidHom = θ := by ext; simp
    constructor
    · intro h
      exact hθ (h.symm.trans hone.symm)
    · rintro rfl
      exact hone.symm
  simp only [hiff]
  simp

/-- A linear character with free complement orbit induces irreducibly. -/
lemma induced_irreducible (θ : N →* ℂ)
    (hθ : Function.Injective (fun a : H => θ.comp (α a).toMonoidHom)) :
    IsIrreducibleConjCharacter (induced α θ) :=
  ⟨induced_isCharacter α θ, induced_norm α θ hθ⟩

/-- Equal induced characters come from the same orbit when the first orbit is free. -/
lemma orbit_of_induced_eq (θ η : N →* ℂ)
    (hθ : Function.Injective (fun a : H => θ.comp (α a).toMonoidHom))
    (heq : induced α θ = induced α η) :
    ∃ a : H, θ.comp (α a).toMonoidHom = η := by
  classical
  by_contra h
  push Not at h
  have hz : classFunctionInner (induced α η) (induced α θ) = 0 := by
    rw [inner_induced]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (Ne.symm (h a))
  rw [← heq, induced_norm α θ hθ] at hz
  exact one_ne_zero hz

/-- Moving a linear character within its orbit preserves its induced character. -/
lemma induced_comp_action (θ : N →* ℂ) (a : H) :
    induced α (θ.comp (α a).toMonoidHom) = induced α θ := by
  ext c
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
  simp only [induced_apply]
  split
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    calc
      _ = ∑ b : H, θ (α (a * b) x.left) := by
        apply Finset.sum_congr rfl
        intro b _
        simp
      _ = _ := Equiv.sum_comp (Equiv.mulLeft a) (fun b => θ (α b x.left))
  · rfl

/-- Free orbits parametrize distinct induced irreducible characters. -/
lemma induced_eq_iff (θ η : N →* ℂ)
    (hθ : Function.Injective (fun a : H => θ.comp (α a).toMonoidHom)) :
    induced α θ = induced α η ↔ ∃ a : H, θ.comp (α a).toMonoidHom = η := by
  constructor
  · exact orbit_of_induced_eq α θ η hθ
  · rintro ⟨a, rfl⟩
    exact (induced_comp_action α θ a).symm

end SemidirectLinearInduction
