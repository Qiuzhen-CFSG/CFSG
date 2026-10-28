module

public import Theory.Representation.AbelianWeightDecomposition
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed vectors for a prime subgroup normalizing an abelian kernel

A prime-order subgroup acting without fixed points on a finite abelian normal
subgroup acts freely on its nontrivial multiplicative characters. Over an
algebraically closed field of characteristic prime to the kernel order, a
nonzero representation with no kernel invariants therefore has a nonzero
prime-subgroup invariant: sum the translates of a nonzero weight vector.
Distinct weight spaces make this sum nonzero.

The character argument uses bijectivity of the displacement endomorphism of
the abelian kernel. This is the fixed-vector step in Thompson, *Nonsolvable
finite groups all of whose local subgroups are solvable*, VI, printed p.630.
-/

open scoped IsMulCommutative

namespace Representation

private theorem conj_eq_self_imp_eq_one
    {H : Type*} [Group H] (B A : Subgroup H) [B.Normal]
    {p : ℕ} [Fact p.Prime] (hA : Nat.card A = p)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥)
    (a : A) (ha : a ≠ 1) (b : B)
    (hb : MulAut.conjNormal (a : H) b = b) : b = 1 := by
  have hc : Commute (a : H) (b : H) := by
    have := congrArg Subtype.val hb
    rw [MulAut.conjNormal_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this)
  have hcent : (b : H) ∈ Subgroup.centralizer (A : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hcA
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hA ha (g' := (⟨c, hcA⟩ : A)))
    have hn' : (a : H) ^ n = c := congrArg Subtype.val hn
    rw [← hn']
    exact (hc.zpow_left n).eq
  have : (b : H) ∈ (⊥ : Subgroup H) := hfree ▸ ⟨b.property, hcent⟩
  exact Subtype.ext (Subgroup.mem_bot.mp this)

private theorem character_conj_ne
    {H C : Type*} [Group H] [CommGroup C]
    (B A : Subgroup H) [B.Normal] [Finite B] [IsMulCommutative B]
    {p : ℕ} [Fact p.Prime] (hA : Nat.card A = p)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥)
    (χ : B →* C) (hχ : χ ≠ 1) (a : A) (ha : a ≠ 1) :
    ∃ b : B, χ (MulAut.conjNormal (a : H) b) ≠ χ b := by
  classical
  by_contra! heq
  let d : B →* B :=
    { toFun := fun b => MulAut.conjNormal (a : H) b * b⁻¹
      map_one' := by simp
      map_mul' := by intros; simp [mul_assoc, mul_left_comm, mul_comm] }
  have hd : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply eq_bot_iff.mpr
    intro b hb
    have hfix : MulAut.conjNormal (a : H) b = b := by
      have : d b = 1 := hb
      exact mul_inv_eq_one.mp this
    exact conj_eq_self_imp_eq_one B A hA hfree a ha b hfix
  have hs : Function.Surjective d := Finite.surjective_of_injective hd
  apply hχ
  ext b
  obtain ⟨c, rfl⟩ := hs b
  simp [d, heq]

private theorem character_conj_injective
    {H C : Type*} [Group H] [CommGroup C]
    (B A : Subgroup H) [B.Normal] [Finite B] [IsMulCommutative B]
    {p : ℕ} [Fact p.Prime] (hA : Nat.card A = p)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥)
    (χ : B →* C) (hχ : χ ≠ 1) :
    Function.Injective (fun a : A => χ.comp (MulAut.conjNormal (a : H)⁻¹).toMonoidHom) := by
  intro a b hab
  by_contra hne
  have hba : b⁻¹ * a ≠ 1 := by
    intro h; exact hne (inv_mul_eq_one.mp h).symm
  obtain ⟨c, hc⟩ := character_conj_ne B A hA hfree χ hχ (b⁻¹ * a) hba
  have heq := DFunLike.congr_fun hab (MulAut.conjNormal (a : H) c)
  apply hc
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, MulAut.mul_apply,
    MulAut.inv_apply_self] using heq.symm

/-- A prime-order subgroup acting fixed freely on an abelian normal subgroup
has a nonzero invariant in every nonzero representation with no kernel
invariants, over an algebraically closed field of coprime characteristic. -/
public theorem prime_subgroup_invariants_ne_bot_of_fixed_free
    {E H V : Type*} [Field E] [IsAlgClosed E] [Group H]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Nontrivial V]
    (rho : Representation E H V)
    (B A : Subgroup H) [B.Normal] [Finite B] [IsMulCommutative B]
    {p : ℕ} [Fact p.Prime] (hA : Nat.card A = p)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥)
    (horder : (Nat.card B : E) ≠ 0)
    (hfix : invariants (rho.comp B.subtype) = ⊥) :
    invariants (rho.comp A.subtype) ≠ ⊥ := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero (hA.trans_ne (Fact.out : p.Prime).ne_zero)
  let : Fintype A := Fintype.ofFinite A
  let weights (χ : {χ : B →* Eˣ // χ ≠ 1}) : Submodule E V :=
    ⨅ b : B, Module.End.eigenspace (rho b) (χ.val b : E)
  have hdec : DirectSum.IsInternal weights :=
    isInternal_nontrivial_characterWeightSpaces (rho.comp B.subtype) horder hfix
  obtain ⟨χ, hχ⟩ : ∃ χ, weights χ ≠ ⊥ := by
    by_contra! h
    have ht := hdec.submodule_iSup_eq_top
    change (⨆ i, weights i) = ⊤ at ht
    simp only [h, iSup_bot] at ht
    exact bot_ne_top ht
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hv' : ∀ b : B, rho b v = (χ.val b : E) • v := by
    simpa only [weights, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using hv
  let chars (a : A) : B →* Eˣ := χ.val.comp (MulAut.conjNormal (a : H)⁻¹).toMonoidHom
  have hchars : ∀ a, chars a ≠ 1 := by
    intro a heq
    apply χ.property
    ext b
    have h := DFunLike.congr_fun heq (MulAut.conjNormal (a : H) b)
    simpa [chars] using h
  let indices (a : A) : {χ : B →* Eˣ // χ ≠ 1} := ⟨chars a, hchars a⟩
  have hinj : Function.Injective indices := by
    intro a b hab
    exact character_conj_injective B A hA hfree χ.val χ.property
      (congrArg Subtype.val hab)
  have hmem (a : A) : rho a v ∈ weights (indices a) := by
    simp only [weights, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro b
    have hmul : (b : H) * a = (a : H) * MulAut.conjNormal (a : H)⁻¹ b := by
      simp [mul_assoc]
    change rho b (rho a v) = (chars a b : E) • rho a v
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply,
      hv', map_smul]
    rfl
  have hsum : (∑ a : A, rho a v) ≠ 0 := by
    intro hz
    have hind := hdec.submodule_iSupIndep.comp hinj
    have hall := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind
      Finset.univ (fun a : A => rho a v) (fun a _ => hmem a) hz 1 (Finset.mem_univ 1)
    exact hv0 (by simpa using hall)
  intro hbot
  apply hsum
  have hmemsum : (∑ a : A, rho a v) ∈ invariants (rho.comp A.subtype) := by
    rw [mem_invariants]
    intro a
    change rho (a : H) (∑ b : A, rho b v) = _
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Function.Bijective.sum_comp (Group.mulLeft_bijective a) (fun b : A => rho b v)
  simpa [hbot] using hmemsum

end Representation
