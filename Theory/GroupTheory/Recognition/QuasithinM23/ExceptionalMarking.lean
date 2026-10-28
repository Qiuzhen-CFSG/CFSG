module
public import Theory.GroupTheory.Recognition.QuasithinM23.ExceptionalSplitting
public import Theory.GroupTheory.Recognition.QuasithinM23.ActionComparison
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Permutation marking of an exceptional local by the native M₂₃ heptad

First split the original extension using its fixed-point-free cubic. Compare
its faithful action on the actual E₁₆ core with the native heptad action via
conjugacy of index-eight subgroups of GL₄(2). The resulting equivariant core
map and A₇ automorphism identify the semidirect products. Every automorphism
of A₇ is induced by a seven-point permutation, giving a pointwise identity
for the entire quotient action. Both setwise and pointwise stabilizers are
transported through that same marking.

This proves the exceptional-local permutation equivalence of Aschbacher–Smith
5.2.17, printed p.655 (`refs/quasithin.pdf`). It does not assert any ambient
recognition or a compatible linear-completion marking.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23
open Sporadic.Mathieu.M23Geometry
local notation "A7" => alternatingGroup (Fin 7)

/-- The exceptional local is permutation-isomorphic to the native M₂₃ heptad
stabilizer on its original seven-point quotient. -/
theorem exceptional_heptad_marking
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = U) (hC : centralizer (U : Set X) = U) :
    ∃ (ζ : X ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7)),
      ∀ x : X, heptadAction (ζ x) = σ * (q x).val * σ⁻¹ := by
  obtain ⟨s,hs⟩ := exceptional_exists_section U hU q hq hk hC
  have hqs (g : A7) : q (s g) = g := DFunLike.congr_fun hs g
  let φ : A7 →* MulAut U := MulAut.conjNormal.comp s
  let f : U ⋊[φ] A7 →* X := SemidirectProduct.lift U.subtype s (by
    intro g
    apply MonoidHom.ext
    intro u
    rfl)
  have hf (z : U ⋊[φ] A7) : f z = (z.left : X) * s z.right := rfl
  have hqf (z : U ⋊[φ] A7) : q (f z) = z.right := by
    rw [hf,map_mul,show q z.left = 1 from hk.symm ▸ z.left.property,one_mul,hqs]
  have hfi : Function.Injective f := by
    intro z w hzw
    have hr : z.right = w.right := by simpa only [hqf] using congrArg q hzw
    have hl : z.left = w.left := by
      apply Subtype.ext
      simpa only [hf,hr,mul_left_inj] using hzw
    exact SemidirectProduct.ext hl hr
  have hfs : Function.Surjective f := by
    intro x
    let u : U := ⟨x*(s (q x))⁻¹, hk ▸ (show q (x*(s (q x))⁻¹) = 1 by
      rw [map_mul,map_inv,hqs,mul_inv_cancel])⟩
    exact ⟨⟨u,q x⟩,inv_mul_cancel_right x (s (q x))⟩
  let e0 := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  let ρ := NormalElementaryQuotient.representation U q hq (hk.trans hC.symm)
  have hρ := NormalElementaryQuotient.representation_injective U q hq (hk.trans hC.symm)
  let ρL : A7 →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive U)).toMonoidHom.comp ρ.asGroupHom
  have hρL : Function.Injective ρL :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive U)).injective.comp
      (fun a b hab => hρ (congrArg Units.val hab))
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2^4 := (Nat.card_congr Additive.toMul).trans hU
  obtain ⟨b,a,hba⟩ := exceptional_action_equiv ρL heptadLinearAction
    hρL heptadLinearAction_injective hd (by simp)
  let u : U ≃* Multiplicative (Fin 4 → ZMod 2) := {
    toFun := fun v => Multiplicative.ofAdd (b (Additive.ofMul v))
    invFun := fun w => (b.symm w.toAdd).toMul
    left_inv := fun v => b.symm_apply_apply (Additive.ofMul v)
    right_inv := fun w => b.apply_symm_apply w.toAdd
    map_mul' := fun v w => b.map_add (Additive.ofMul v) (Additive.ofMul w) }
  have hu (g : A7) : (φ g).trans u = u.trans (heptadBinaryAction (a g)) := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change b (Additive.ofMul (φ g v)) = heptadLinearAction (a g) (b (Additive.ofMul v))
    have he : Additive.ofMul (φ g v) = ρL g (Additive.ofMul v) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change s g * (v : X) * (s g)⁻¹ = ((ρ g (Additive.ofMul v)).toMul : X)
      rw [←hqs g,NormalElementaryQuotient.representation_apply,hqs]
      rfl
    rw [he]
    exact hba g (Additive.ofMul v)
  let ζ : X ≃* heptadStabilizer := e0.symm.trans
    ((SemidirectProduct.congr u a hu).trans heptadBinarySplitEquiv)
  have hζ (x : X) : heptadAction (ζ x) = (a (q x)).val := by
    obtain ⟨z,rfl⟩ := e0.surjective x
    change heptadAction (heptadBinarySplitEquiv ((SemidirectProduct.congr u a hu)
      (e0.symm (e0 z)))) = _
    rw [e0.symm_apply_apply]
    change heptadAction (heptadBinarySplitEquiv ⟨u z.left,a z.right⟩) = _
    rw [show q (e0 z) = z.right from hqf z]
    exact heptadAction_split ⟨heptadBinaryEquiv (u z.left),a z.right⟩
  obtain ⟨σ,hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).2 a
  refine ⟨ζ,σ,fun x => (hζ x).trans ?_⟩
  exact (congrArg (fun t : MulAut A7 => (t (q x)).val) hσ).symm

open scoped Pointwise

/-- A permutation marking transports every setwise stabilizer through the
same equivalence, including later pair and four-set stabilizers. -/
theorem heptad_marking_map_stabilizer
    {X : Type*} [Group X] (p : X →* Equiv.Perm (Fin 7))
    (ζ : X ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7))
    (hζ : ∀ x, heptadAction (ζ x) = σ * p x * σ⁻¹) (S : Set (Fin 7)) :
    ((MulAction.stabilizer (Equiv.Perm (Fin 7)) S).comap p).map ζ.toMonoidHom =
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) (σ • S)).comap heptadAction := by
  ext y
  rw [mem_map_equiv]
  change p (ζ.symm y) ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) S ↔ _
  have hy : heptadAction y = (MulAut.conj σ) (p (ζ.symm y)) := by
    simpa only [ζ.apply_symm_apply,MulAut.conj_apply] using hζ (ζ.symm y)
  change _ ↔ heptadAction y ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) (σ • S)
  rw [hy,MulAction.stabilizer_smul_eq_stabilizer_map_conj,mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]

/-- The same marking simultaneously transports every pointwise fixer. -/
theorem heptad_marking_map_fixingSubgroup
    {X : Type*} [Group X] (p : X →* Equiv.Perm (Fin 7))
    (ζ : X ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7))
    (hζ : ∀ x, heptadAction (ζ x) = σ * p x * σ⁻¹) (S : Set (Fin 7)) :
    ((fixingSubgroup (Equiv.Perm (Fin 7)) S).comap p).map ζ.toMonoidHom =
      (fixingSubgroup (Equiv.Perm (Fin 7)) (σ • S)).comap heptadAction := by
  ext y
  rw [mem_map_equiv]
  change p (ζ.symm y) ∈ fixingSubgroup (Equiv.Perm (Fin 7)) S ↔ _
  have hy : heptadAction y = (MulAut.conj σ) (p (ζ.symm y)) := by
    simpa only [ζ.apply_symm_apply,MulAut.conj_apply] using hζ (ζ.symm y)
  change _ ↔ heptadAction y ∈ fixingSubgroup (Equiv.Perm (Fin 7)) (σ • S)
  rw [hy,SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj,mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]

/-- The same permutation equivalence maps the entire original action kernel
to the literal native heptad kernel. -/
theorem heptad_marking_map_kernel
    {X : Type*} [Group X] (p : X →* Equiv.Perm (Fin 7))
    (ζ : X ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7))
    (hζ : ∀ x, heptadAction (ζ x) = σ * p x * σ⁻¹) :
    p.ker.map ζ.toMonoidHom = heptadKernel := by
  ext y
  rw [mem_map_equiv]
  change p (ζ.symm y) = 1 ↔ heptadAction y = 1
  have hy : heptadAction y = (MulAut.conj σ) (p (ζ.symm y)) := by
    simpa only [ζ.apply_symm_apply,MulAut.conj_apply] using hζ (ζ.symm y)
  rw [hy]
  exact (MulEquiv.map_eq_one_iff _).symm

/-- An inner adjustment in the native heptad sends a chosen ordered pair to
the standard pair, preserving the pointwise identity on the entire action. -/
theorem heptad_marking_align_pair
    {X : Type*} [Group X] (p : X →* Equiv.Perm (Fin 7))
    (ζ : X ≃* heptadStabilizer) (σ : Equiv.Perm (Fin 7))
    (hζ : ∀ x, heptadAction (ζ x) = σ * p x * σ⁻¹)
    (i j : Fin 7) (hij : i ≠ j) :
    ∃ (η : X ≃* heptadStabilizer) (τ : Equiv.Perm (Fin 7)),
      τ i = 5 ∧ τ j = 6 ∧
      ∀ x, heptadAction (η x) = τ * p x * τ⁻¹ := by
  have := alternatingGroup.isMultiplyPretransitive (Fin 7)
  have ht : MulAction.IsMultiplyPretransitive A7 (Fin 7) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 7) - 2) (by simp) (Nat.sub_le _ _)
  obtain ⟨a,hai,haj⟩ := MulAction.is_two_pretransitive_iff.mp ht
    (σ.injective.ne hij) (by decide : (5 : Fin 7) ≠ 6)
  let k := AlternatingSection.s a
  refine ⟨ζ.trans (MulAut.conj k),a.val * σ,hai,haj,?_⟩
  intro x
  change heptadAction (k * ζ x * k⁻¹) = (a.val * σ) * p x * (a.val * σ)⁻¹
  rw [map_mul,map_mul,map_inv,AlternatingSection.heptadAction_s,hζ]
  group

end Theory.GroupTheory.QuasithinM23
