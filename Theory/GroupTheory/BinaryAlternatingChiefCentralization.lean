module

public import Theory.GroupAction.PGroupNoncentralChiefQuotient
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ThreeSubgroups
public import Mathlib.GroupTheory.IsPerfect

/-!
# Lifting binary alternating displacement to group centralization

Let a finite group map onto S₅ with two-group kernel. If an even involution
in the quotient moves at most one binary dimension on a normal two-group
section C/U, every normal perfect subgroup with even image centralizes C/U.
The section C/U need not itself be elementary abelian.

Set M = [C,K]. Perfectness and the three-subgroups lemma give [M,K] = M.
If M is not contained in U, a maximal invariant subgroup above U ∩ M gives
an actual nontrivial elementary abelian irreducible quotient of M. The
normal two-group kernel fixes this quotient, so its conjugation action
factors through the original S₅ map. The relative-index bound limits the
chosen even involution's displacement to one dimension. The A₅ displacement
theorem then kills K's action, contradicting [M,K] = M.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.71(1), printed p.1075 (PDF p.1092). This is the finite-group
lifting step after the chief-factor displacement calculation.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement

namespace BinaryAlternatingChiefCentralization

private def binaryRepresentation
    {P V : Type*} [Group P] [Group V] [IsElementaryAbelian 2 V]
    (α : P →* MulAut V) : Representation (ZMod 2) P (Additive V) where
  toFun a := (α a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change α 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change α (a * b) v.toMul = α a (α b v.toMul)
    rw [map_mul]
    rfl

private theorem iterated_commutator_eq
    {H : Type*} [Group H] (C K : Subgroup H) [C.Normal] [K.Normal]
    [Group.IsPerfect K] : ⁅⁅C, K⁆, K⁆ = ⁅C, K⁆ := by
  apply le_antisymm (commutator_le_left _ _)
  have h := commutator_commutator_le_of_rotate
    (H₁ := K) (H₂ := K) (H₃ := C) (K := ⁅⁅C,K⁆,K⁆)
    (show ⁅⁅K,C⁆,K⁆ ≤ ⁅⁅C,K⁆,K⁆ by rw [commutator_comm K C]) le_rfl
  rwa [commutator_eq_self, commutator_comm K C] at h

private theorem imageSpace_card
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    {P A B : Subgroup H} {ρ : Representation (ZMod 2) P W}
    (d : BinaryConjugationSection P A B ρ) (D : Subgroup H) (hDA : D ≤ A) :
    Nat.card (d.imageSpace D) = B.relIndex D := by
  change Nat.card ((D.subgroupOf A).map d.coordinates) = _
  rw [← relIndex_ker, d.kernel_eq]
  exact relIndex_subgroupOf hDA

/-- Small displacement by an even involution forces a perfect even-image subgroup
to centralize the original normal two-group section. -/
theorem commutator_le
    {H : Type*} [Group H] [Finite H]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hp : IsPGroup 2 q.ker)
    (C U K : Subgroup H) [C.Normal] [U.Normal] [K.Normal]
    [Group.IsPerfect K] (_hUC : U ≤ C) (hCq : C ≤ q.ker)
    (hKeven : ∀ k : K, q k ∈ alternatingGroup (Fin 5))
    (t : H) (htord : orderOf (q t) = 2) (hteven : q t ∈ alternatingGroup (Fin 5))
    (D : Subgroup H) (_hDC : D ≤ C) (hindex : U.relIndex D ≤ 2)
    (hdisp : ⁅zpowers t, C⁆ ≤ D) : ⁅K,C⁆ ≤ U := by
  rw [Subgroup.commutator_comm]
  by_contra hnot
  let M := ⁅C,K⁆
  have hMC : M ≤ C := commutator_le_left _ _
  have hM : IsPGroup 2 M := hp.to_le (hMC.trans hCq)
  have hBM : U ⊓ M < M := lt_of_le_of_ne inf_le_right (by
    intro he
    exact hnot (he.symm.le.trans inf_le_left))
  obtain ⟨B, hUB, hBM', hBN, hnormal, α, hα, helem, hnontriv, hirr, _, hnonker⟩ :=
    exists_noncentral_irreducible_quotient_above (⊤ : Subgroup H) M (U ⊓ M) K
      le_top le_normalizer_of_normal le_normalizer_of_normal hBM hM le_top
      (iterated_commutator_eq C K)
  let _ := hnormal
  let _ := helem
  let _ := hnontriv
  let V := M ⧸ B.subgroupOf M
  let q' : (⊤ : Subgroup H) →* Equiv.Perm (Fin 5) := q.comp (⊤ : Subgroup H).subtype
  have hq' : Function.Surjective q' := by
    intro s
    obtain ⟨h, rfl⟩ := hq s
    exact ⟨⟨h, mem_top h⟩, rfl⟩
  have hp' : IsPGroup 2 q'.ker := hp.comap_subtype
  let _ : MulDistribMulAction (⊤ : Subgroup H) V := MulDistribMulAction.compHom V α
  have hfixed := irreducible_normal_two_subgroup_fixes hirr q'.ker hp'
  have hkill : q'.ker ≤ α.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    ext v
    have hv : v ∈ FixedPoints.subgroup q'.ker V := by rw [hfixed]; trivial
    exact hv ⟨a,ha⟩
  let β : Equiv.Perm (Fin 5) →* MulAut V := q'.liftOfSurjective hq' ⟨α,hkill⟩
  have hβ (h : (⊤ : Subgroup H)) : β (q' h) = α h :=
    q'.liftOfRightInverse_comp_apply (Function.surjInv hq')
      (Function.rightInverse_surjInv hq') ⟨α,hkill⟩ h
  let σ := binaryRepresentation β
  let c : M →* Multiplicative (Additive V) := {
    toFun := fun m => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' _ m))
    map_one' := map_one (QuotientGroup.mk' _)
    map_mul' := map_mul (QuotientGroup.mk' _) }
  let d : BinaryConjugationSection (⊤ : Subgroup H) M B (σ.comp q') := {
    section_le := le_top
    kernel_le := hBM'.le
    normalized := le_normalizer_of_normal
    coordinates := c
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := by ext m; exact QuotientGroup.eq_one_iff m
    equivariant := by
      intro h m
      change QuotientGroup.mk' _ _ = β (q' h) (QuotientGroup.mk' _ m)
      rw [hβ]
      exact (hα h m).symm }
  let E := D ⊓ M
  have hindexE : (U ⊓ M).relIndex E = U.relIndex E := by
    have he : (U ⊓ M).subgroupOf E = U.subgroupOf E := by
      ext x
      exact and_iff_left x.property.2
    exact congrArg Subgroup.index he
  have hnzero (A L : Subgroup H) : A.relIndex L ≠ 0 := by
    intro hz
    have hd := relIndex_dvd_card A L
    rw [hz, zero_dvd_iff] at hd
    exact Nat.card_pos.ne' hd
  have hcard : Nat.card (d.imageSpace E) ≤ 2 := by
    rw [imageSpace_card d E inf_le_right]
    exact (relIndex_le_of_le_left hUB (hnzero _ _)).trans
      (hindexE.le.trans ((relIndex_le_of_le_right inf_le_left (hnzero _ _)).trans hindex))
  have hdim : Module.finrank (ZMod 2) (d.imageSpace E) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (d.imageSpace E) by omega)
    omega
  have hcomm : ⁅zpowers t,M⁆ ≤ E :=
    le_inf ((commutator_mono le_rfl hMC).trans hdisp) (commutator_le_right _ _)
  have hr := Submodule.finrank_mono
    (d.displacement_range_le_imageSpace_of_commutator_le (zpowers t) E hcomm
      ⟨t,mem_top t⟩ (mem_zpowers t))
  let a : alternatingGroup (Fin 5) := ⟨q t, hteven⟩
  have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans htord
  have htriv := AlternatingFiveInvolutionDisplacement.trivial_of_displacement_le_one
    (σ.comp (alternatingGroup (Fin 5)).subtype) a ha (hr.trans hdim)
  apply hnonker
  intro k hk
  apply MonoidHom.mem_ker.mpr
  ext v
  have htr := htriv ⟨q (k : H), hKeven ⟨k,hk⟩⟩
  have he := LinearMap.congr_fun htr (Additive.ofMul v)
  change β (q' k) v = v at he
  rwa [hβ] at he

end BinaryAlternatingChiefCentralization
