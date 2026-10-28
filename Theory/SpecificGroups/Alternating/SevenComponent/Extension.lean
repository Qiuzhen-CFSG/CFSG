module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Alternating.Aut
public import Theory.PGroupCore
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The literal seven-letter action of an A₇ core extension

Conjugation on K/O₂(K) and Aut(A₇)=S₇ construct the action of an ambient
group with normal K. Its restriction is the original marked quotient map.
When G/K is a two-group, the action kernel is a two-group and in fact
exactly O₂(G). Thus both the seven-letter coordinates and the kernel used
in the ordinary A₇ argument of C.1.29, printed p.134, are proved.
-/
public section
open Subgroup
namespace alternatingGroup.SevenComponent
variable {G : Type*} [Group G]

/-- The seven-letter action induced by the actual normal core quotient. -/
theorem exists_extension (K : Subgroup G) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ f : G →* Equiv.Perm (Fin 7),
      ∀ k : K, f k = (e (QuotientGroup.mk' (pCore 2 K) k)).val := by
  let eS : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let a : G →* MulAut (alternatingGroup (Fin 7)) :=
    (MulAut.congr e).toMonoidHom.comp (normalQuotientAction K (pCore 2 K))
  let f : G →* Equiv.Perm (Fin 7) := eS.symm.toMonoidHom.comp a
  refine ⟨f, fun k => ?_⟩
  apply eS.injective
  change eS (eS.symm (a k)) = _
  rw [eS.apply_symm_apply]
  change MulAut.congr e (normalQuotientAction K (pCore 2 K) k) =
    MulAut.conjNormal (e (QuotientGroup.mk' (pCore 2 K) k)).val
  rw [normalQuotientAction_inner, MulAut.conjNormal_val]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

/-- If the normal A₇ extension has two-group quotient, the seven-letter
permutation action has a two-group kernel. No cover or splitting is assumed. -/
theorem extension_kernel_isTwoGroup (K : Subgroup G) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hG : IsPGroup 2 (G ⧸ K))
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ k : K, f k = (e (QuotientGroup.mk' (pCore 2 K) k)).val) :
    IsPGroup 2 f.ker := by
  intro x
  obtain ⟨n, hn⟩ := hG (QuotientGroup.mk' K x.val)
  have hxn : x.val ^ 2 ^ n ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' K (x.val ^ 2 ^ n) = 1
    rwa [map_pow]
  let k : K := ⟨x.val ^ 2 ^ n, hxn⟩
  have hfk : f k = 1 := by
    change f (x.val ^ 2 ^ n) = 1
    rw [map_pow, show f x.val = 1 from x.property, one_pow]
  have hk : k ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.map_eq_one_iff.mp
    exact Subtype.ext ((hf k).symm.trans hfk)
  obtain ⟨m, hm⟩ := pCore_isPGroup (p := 2) (G := K) ⟨k, hk⟩
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  have h := congrArg (fun z : pCore 2 K => ((z : K) : G)) hm
  simpa only [coe_pow, coe_one, k, pow_add, pow_mul] using h

/-- The action contains the actual alternating subgroup on seven letters. -/
theorem alternating_le_range (K : Subgroup G) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ k : K, f k = (e (QuotientGroup.mk' (pCore 2 K) k)).val) :
    alternatingGroup (Fin 7) ≤ f.range := by
  intro a ha
  obtain ⟨q, hq⟩ := e.surjective ⟨a, ha⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
  exact ⟨k, (hf k).trans (congrArg Subtype.val hq)⟩

variable [Finite G]
open scoped commutatorElement

/-- The kernel is exactly the original two-core, with no arbitrary quotient
identification or multiplier assertion. -/
theorem extension_kernel_eq_twoCore (K : Subgroup G) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hG : IsPGroup 2 (G ⧸ K))
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ k : K, f k = (e (QuotientGroup.mk' (pCore 2 K) k)).val) :
    f.ker = pCore 2 G := by
  have hk : f.ker ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, extension_kernel_isTwoGroup K e hG f hf⟩
  apply le_antisymm hk
  intro x hx
  change f x = 1
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by decide) (by decide)).injective
  apply MulEquiv.ext
  intro a
  obtain ⟨z, rfl⟩ := e.surjective a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  apply Subtype.ext
  change f x * (e (QuotientGroup.mk' (pCore 2 K) k)).val * (f x)⁻¹ =
    (e (QuotientGroup.mk' (pCore 2 K) k)).val
  rw [← hf]
  have hcK : ⁅x, (k : G)⁆ ∈ K := commutator_le_right (pCore 2 G) K
    (commutator_mem_commutator hx k.property)
  have hcQ : ⁅x, (k : G)⁆ ∈ pCore 2 G := commutator_le_left (pCore 2 G) K
    (commutator_mem_commutator hx k.property)
  let c : K := ⟨⁅x, (k : G)⁆, hcK⟩
  have hc : c ∈ pCore 2 K := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal]
    exact hcQ
  have hfc : f c = 1 := by
    rw [hf, show QuotientGroup.mk' (pCore 2 K) c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    simp
  have he : ⁅f x, f k⁆ = 1 := by simpa only [c, map_commutatorElement] using hfc
  have hcomm := commutatorElement_eq_one_iff_mul_comm.mp he
  rw [hcomm, mul_inv_cancel_right]
end alternatingGroup.SevenComponent
