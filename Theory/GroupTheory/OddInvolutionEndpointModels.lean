module

public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Odd subgroups extended by an involution

An involution complements a normal subgroup of odd order when they generate
the ambient group. This gives an actual multiplicative equivalence with a
semidirect product by the concrete cyclic group of order two, together with
the action of its distinguished generator. If the odd subgroup is abelian
and equals its commutator with the involution, conjugation is inversion.
For a cyclic subgroup this identifies the extension with a dihedral group.
The order-six model is also explicitly identified with the permutations of
three points by checking its six-element multiplication table.

These elementary extension results support Aschbacher--Smith,
*The Classification of Quasithin Groups*, Theorem D.2.17(1)--(4).
-/

@[expose] public section

open scoped IsMulCommutative
namespace Theory.GroupTheory

theorem involution_inverts_abelian_action_commutator
    {A W : Type*} [Group A] [Group W] [IsMulCommutative W]
    [MulDistribMulAction A W] (a : A) (ha : a ≠ 1 ∧ a ^ 2 = 1) :
    ∀ w ∈ commutatorAction (Subgroup.zpowers a) W, a • w = w⁻¹ := by
  have haa (w : W) : a • (a • w) = w := by
    rw [smul_smul, ← pow_two, ha.2, one_smul]
  have hmem (p : Subgroup.zpowers a) : (p : A) = 1 ∨ (p : A) = a := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp p.property
    have hred : a ^ n = a ^ (n % 2) := by
      simpa only [orderOf_eq_prime ha.2 ha.1, Nat.cast_ofNat] using
        (zpow_mod_orderOf a n).symm
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [← hn, hred, h]; simp
    · right; rw [← hn, hred, h]; simp
  intro w hw
  rw [commutatorAction_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
      obtain ⟨p, x, rfl⟩ := hw
      rcases hmem p with hp | hp
      · change a • (x⁻¹ * ((p : A) • x)) = (x⁻¹ * ((p : A) • x))⁻¹
        simp [hp]
      · change a • (x⁻¹ * ((p : A) • x)) = (x⁻¹ * ((p : A) • x))⁻¹
        rw [hp, smul_mul', smul_inv', haa, mul_inv_rev, inv_inv]
  | one => simp
  | mul x y _ _ hx hy => simp only [smul_mul', hx, hy, mul_inv_rev]; exact mul_comm _ _
  | inv x _ hx => simp only [smul_inv', hx]

theorem inverts_abelian_of_full_commutator
    {G : Type*} [Group G] (R : Subgroup G) [R.Normal] [IsMulCommutative R]
    (t : G) (ht : t ≠ 1 ∧ t ^ 2 = 1) (hc : ⁅R, Subgroup.zpowers t⁆ = R) :
    ∀ r : R, t * (r : G) * t⁻¹ = (r : G)⁻¹ := by
  let hn : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_of_normal
  let : MulDistribMulAction G R := MulDistribMulAction.compHom R (MulAut.conjNormal : G →* MulAut R)
  have hm : (commutatorAction (Subgroup.zpowers t) R).map R.subtype = R := by
    rw [commutatorAction_subgroup_conj_map_eq_commutator R (Subgroup.zpowers t) hn, hc]
  have hfull : commutatorAction (Subgroup.zpowers t) R = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hm
  intro r
  have h := involution_inverts_abelian_action_commutator t ht r (hfull ▸ Subgroup.mem_top r)
  exact congrArg Subtype.val h

theorem odd_involution_complement
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) [R.Normal]
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) : R.IsComplement' (Subgroup.zpowers t) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_of_coprime_natCard
    simpa [Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1] using hodd.symm
  · rw [← Subgroup.normal_mul, hgen]; rfl

theorem odd_involution_not_mem
    {G : Type*} [Group G] [Finite G] (R : Subgroup G)
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : t ≠ 1 ∧ t ^ 2 = 1) : t ∉ R := by
  intro hmem
  have hd : 2 ∣ Nat.card R := by
    simpa [Subgroup.orderOf_coe, orderOf_eq_prime ht.2 ht.1] using
      orderOf_dvd_natCard (⟨t,hmem⟩ : R)
  have hh := Nat.eq_one_of_dvd_coprimes hodd (dvd_refl 2) hd
  omega

theorem odd_involution_dihedral
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) [R.Normal] [IsCyclic R]
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) (hc : ⁅R, Subgroup.zpowers t⁆ = R) :
    Nonempty (G ≃* DihedralGroup (Nat.card R)) := by
  obtain ⟨e⟩ := R.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted t inferInstance
    ht.2 (odd_involution_not_mem R hodd t ht)
    (fun r hr => inverts_abelian_of_full_commutator R t ht hc ⟨r, hr⟩)
  exact ⟨((MulEquiv.subgroupCongr hgen).trans (Subgroup.topEquiv)).symm.trans e⟩

theorem odd_involution_semidirect_model
    {G N : Type*} [Group G] [Group N] [Finite G] (R : Subgroup G) [R.Normal]
    (hodd : Nat.Coprime 2 (Nat.card R)) (t : G) (ht : t ≠ 1 ∧ t ^ 2 = 1)
    (hgen : R ⊔ Subgroup.zpowers t = ⊤) (e : R ≃* N) :
    ∃ φ : Multiplicative (ZMod 2) →* MulAut N,
      (∀ r : R, φ (Multiplicative.ofAdd 1) (e r) = e (MulAut.conjNormal t r)) ∧
      Nonempty (G ≃* N ⋊[φ] Multiplicative (ZMod 2)) := by
  let T := Subgroup.zpowers t
  have hT : Nat.card T = 2 := by
    simp only [T, Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1]
  let g : T := ⟨t, Subgroup.mem_zpowers t⟩
  have hg : ∀ y : T, y ∈ Subgroup.zpowers g := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  let eT : T ≃* Multiplicative (ZMod 2) :=
    (zmodMulEquivOfGenerator hg hT).symm
  let E := SemidirectProduct.mulEquivSubgroup (odd_involution_complement R hodd t ht hgen)
  let F := SemidirectProduct.congr' (φ₁ :=
    R.normalizerMonoidHom.comp (Subgroup.inclusion (R.normalizer_eq_top ▸ le_top))) e eT
  refine ⟨_, ?_, ⟨E.symm.trans F⟩⟩
  intro r
  simp only [MonoidHom.comp_apply, eT, MulEquiv.symm_symm]
  change e ((R.normalizerMonoidHom _) (e.symm (e r))) = _
  rw [e.symm_apply_apply]
  change e ((R.normalizerMonoidHom ((Subgroup.inclusion _)
    ((zmodMulEquivOfGenerator hg hT) (Multiplicative.ofAdd 1)))) r) = _
  rw [zmodMulEquivOfGenerator_apply_ofAdd_one]
  rfl

private def dihedralThreeToPerm : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun d := match d with
    | .r i => (Equiv.swap 0 1 * Equiv.swap 1 2) ^ i.val
    | .sr i => Equiv.swap 0 1 * (Equiv.swap 0 1 * Equiv.swap 1 2) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem nonempty_dihedralThreeEquivPerm : Nonempty (DihedralGroup 3 ≃* Equiv.Perm (Fin 3)) :=
  ⟨MulEquiv.ofBijective dihedralThreeToPerm (by decide +kernel)⟩

end Theory.GroupTheory
