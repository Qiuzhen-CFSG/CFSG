module

public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.SylowNormalCenterIntersection
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Faithful complement action in the Held local configuration

With an explicit complement K to F in the involution centralizer H, we
construct K ≃ S4 and the actual semidirect product F ⋊ K ≃ H. Conjugation
by K on F is faithful, C_H(F) = F, and the given Sylow center has order two.
None of these consequences needs simplicity of the ambient group.

For faithfulness, K ∩ C_H(F) is normal in H. A normal subgroup of even
order contains the distinguished involution: its intersection with the
local Sylow subgroup meets the cyclic center. Since that involution lies
in F, disjointness of the complement forces K ∩ C_H(F) to have odd order.
Its image in S4 is normal, hence trivial. The last finite assertion is
checked on the twenty-four permutations, by constructing an involution
from each nonidentity element and one of its conjugates.

These are local reductions for Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), p.314, and D. Held, "A Characterization of some multiply
transitive permutation groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756. They do not assert global recognition.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.LocalData
universe u
variable {G : Type u} [Group G] (D : LocalData G)

/-- The supplied complement identifies with the actual symmetric quotient. -/
@[expose] public noncomputable def complementEquiv (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) : K ≃* Equiv.Perm (Fin 4) := by
  let := D.kernel_normal
  exact hK.symm.QuotientMulEquiv.symm.trans D.quotientEquiv

/-- Conjugation on the elementary kernel by the actual complement. -/
@[expose] public def complementAction (K : Subgroup D.centralizer) : K →* MulAut D.kernel := by
  let := D.kernel_normal
  exact D.kernel.normalizerMonoidHom.comp
    (inclusion (D.kernel.normalizer_eq_top ▸ le_top))

/-- The action is actual conjugation inside the involution centralizer. -/
public theorem complementAction_apply (K : Subgroup D.centralizer) (k : K) (f : D.kernel) :
    (D.complementAction K k f : D.centralizer) = k * f * (k : D.centralizer)⁻¹ := rfl

/-- Multiplication identifies the semidirect product with the given centralizer. -/
@[expose] public noncomputable def complementSemidirectEquiv (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    D.kernel ⋊[D.complementAction K] K ≃* D.centralizer := by
  let := D.kernel_normal
  exact SemidirectProduct.mulEquivSubgroup hK

/-- Every normal subgroup of even order contains the specified central involution. -/
public theorem centralInvolution_mem_even_normal [Finite G]
    (N : Subgroup D.centralizer) [N.Normal] (hN : 2 ∣ Nat.card N) :
    D.centralInvolution ∈ N := by
  obtain ⟨x, hxc, hxne, hxN⟩ :=
    D.localSylow.exists_ne_one_mem_center_of_normal N hN
  let n := orderOf x / 2
  have hx2 : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos x))
      (D.localSylow.isPGroup'.dvd_orderOf hxne)
  let e : D.localSylow ≃* D.sylow :=
    subgroupOfEquivOfLe D.sylow_le_centralizer
  let y : center D.sylow := centerCongr e ⟨x ^ n, (center _).pow_mem hxc n⟩
  have hy2 : orderOf y = 2 := by
    rw [show orderOf y = orderOf (x ^ n) from
      (centerCongr e).orderOf_eq _ |>.trans (Subgroup.orderOf_mk _ _)]
    exact hx2
  have heq : ((x ^ n : D.localSylow) : D.centralizer) = D.centralInvolution :=
    Subtype.ext (congrArg (fun a : center D.sylow => ((a : D.sylow) : G))
      (D.involution_unique y hy2))
  rw [← heq]
  exact N.pow_mem hxN n

private theorem perm_four_normal_eq_bot_of_not_even
    (N : Subgroup (Equiv.Perm (Fin 4))) [N.Normal] (hN : ¬ 2 ∣ Nat.card N) : N = ⊥ := by
  have no_two (x : Equiv.Perm (Fin 4)) (hxN : x ∈ N) (hx2 : x ^ 2 = 1) : x = 1 := by
    have hd : orderOf x ∣ Nat.card N := by
      simpa only [Subgroup.orderOf_mk] using (_root_.orderOf_dvd_natCard (x := (⟨x, hxN⟩ : N)))
    have hdiv := (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2)
    exact orderOf_eq_one_iff.mp (hdiv.resolve_right (fun h => hN (h ▸ hd)))
  have witness : ∀ x : Equiv.Perm (Fin 4), x ≠ 1 →
      x ^ 2 = 1 ∨ (x ^ 2 ≠ 1 ∧ (x ^ 2) ^ 2 = 1) ∨
        ∃ g : Equiv.Perm (Fin 4),
          x * (g * x * g⁻¹) ≠ 1 ∧ (x * (g * x * g⁻¹)) ^ 2 = 1 := by
    decide +kernel
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  by_contra hxne
  rcases witness x hxne with h | ⟨hne, htwo⟩ | ⟨g, hne, htwo⟩
  · exact hxne (no_two x hx h)
  · exact hne (no_two _ (N.pow_mem hx _) htwo)
  · exact hne (no_two _ (N.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x hx g)) htwo)

private theorem complement_centralizer_normal (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    (K ⊓ Subgroup.centralizer (D.kernel : Set D.centralizer)).Normal := by
  let := D.kernel_normal
  let C := Subgroup.centralizer (D.kernel : Set D.centralizer)
  have hCnormal : C.Normal := inferInstance
  constructor
  intro n hn g
  obtain ⟨⟨f, k⟩, rfl⟩ := hK.2 g
  have hkn : (k : D.centralizer) * n * (k : D.centralizer)⁻¹ ∈ C := hCnormal.conj_mem n hn.2 k
  have hcomm := mem_centralizer_iff.mp hkn f f.property
  have heq : (f : D.centralizer) * k * n * ((f : D.centralizer) * k)⁻¹ =
      (k : D.centralizer) * n * (k : D.centralizer)⁻¹ := by
    calc
      _ = (f : D.centralizer) * ((k : D.centralizer) * n * (k : D.centralizer)⁻¹) *
          (f : D.centralizer)⁻¹ := by simp only [mul_inv_rev, mul_assoc]
      _ = _ := by rw [hcomm]; simp
  change (f : D.centralizer) * k * n * ((f : D.centralizer) * k)⁻¹ ∈ K ⊓ C
  rw [heq]
  exact ⟨K.mul_mem (K.mul_mem k.property hn.1) (K.inv_mem k.property), hkn⟩

/-- No nonidentity complement element centralizes the elementary kernel. -/
public theorem complement_inf_kernel_centralizer [Finite G]
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    K ⊓ Subgroup.centralizer (D.kernel : Set D.centralizer) = ⊥ := by
  let N := K ⊓ Subgroup.centralizer (D.kernel : Set D.centralizer)
  let : N.Normal := D.complement_centralizer_normal K hK
  have hN : ¬ 2 ∣ Nat.card N := by
    intro hdvd
    have hzN := D.centralInvolution_mem_even_normal N hdvd
    have hz := Subgroup.disjoint_def.mp hK.disjoint D.centralInvolution_mem_kernel hzN.1
    exact D.z_ne_one (congrArg Subtype.val hz)
  let e := D.complementEquiv K hK
  let Q := N.subgroupOf K
  let R := Q.map e.toMonoidHom
  let : R.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hcard : Nat.card R = Nat.card N :=
    (Nat.card_congr (e.subgroupMap Q).toEquiv).symm.trans
      (Nat.card_congr (subgroupOfEquivOfLe (show N ≤ K from inf_le_left)).toEquiv)
  have hR : R = ⊥ := perm_four_normal_eq_bot_of_not_even R (hcard ▸ hN)
  apply Subgroup.card_eq_one.mp
  rw [← hcard]
  exact Subgroup.card_eq_one.mpr hR

/-- The supplied symmetric complement acts faithfully on the elementary kernel. -/
public theorem complementAction_injective [Finite G]
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    Function.Injective (D.complementAction K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro k hk
  have hkC : (k : D.centralizer) ∈ Subgroup.centralizer (D.kernel : Set D.centralizer) := by
    apply mem_centralizer_iff.mpr
    intro f hf
    have he : D.complementAction K k = 1 := hk
    have hconj : (k : D.centralizer) * f * (k : D.centralizer)⁻¹ = f :=
      congrArg (fun a : MulAut D.kernel => (a ⟨f, hf⟩ : D.centralizer)) he
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hkbot : (k : D.centralizer) ∈ K ⊓
      Subgroup.centralizer (D.kernel : Set D.centralizer) := ⟨k.property, hkC⟩
  rw [D.complement_inf_kernel_centralizer K hK, mem_bot] at hkbot
  exact Subtype.ext hkbot

/-- The elementary kernel is self-centralizing in the involution centralizer. -/
public theorem kernel_centralizer_eq [Finite G]
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    Subgroup.centralizer (D.kernel : Set D.centralizer) = D.kernel := by
  let := D.kernel_elementary
  have hFC : D.kernel ≤ Subgroup.centralizer (D.kernel : Set D.centralizer) :=
    le_centralizer D.kernel
  apply le_antisymm _ hFC
  intro x hx
  obtain ⟨⟨f, k⟩, rfl⟩ := hK.2 x
  have hkC : (k : D.centralizer) ∈ Subgroup.centralizer (D.kernel : Set D.centralizer) := by
    have h := (Subgroup.centralizer (D.kernel : Set D.centralizer)).mul_mem
      ((Subgroup.centralizer (D.kernel : Set D.centralizer)).inv_mem (hFC f.property)) hx
    simpa only [inv_mul_cancel_left] using h
  have hk : (k : D.centralizer) = 1 := by
    have hm : (k : D.centralizer) ∈ K ⊓
        Subgroup.centralizer (D.kernel : Set D.centralizer) := ⟨k.property, hkC⟩
    rwa [D.complement_inf_kernel_centralizer K hK, mem_bot] at hm
  change (f : D.centralizer) * k ∈ D.kernel
  rw [hk, mul_one]
  exact f.property

/-- Under splitting, the full intrinsic Sylow center is generated by the involution. -/
public theorem sylow_center_eq_zpowers [Finite G]
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    center D.sylow = zpowers (D.involution : D.sylow) := by
  apply le_antisymm
  · intro x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xH : D.centralizer := ⟨x, D.sylow_le_centralizer x.property⟩
    have hxC : xH ∈ Subgroup.centralizer (D.kernel : Set D.centralizer) := by
      apply mem_centralizer_iff.mpr
      intro f hf
      exact Subtype.ext (congrArg (fun a : D.sylow => (a : G))
        (mem_center_iff.mp hx ⟨f, D.kernel_le_localSylow hf⟩))
    have hxF : xH ∈ D.kernel := D.kernel_centralizer_eq K hK ▸ hxC
    have hx2 : orderOf xH = 2 := by
      let := D.kernel_elementary
      apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) xH hxF)
      intro he
      exact hxone (Subtype.ext (congrArg (fun a : D.centralizer => (a : G)) he))
    have hxZ2 : orderOf (⟨x, hx⟩ : center D.sylow) = 2 := by
      simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe, xH] using hx2
    have heq : x = D.involution :=
      congrArg Subtype.val (D.involution_unique ⟨x, hx⟩ hxZ2)
    rw [heq]
    exact mem_zpowers _
  · exact zpowers_le.mpr D.involution.property

/-- Under splitting, the cyclic Sylow center has order exactly two. -/
public theorem sylow_center_card [Finite G]
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    Nat.card (center D.sylow) = 2 := by
  rw [D.sylow_center_eq_zpowers K hK, Nat.card_zpowers]
  simpa only [Subgroup.orderOf_coe] using D.involution_order

end Theory.GroupTheory.HeldM22A10.LocalData
