module
public import Theory.GroupTheory.CComponent.PrimeRankOuterTwo

/-!
# Prime absorption through a normal action image

Let C be normal in a finite group G. If the kernel of its action lies in
O₂(G), and O₂(G) acts trivially, the image of C in G/O₂(G) contains an
actual copy of any normal subgroup of the action image contained in C's
image. A subgroup of full odd-prime rank with prime-to-p center and outer
automorphism group a two-group absorbs every order-p element. Coprime
kernel absorption then puts those elements in the original C.

This retains both quotient maps and does not assume that the entire action
kernel is a two-group. The application is the G₂(2) cubic containment in
Aschbacher--Smith 14.3.31, printed p.1003, using the outer-two case of A.3.18.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentPrimeRank
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D] {p : ℕ} [Fact p.Prime]

/-- Absorb prime actors in a normal subgroup whose action contains a full-rank
normal subgroup; the kernel on that subgroup must lie in the ambient two-core. -/
theorem prime_actor_mem_of_normal_image
    (f : G →* D) (C : Subgroup G) [C.Normal] (S : Subgroup D) [S.Normal]
    (hS : S ≤ C.map f) (hk : C ⊓ f.ker ≤ pCore 2 G)
    (hQ : pCore 2 G ≤ f.ker)
    (hz : Nat.Coprime p (Nat.card (center S))) (hr : 2 ≤ primeRank p S)
    (hG : primeRank p G ≤ 2) (ho : Odd p) (hout : IsPGroup 2 (MulAut.Outer S))
    (x : G) (hx : orderOf x = p) : x ∈ C := by
  let B := C ⊓ S.comap f
  let q := QuotientGroup.mk' (pCore 2 G)
  let j : B →* S := (f.comp B.subtype).codRestrict S (fun b => b.property.2)
  have hj : Function.Surjective j := by
    intro s
    obtain ⟨b,hb,he⟩ := hS s.property
    exact ⟨⟨b,hb,(show f b ∈ S from he.symm ▸ s.property)⟩,Subtype.ext he⟩
  let k := q.comp B.subtype
  have heq : k.ker = j.ker := by
    ext b
    constructor
    · intro hb
      apply Subtype.ext
      exact hQ ((QuotientGroup.eq_one_iff (b:G)).mp hb)
    · intro hb
      apply (QuotientGroup.eq_one_iff (b:G)).mpr
      exact hk ⟨b.property.1,congrArg Subtype.val hb⟩
  have hrange : k.range = B.map q := by
    rw [MonoidHom.range_comp,range_subtype]
  let e : B.map q ≃* S := (MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange k).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq heq).trans
        (QuotientGroup.quotientKerEquivOfSurjective j hj)))
  let : (B.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hcop : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  apply Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem q hcop C x hx
  by_cases hqx : q x = 1
  · exact hqx ▸ (C.map q).one_mem
  have hxq : orderOf (q x) = p := orderOf_eq_prime (by
    rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]) hqx
  apply map_mono (show B ≤ C from inf_le_left)
  apply prime_actor_mem_of_full_rank (B.map q) ?_ ?_ ?_ ho ?_ (q x) hxq
  · rwa [Nat.card_congr (centerCongr e).toEquiv]
  · rwa [primeRank_congr p e]
  · exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hG
  · exact hout.of_equiv (MulAut.outerCongr e).symm
end Theory.GroupTheory.CComponentPrimeRank
