module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
/-!
# Cardinality of a central displacement group

If conjugation by K acts transitively on a central coset tZ, its
displacement homomorphism has image Z. When C_K(t)=Z, the kernel is
also Z, so |K|=|Z|². The proof uses the kernel-index cardinality formula
and works with Nat.card without a finiteness hypothesis.

Source application: Aschbacher–Smith, Lemma 2.4.21, printed p.536.
-/
public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem card_eq_square_of_central_displacement
    (K Z : Subgroup G) (t : G) (hZK : Z ≤ K)
    (hcent : Z ≤ centralizer (K : Set G))
    (hfixed : K ⊓ centralizer ({t} : Set G) = Z)
    (hquad : ⁅K,zpowers t⁆ ≤ Z)
    (htrans : ∀ z ∈ Z, ∃ k ∈ K, k*t*k⁻¹=t*z) :
    Nat.card K = Nat.card Z ^ 2 := by
  have hcross {k : G} (hk : k ∈ K) : ⁅k,t⁆ ∈ Z :=
    hquad (commutator_mem_commutator hk (mem_zpowers t))
  have hcomm {k l : G} (hk : k ∈ K) (hl : l ∈ K) : Commute k ⁅l,t⁆ :=
    mem_centralizer_iff.mp (hcent (hcross hl)) k hk
  let q : K →* G := {
    toFun k := ⁅(k:G),t⁆
    map_one' := by simp
    map_mul' k l := by
      change ⁅(k:G)*(l:G),t⁆=⁅(k:G),t⁆*⁅(l:G),t⁆
      rw [commutatorElement_mul_left_eq_conj_mul,(hcomm k.property l.property).eq,
        mul_inv_cancel_right]
      exact (hcomm (hZK (hcross k.property)) l.property).symm.eq }
  have hk : q.ker = Z.subgroupOf K := by
    ext k
    change ⁅(k:G),t⁆=1 ↔ (k:G) ∈ Z
    rw [commutatorElement_eq_one_iff_commute,←hfixed]
    exact ⟨fun h => ⟨k.property,mem_centralizer_singleton_iff.mpr h.eq⟩,
      fun h => (mem_centralizer_singleton_iff.mp h.2)⟩
  have hr : q.range = Z := by
    apply le_antisymm
    · rintro z ⟨k,rfl⟩
      exact hcross k.property
    · intro z hz
      obtain ⟨k,hk,he⟩ := htrans z hz
      refine ⟨⟨k,hk⟩,?_⟩
      change k*t*k⁻¹*t⁻¹=z
      rw [he]
      have hzt := mem_centralizer_singleton_iff.mp ((show z ∈ K ⊓ centralizer ({t}:Set G) from hfixed.symm ▸ hz).2)
      rw [←hzt,mul_inv_cancel_right]
  have hcard := q.ker.card_mul_index
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv] at hcard
  exact hcard.symm.trans (pow_two _).symm
end Subgroup

