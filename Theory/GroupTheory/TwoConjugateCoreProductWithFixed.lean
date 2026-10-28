module
public import Theory.GroupTheory.TwoConjugateCoreProduct
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Two-centralizer core products retaining a fixed kernel

Let U be a central subgroup of a finite p-group Q, with [Q,L] contained
in U and L p-perfect. Two conjugate actors generating L modulo Q force
Q = U C_Q(L) when their centralizer indices are at most n and
|U:C_U(L)| is at least n². The sharp product count first gives
Q = U C_Q(A,Aᵍ). This centralizer is L-invariant, and p-perfect
commutator idempotence makes it centralize L, even when C_U(L) is nontrivial.

This is the central-kernel version of the two-root-eight argument used at
Aschbacher--Smith 3.3.28, printed p.601; it does not assume a split module.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem product_of_central_relative_index (Q U C F : Subgroup G)
    (hUQ : U ≤ Q) (hCQ : C ≤ Q) (hc : U ≤ centralizer (Q : Set G))
    (hFU : F ≤ U) (hUF : U ⊓ C ≤ F) (hi : C.relIndex Q ≤ F.relIndex U) :
    Q = U ⊔ C := by
  have hn : U ≤ normalizer (C : Set G) :=
    (hc.trans (centralizer_le hCQ)).trans (centralizer_le_normalizer _)
  have hs := card_set_mul_mul_card_inf U C
  rw [← coe_mul_of_left_le_normalizer_right U C hn] at hs
  change Nat.card (U ⊔ C : Subgroup G) * Nat.card (U ⊓ C : Subgroup G) =
    Nat.card U * Nat.card C at hs
  have hq := relIndex_mul_relIndex (⊥ : Subgroup G) C Q bot_le hCQ
  have hu := relIndex_mul_relIndex (⊥ : Subgroup G) F U bot_le hFU
  simp only [relIndex_bot_left] at hq hu
  have hf := Nat.card_le_card_of_injective (inclusion hUF) (inclusion_injective hUF)
  have hbound := Nat.mul_le_mul hi hf
  have hpos : 0 < Nat.card (U ⊓ C : Subgroup G) := Nat.card_pos
  apply (eq_of_le_of_card_ge (sup_le hUQ hCQ) ?_).symm
  apply Nat.le_of_mul_le_mul_right (c := Nat.card (U ⊓ C : Subgroup G)) ?_ hpos
  calc
    Nat.card Q * Nat.card (U ⊓ C : Subgroup G) =
        Nat.card C * (C.relIndex Q * Nat.card (U ⊓ C : Subgroup G)) := by
      rw [← hq]; ac_rfl
    _ ≤ Nat.card C * (F.relIndex U * Nat.card F) := Nat.mul_le_mul_left _ hbound
    _ = Nat.card (U ⊔ C : Subgroup G) * Nat.card (U ⊓ C : Subgroup G) := by
      rw [mul_comm (F.relIndex U),hu,hs,mul_comm]

/-- A sharp centralizer bound gives the core product without removing the
fixed kernel of U. The required generation is only generation of L modulo Q. -/
theorem core_product_of_centralizer_index_with_fixed
    {p : ℕ} [Fact p.Prime] (Q U L K : Subgroup G)
    (hQ : IsPGroup p Q) (hL : IsPPerfect p L)
    (hUQ : U ≤ Q) (hc : U ≤ centralizer (Q : Set G))
    (hcomm : ⁅Q,L⁆ ≤ U) (hgen : L ≤ Q ⊔ K)
    (hi : (centralizer (K : Set G)).relIndex Q ≤
      (centralizer (L : Set G)).relIndex U) :
    Q = U ⊔ (Q ⊓ centralizer (L : Set G)) := by
  let C := Q ⊓ centralizer (K : Set G)
  let F := U ⊓ centralizer (L : Set G)
  have hUF : U ⊓ C ≤ F := by
    rintro u ⟨hu,huC⟩
    refine ⟨hu,?_⟩
    have hh : Q ⊔ K ≤ centralizer ({u} : Set G) := sup_le
      (fun q hq => mem_centralizer_singleton_iff.mpr (hc hu q hq))
      (fun k hk => mem_centralizer_singleton_iff.mpr (huC.2 k hk))
    exact fun l hl => mem_centralizer_singleton_iff.mp (hh (hgen hl))
  have hs : Q = U ⊔ C := product_of_central_relative_index Q U C F hUQ
    inf_le_left hc inf_le_left hUF (by simpa only [C,F,inf_relIndex_left] using hi)
  have hQN : Q ≤ normalizer (C : Set G) := by
    rw [hs]
    exact sup_le ((hc.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _))
      C.le_normalizer
  have hKN : K ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (K : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hLN : L ≤ normalizer (C : Set G) := hgen.trans (sup_le hQN hKN)
  have hCL : ⁅C,L⁆ ≤ F :=
    (le_inf ((commutator_mono (show C ≤ Q from inf_le_left) le_rfl).trans hcomm)
      (le_normalizer_iff_commutator_le_left.mp hLN)).trans hUF
  have hcentral : C ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← commutator_isPPerfect_idempotent L C hL (hQ.to_le inf_le_left) hLN]
    apply le_bot_iff.mp
    exact (commutator_mono (hCL.trans inf_le_right) le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le
  exact le_antisymm (hs.le.trans (sup_le_sup_left (le_inf inf_le_left hcentral) U))
    (sup_le hUQ inf_le_left)

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro a ha
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

/-- Two conjugate index bounds suffice for a core product even when U has
central fixed points. Only the conjugator must preserve Q. -/
theorem core_product_of_two_conjugate_indices_with_fixed
    {p : ℕ} [Fact p.Prime] (Q U L A : Subgroup G)
    (hQ : IsPGroup p Q) (hL : IsPPerfect p L)
    (hUQ : U ≤ Q) (hc : U ≤ centralizer (Q : Set G))
    (hcomm : ⁅Q,L⁆ ≤ U) (g : G) (hg : g ∈ normalizer (Q : Set G))
    (hgen : L ≤ Q ⊔ (A ⊔ A.map (MulAut.conj g).toMonoidHom))
    (n : ℕ) (hi : (centralizer (A : Set G)).relIndex Q ≤ n)
    (hindex : n * n ≤ (centralizer (L : Set G)).relIndex U) :
    Q = U ⊔ (Q ⊓ centralizer (L : Set G)) := by
  have hi' : (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex Q ≤ n := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (centralizer (A : Set G)) Q (MulAut.conj g).injective
    have hm : Q.map (MulAut.conj g).toMonoidHom = Q := mem_normalizer_iff_map_conj_eq.mp hg
    rw [centralizer_map_equiv,hm] at hh
    exact hh.le.trans hi
  apply core_product_of_centralizer_index_with_fixed Q U L _ hQ hL hUQ hc hcomm hgen
  have he : centralizer (A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) =
      centralizer (A : Set G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (show A ≤ A ⊔ A.map (MulAut.conj g).toMonoidHom from le_sup_left))
        (centralizer_le (show A.map (MulAut.conj g).toMonoidHom ≤
          A ⊔ A.map (MulAut.conj g).toMonoidHom from le_sup_right))
    · intro x hx
      have hh : A ⊔ A.map (MulAut.conj g).toMonoidHom ≤ centralizer ({x} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.mpr (hx.1 a ha))
        (fun a ha => mem_centralizer_singleton_iff.mpr (hx.2 a ha))
      exact fun k hk => mem_centralizer_singleton_iff.mp (hh hk)
  rw [he]
  exact relIndex_inf_le.trans ((Nat.mul_le_mul hi hi').trans hindex)

end Subgroup
