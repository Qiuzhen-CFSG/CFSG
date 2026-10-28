module
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Core splitting from two conjugate centralizer indices

A central layer V of Q splits off once its order equals the upper bound
on the index of a common centralizer. If the two actors generate modulo Q,
the complement is normal in the generated group. When [Q,L] lies in V
and C_V(L) is trivial, that complement is exactly C_Q(L).

The second theorem obtains the bound from two conjugate centralizers.
This is the finite-group index argument in Aschbacher--Smith 13.3.10(2),
printed p.888, applied in OriginalUnitaryBaumann.CoreProduct.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem product_of_central_index (Q V C : Subgroup G)
    (hVQ : V ≤ Q) (hCQ : C ≤ Q) (hc : V ≤ centralizer (Q : Set G))
    (hd : Disjoint V C) (hi : C.relIndex Q ≤ Nat.card V) : Q = V ⊔ C := by
  have hn : V ≤ normalizer (C : Set G) :=
    (hc.trans (centralizer_le hCQ)).trans (centralizer_le_normalizer _)
  have hs := card_set_mul_mul_card_inf V C
  rw [←coe_mul_of_left_le_normalizer_right V C hn,hd.eq_bot,Nat.card_unique (α := (⊥ : Subgroup G)),mul_one] at hs
  change Nat.card (V ⊔ C : Subgroup G) = Nat.card V * Nat.card C at hs
  have hq := relIndex_mul_relIndex (⊥ : Subgroup G) C Q bot_le hCQ
  rw [relIndex_bot_left,relIndex_bot_left] at hq
  apply (eq_of_le_of_card_ge (sup_le hVQ hCQ) ?_).symm
  rw [hs,←hq]
  exact Nat.mul_le_mul_left (Nat.card C) hi |>.trans_eq (Nat.mul_comm _ _)

/-- A sharp centralizer-index bound splits a central layer from the core.
The complement centralizes L because the quotient generators normalize it
and the whole L-commutator lies in the disjoint central layer. -/
theorem core_product_of_centralizer_index (Q V L K : Subgroup G)
    (hVQ : V ≤ Q) (hc : V ≤ centralizer (Q : Set G))
    (hcomm : ⁅Q,L⁆ ≤ V) (hgen : Q ⊔ K = ⊤)
    (hfixK : V ⊓ centralizer (K : Set G) = ⊥)
    (hfixL : V ⊓ centralizer (L : Set G) = ⊥)
    (hi : (Q ⊓ centralizer (K : Set G)).relIndex Q ≤ Nat.card V) :
    Q = V ⊔ (Q ⊓ centralizer (L : Set G)) ∧
      Disjoint V (Q ⊓ centralizer (L : Set G)) ∧
      Q ⊓ centralizer (L : Set G) ≤ centralizer (K : Set G) := by
  let C := Q ⊓ centralizer (K : Set G)
  let D := Q ⊓ centralizer (L : Set G)
  have hd : Disjoint V C := disjoint_iff.mpr (le_bot_iff.mp
    ((inf_le_inf_left V (show C ≤ centralizer (K : Set G) from inf_le_right)).trans hfixK.le))
  have hs : Q = V ⊔ C := product_of_central_index Q V C hVQ inf_le_left hc hd hi
  have hQN : Q ≤ normalizer (C : Set G) := by
    rw [hs]
    exact sup_le ((hc.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _))
      C.le_normalizer
  have hKN : K ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (K : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hn : (⊤ : Subgroup G) ≤ normalizer (C : Set G) := hgen ▸ sup_le hQN hKN
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hCL : C ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf ((commutator_mono (show C ≤ Q from inf_le_left) le_rfl).trans hcomm)
      (commutator_le_left C L)).trans hd.eq_bot.le
  have hCD : C ≤ D := le_inf inf_le_left hCL
  have hdD : Disjoint V D := disjoint_iff.mpr (le_bot_iff.mp
    ((inf_le_inf_left V (show D ≤ centralizer (L : Set G) from inf_le_right)).trans hfixL.le))
  have hDC : D ≤ C := by
    intro d hdD'
    have hh : d ∈ ((V : Set G) * (C : Set G)) := by
      rw [←coe_mul_of_left_le_normalizer_right V C (hVQ.trans hQN),←hs]
      exact hdD'.1
    obtain ⟨v,hv,c,hc',he⟩ := hh
    have hvD : v ∈ D := by
      have hh := D.mul_mem hdD' (D.inv_mem (hCD hc'))
      rwa [←he,mul_inv_cancel_right] at hh
    have hvone : v = 1 := hdD.eq_bot.le ⟨hv,hvD⟩
    change v * c = d at he
    rw [hvone,one_mul] at he
    exact he ▸ hc'
  have he : D = C := le_antisymm hDC hCD
  exact ⟨hs.trans (congrArg (V ⊔ ·) he.symm),hdD,hDC.trans inf_le_right⟩

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

/-- Two conjugate centralizers of index at most n give a direct core product
when their images generate modulo Q and the central layer has order at least n². -/
theorem core_product_of_two_conjugate_indices (Q V L A : Subgroup G) [Q.Normal]
    (hVQ : V ≤ Q) (hc : V ≤ centralizer (Q : Set G))
    (hcomm : ⁅Q,L⁆ ≤ V) (g : G)
    (hgen : Q ⊔ (A ⊔ A.map (MulAut.conj g).toMonoidHom) = ⊤)
    (hfixL : V ⊓ centralizer (L : Set G) = ⊥)
    (n : ℕ) (hi : (centralizer (A : Set G)).relIndex Q ≤ n)
    (hcard : n * n ≤ Nat.card V) :
    Q = V ⊔ (Q ⊓ centralizer (L : Set G)) ∧
      Disjoint V (Q ⊓ centralizer (L : Set G)) ∧
      Q ⊓ centralizer (L : Set G) ≤ centralizer (A : Set G) := by
  let K := A ⊔ A.map (MulAut.conj g).toMonoidHom
  have hfixK : V ⊓ centralizer (K : Set G) = ⊥ := by
    apply le_bot_iff.mp
    rintro v ⟨hv,hvK⟩
    apply hfixL.le
    refine ⟨hv,?_⟩
    have htot : Q ⊔ K ≤ centralizer ({v} : Set G) := by
      apply sup_le
      · intro q hq
        exact (mem_centralizer_singleton_iff).mpr (hc hv q hq)
      · intro k hk
        exact (mem_centralizer_singleton_iff).mpr (hvK k hk)
    intro l hl
    have hh := htot (hgen ▸ mem_top l)
    exact (mem_centralizer_singleton_iff).mp hh
  have hi' : (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex Q ≤ n := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (centralizer (A : Set G)) Q (MulAut.conj g).injective
    rw [centralizer_map_equiv,show Q.map (MulAut.conj g).toMonoidHom = Q from Normal.map_conj_eq Q g] at hh
    exact hh.le.trans hi
  have hcent : centralizer (K : Set G) =
      centralizer (A : Set G) ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (show A ≤ K from le_sup_left))
        (centralizer_le (show A.map (MulAut.conj g).toMonoidHom ≤ K from le_sup_right))
    · intro x hx
      have hh : K ≤ centralizer ({x} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.mpr (hx.1 a ha))
        (fun a ha => mem_centralizer_singleton_iff.mpr (hx.2 a ha))
      exact fun k hk => mem_centralizer_singleton_iff.mp (hh hk)
  have hbound : (Q ⊓ centralizer (K : Set G)).relIndex Q ≤ Nat.card V := by
    rw [inf_relIndex_left,hcent]
    exact relIndex_inf_le.trans ((Nat.mul_le_mul hi hi').trans hcard)
  obtain ⟨hs,hd,hk⟩ := core_product_of_centralizer_index Q V L K hVQ hc hcomm
    hgen hfixK hfixL hbound
  exact ⟨hs,hd,hk.trans (centralizer_le (show A ≤ K from le_sup_left))⟩

end Subgroup
