module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The rank inequalities for 16.3.9

Sylow detection compares K⟨t⟩ with T. Conjugation on L has kernel T_C,
whose rank is exactly two by its dihedral/semidihedral shape and its
explicit elementary four-group. The independent central involution
bound handles t outside K; the inside case has nontrivial center.

Source: Aschbacher–Smith, printed p.1180, first paragraph and (!).
No numerical rank for a simple model is assumed here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Restrict conjugation on L to T; its kernel is exactly T_C. -/
theorem sylow_rank_le (h : TerminalCounterexample T z L t) :
    primeRank 2 T ≤ primeRank 2 (commutingSylow T L) + primeRank 2 (MulAut L) := by
  let f : T →* MulAut L := L.normalizerMonoidHom.comp (inclusion h.sylow_le_normalizer)
  have hker : f.ker = (centralizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
    rfl
  have hf (x : T) : f x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
    change x ∈ f.ker ↔ _
    rw [hker]
    rfl
  let e : f.ker ≃* commutingSylow T L :=
    { toFun := fun x => ⟨x.1, x.1.2, (hf x.1).mp x.2⟩
      invFun := fun x => ⟨⟨x, x.2.1⟩, (hf _).mpr x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hr := primeRank_le_ker_add (p := 2) f
  rw [primeRank_equiv 2 e] at hr
  exact hr

/-- Inequality (!) of 16.3.9 for the actual K⟨t⟩. -/
theorem enlargement_rank_le (h : TerminalCounterexample T z L t)
    (hshape : NonterminalCentralizerShape T z L t) :
    primeRank 2 (enlargement t L ⊔ zpowers t : Subgroup G) ≤
      primeRank 2 (MulAut L) + 2 := by
  have hTC : primeRank 2 (commutingSylow T L) ≤ 2 := by
    rcases hshape.model with ⟨n, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rw [primeRank_equiv 2 e]
      exact dihedral_rank_le_two n
    · rw [primeRank_equiv 2 e]
      exact semidihedral_rank_le_two n hn
  have hr := sylow_rank_le h
  have hs := T.primeRank_eq
  have he := primeRank_le_of_injective 2
    (enlargement t L ⊔ zpowers t : Subgroup G).subtype Subtype.val_injective
  omega


/-- The exact two-rank asserted after 16.3.8. -/
theorem commutingSylow_rank_eq_two (h : TerminalCounterexample T z L t)
    (hshape : NonterminalCentralizerShape T z L t) :
    primeRank 2 (commutingSylow T L) = 2 := by
  apply le_antisymm
  · rcases hshape.model with ⟨n, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rw [primeRank_equiv 2 e]
      exact dihedral_rank_le_two n
    · rw [primeRank_equiv 2 e]
      exact semidihedral_rank_le_two n hn
  · let E := zpowers z ⊔ zpowers t
    let := (four_group h).1
    let : IsElementaryAbelian 2 (E.subgroupOf (commutingSylow T L)) :=
      IsElementaryAbelian.subgroupOf (four_le_commutingSylow h)
    apply IsElementaryAbelian.primeRank_ge_of_card (E.subgroupOf (commutingSylow T L))
    rw [Nat.card_congr (subgroupOfEquivOfLe (four_le_commutingSylow h)).toEquiv]
    exact (four_group h).2


/-- The outside alternative (i) of 16.3.9 increases two-rank by one. -/
theorem enlargement_rank_succ_le (h : TerminalCounterexample T z L t)
    (htK : t ∉ enlargement t L) :
    primeRank 2 (enlargement t L) + 1 ≤
      primeRank 2 (enlargement t L ⊔ zpowers t : Subgroup G) :=
  primeRank_succ_le_sup_zpowers _ t h.involution (enlargement_le h) htK

/-- Combine the outside lower bound with the faithful-action upper bound. -/
theorem enlargement_rank_succ_le_aut (h : TerminalCounterexample T z L t)
    (hshape : NonterminalCentralizerShape T z L t) (htK : t ∉ enlargement t L) :
    primeRank 2 (enlargement t L) + 1 ≤ primeRank 2 (MulAut L) + 2 :=
  (enlargement_rank_succ_le h htK).trans (enlargement_rank_le h hshape)

end CFSG.Quasithin.Chapter16.EnlargementSieve
