module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PrimeRankProduct

/-! Cardinality and cubic rank of an actual commuting centerless conjugate
pair. The embeddings into the original group are retained. These are the
pair comparisons in source 2.5.19, printed pp.563–564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pair_disjoint (P : Subgroup G) (hz : center P = ⊥)
    (t : G) (hc : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G)) :
    Disjoint P (P.map (MulAut.conj t).toMonoidHom) := by
  apply disjoint_def.mpr
  intro x hxP hxT
  have hxZ : (⟨x,hxP⟩ : P) ∈ center P :=
    mem_center_iff.mpr (fun y => Subtype.ext (hc y.property x hxT).symm)
  rw [hz,mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

omit [Finite G] in
theorem centerless_conjugate_pair_card
    (P : Subgroup G) (hz : center P = ⊥) (t : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G)) :
    Nat.card (P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) = Nat.card P ^ 2 := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting P
    (P.map (MulAut.conj t).toMonoidHom) (pair_disjoint P hz t hc) hc
  have hc : Nat.card (P.map (MulAut.conj t).toMonoidHom) = Nat.card P :=
    (Nat.card_congr ((MulAut.conj t).subgroupMap P).toEquiv).symm
  rw [← Nat.card_congr e.toEquiv,Nat.card_prod,hc,pow_two]

theorem centerless_conjugate_pair_three_rank
    (P : Subgroup G) (hz : center P = ⊥) (t : G)
    (hc : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G))
    (hr : 1 ≤ primeRank 3 P) :
    2 ≤ primeRank 3 (P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  have he : primeRank 3 (P.map (MulAut.conj t).toMonoidHom) = primeRank 3 P :=
    (primeRank_equiv 3 ((MulAut.conj t).subgroupMap P)).symm
  rw [primeRank_sup_eq_add_of_disjoint_commuting P _ (pair_disjoint P hz t hc) hc,he]
  omega
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
