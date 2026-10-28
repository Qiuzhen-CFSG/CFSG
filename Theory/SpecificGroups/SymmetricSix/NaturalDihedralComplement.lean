module

public import Theory.SpecificGroups.SymmetricSix.NaturalDihedralLifts
public import Theory.GroupTheory.DihedralPairKernel
public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Extending the retained dihedral complement over the polar kernel

The two supplied commuting lifts with identical kernel fixed spaces produce
a dihedral subgroup projecting injectively to the quotient Sylow two-group.
Its product with the original kernel has odd index forty-five. Gaschütz
extends this proved local complement to the original full kernel. The two
commuting lifts are essential inputs supplied by the original source pair.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
open scoped Matrix
variable {G : Type*} [Group G] [Finite G]

/-- The actual split four-group with equal kernel fixed spaces yields a
complement to the same full polar kernel, by the proved dihedral relation. -/
theorem exists_complement_of_same_kernel_fixed
    (q : G→*A6) (hq : Function.Surjective q)
    (e : q.ker≃*Multiplicative NaturalModule)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v)=
      Multiplicative.ofAdd ((polarRepresentation (q g).val).val *ᵥ (e v).toAdd))
    (x y : G) (hx2 : x^2=1) (hy2 : y^2=1) (hxy : Commute x y)
    (hqx : orderOf (q x)=2) (hqy : orderOf (q y)=2) (hne : q x≠q y)
    (hfixed : ∀ a∈q.ker,Commute a y → Commute a x) :
    ∃ K : Subgroup G, q.ker.IsComplement' K := by
  obtain ⟨s,hs,_,_,_,h4,hqo⟩ := exists_dihedral_lift_of_same_kernel_fixed
    q hq e he x y hx2 hy2 hxy hqx hqy hne hfixed
  obtain ⟨hK,hdis⟩ := Theory.GroupTheory.dihedral_pair_kernel_disjoint q x s
    hx2 (hs ▸ pow_orderOf_eq_one s) h4 hqo
  let K := closure ({x,s}:Set G)
  let H := q.ker⊔K
  have hkcard : Nat.card q.ker=16 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card NaturalModule=16
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hHcard : Nat.card H=128 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint q.ker K
      (by rw [normalizer_eq_top]; exact le_top) hdis,hkcard,hK]
  have hidx : q.ker.index=360 := by
    rw [index_eq_card,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hGcard : Nat.card G=5760 := by
    have hh := q.ker.card_mul_index
    rw [hkcard,hidx] at hh
    exact hh.symm
  have hHidx : H.index=45 := by
    have hh := H.card_mul_index
    rw [hHcard,hGcard] at hh
    omega
  let : IsMulCommutative q.ker := ⟨⟨fun a b => e.injective (by simp only [map_mul,mul_comm])⟩⟩
  exact exists_complement_of_coprime_overgroup q.ker H le_sup_left
    (by rw [hkcard,hHidx]; decide) ⟨K.subgroupOf H,isComplement'_subgroupOf_sup_of_disjoint q.ker K hdis⟩

end Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
