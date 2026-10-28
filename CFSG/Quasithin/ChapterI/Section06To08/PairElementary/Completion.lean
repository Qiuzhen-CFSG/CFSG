module

public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.NormalizerAction
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Completion of the elementary TI-pair theorem

This module assembles I.6.2(1) and (2a), with the intended distinctness
hypothesis `V ≠ A` retained explicitly. Equal rank of finite elementary abelian
2-groups is expressed by equal orders. The common positive rank of the mutual
normalizers is witnessed by a common order `2 ^ n`.

When `U = V`, equality of orders forces `B = A`; the multiplication
isomorphism of the mutual normalizers therefore gives the internal direct
product `X = V × A`. A nonidentity element of `C_A(V)` forces `U = V` by the
TI centralizer criterion.

For the 2-group specialization, nontriviality and relative normality of `Y`
give a nonidentity element of `Z(X) ∩ Y` by the fixed-point theorem. If both
mutual normalizers were proper, the centralizer descriptions would put this
element in both disjoint factors `U` and `B`, a contradiction. This proof uses
no quotient recognition or Shult theorem.

The final theorem uses the source hypotheses directly. Every product
isomorphism records multiplication in the ambient group, and normality is
inside `X`, not in the ambient group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.6.2, printed pp. 424--425.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

/-- If the first mutual normalizer is full, so is the second. -/
theorem ti_pair_full_normalizer_right [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) = V) :
    A ⊓ Subgroup.normalizer (V : Set G) = A := by
  apply Subgroup.eq_of_le_of_card_ge inf_le_left
  have h := ti_pair_mutual_normalizers_card_eq V A hVA hV hA hcard
  rw [hU, hcard] at h
  exact h.le

/-- I.6.2(1): multiplication realizes the generated group as the internal
direct product when `N_V(A) = V`. -/
theorem ti_pair_mulEquiv_of_full_normalizer [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) = V) :
    ∃ e : V × A ≃* ↥(V ⊔ A),
      ∀ v a, (e (v, a) : G) = (v : G) * (a : G) := by
  have hB := ti_pair_full_normalizer_right V A hVA hV hA hcard hU
  obtain ⟨e, he⟩ := ti_pair_mutual_normalizers_mulEquiv V A hVA
  let f := (MulEquiv.subgroupCongr hU.symm).prodCongr (MulEquiv.subgroupCongr hB.symm)
  let g := MulEquiv.subgroupCongr (congrArg₂ (· ⊔ ·) hU hB)
  refine ⟨(f.trans e).trans g, ?_⟩
  intro v a
  exact he (f (v, a)).1 (f (v, a)).2

/-- The particular case of I.6.2(1): a nontrivial `C_A(V)` forces `N_V(A) = V`. -/
theorem ti_pair_full_normalizer_of_centralizer_ne_bot (V A : Subgroup G)
    (hVA : Disjoint V A) (hA : IsTISubgroup A)
    (hC : A ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥) :
    V ⊓ Subgroup.normalizer (A : Set G) = V := by
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
  have hb1 : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have hbN := Subgroup.centralizer_le_normalizer (V : Set G) b.property.2
  rw [ti_pair_opposite_normalizer_eq_centralizer A V hVA.symm hA
    b.property.1 hbN hb1]
  apply inf_eq_left.mpr
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (show Commute v (b : G) from b.property.2 v hv)

/-- A TI-pair generating a 2-group has full mutual normalizers. The proof
uses a nonidentity central fixed point in the normal subgroup `Y`. -/
theorem ti_pair_full_normalizer_of_isPGroup [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥)
    (hX : IsPGroup 2 ↥(V ⊔ A)) :
    V ⊓ Subgroup.normalizer (A : Set G) = V := by
  let U := V ⊓ Subgroup.normalizer (A : Set G)
  let B := A ⊓ Subgroup.normalizer (V : Set G)
  let X := V ⊔ A
  let Y := U ⊔ B
  by_contra hproper
  have hBproper : B ≠ A := by
    intro hB
    exact hproper (ti_pair_full_normalizer_right A V hVA.symm hA hV hcard.symm hB)
  obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ V ≤ U from fun h => hproper (le_antisymm inf_le_left h))
  obtain ⟨a, ha, haB⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ A ≤ B from fun h => hBproper (le_antisymm inf_le_left h))
  have hYX : Y ≤ X := sup_le
    (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  let D := Y.subgroupOf X
  have hD : D ≠ ⊥ := by
    intro hD
    have hdis := Subgroup.subgroupOf_eq_bot.mp hD
    have hY : Y = ⊥ := le_antisymm (fun y hy => hdis.le_bot ⟨hy, hYX hy⟩) bot_le
    exact hU (le_antisymm (hY ▸ (le_sup_left : U ≤ Y)) bot_le)
  let : D.Normal := ti_pair_normal_subgroupOf V A hVA hV hA
  have hZ := Subgroup.center_inf_ne_bot_of_normal hX D hD
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hzY : ((z : X) : G) ∈ Y := z.property.2
  have hcentral : ∀ x ∈ X, Commute ((z : X) : G) x := by
    intro x hx
    have h := Subgroup.mem_center_iff.mp z.property.1 ⟨x, hx⟩
    exact (congrArg (fun t : X => (t : G)) h).symm
  have hzU : ((z : X) : G) ∈ U := by
    change ((z : X) : G) ∈ V ⊓ Subgroup.normalizer (A : Set G)
    rw [← ti_pair_centralizer_eq V A hVA hA hv hvU]
    exact ⟨hzY, Subgroup.mem_centralizer_singleton_iff.mpr
      (hcentral v ((show V ≤ X from le_sup_left) hv))⟩
  have hzB : ((z : X) : G) ∈ B := by
    change ((z : X) : G) ∈ A ⊓ Subgroup.normalizer (V : Set G)
    rw [← ti_pair_centralizer_eq_right V A hVA hV ha haB]
    exact ⟨hzY, Subgroup.mem_centralizer_singleton_iff.mpr
      (hcentral a ((show A ≤ X from le_sup_right) ha))⟩
  have hz1 : ((z : X) : G) = 1 := hVA.le_bot ⟨hzU.1, hzB.1⟩
  exact hz (Subtype.ext (Subtype.ext hz1))



/-- The two factors centralize each other in the full-normalizer case. -/
theorem ti_pair_commute_of_full_normalizer [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) = V) :
    V ≤ Subgroup.centralizer (A : Set G) := by
  have hB := ti_pair_full_normalizer_right V A hVA hV hA hcard hU
  intro v hv a ha
  have hvU : v ∈ V ⊓ Subgroup.normalizer (A : Set G) := hU.symm ▸ hv
  have haB : a ∈ A ⊓ Subgroup.normalizer (V : Set G) := hB.symm ▸ ha
  exact (ti_pair_commute_of_mutual_normalizers V A hVA hv hvU.2 ha haB.2).symm

/-- The 2-group specialization, with commutation and the multiplication
isomorphism preserving the given embeddings of `V` and `A`. -/
theorem ti_pair_directProduct_of_isPGroup [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥)
    (hX : IsPGroup 2 ↥(V ⊔ A)) :
    V ≤ Subgroup.centralizer (A : Set G) ∧
      ∃ e : V × A ≃* ↥(V ⊔ A),
        ∀ v a, (e (v, a) : G) = (v : G) * (a : G) := by
  have hfull := ti_pair_full_normalizer_of_isPGroup V A hVA hV hA hcard hU hX
  exact ⟨ti_pair_commute_of_full_normalizer V A hVA hV hA hcard hfull,
    ti_pair_mulEquiv_of_full_normalizer V A hVA hV hA hcard hfull⟩

/-- The mutual normalizers have the same positive elementary-abelian rank,
expressed by their orders being the same power of two. -/
theorem ti_pair_mutual_normalizers_common_rank [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : Disjoint V A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥) :
    ∃ n > 0, Nat.card ↥(V ⊓ Subgroup.normalizer (A : Set G)) = 2 ^ n ∧
      Nat.card ↥(A ⊓ Subgroup.normalizer (V : Set G)) = 2 ^ n := by
  have hp : IsPGroup 2 ↥(V ⊓ Subgroup.normalizer (A : Set G)) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective
      (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  obtain ⟨n, hn, hc⟩ := hp.nontrivial_iff_card.mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hU)
  exact ⟨n, hn, hc, (ti_pair_mutual_normalizers_card_eq V A hVA hV hA hcard).symm.trans hc⟩

open scoped commutatorElement

/-- I.6.2(1) and (2a), together with the mutual centralizer and rank statements
from its proof and the elementary 2-group specialization. Distinctness repairs
the omitted source hypothesis. The last clause applies whenever `v ∈ V − U`,
so in particular gives the assertion in the proper-normalizer case. -/
theorem lemma_I_6_2_elementary [Finite G] (V A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVA : V ≠ A) (hV : IsTISubgroup V) (hA : IsTISubgroup A)
    (hcard : Nat.card V = Nat.card A)
    (hcross : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≠ V →
      Disjoint (A.map (MulAut.conj g).toMonoidHom) V)
    (hU : V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥) :
    let U := V ⊓ Subgroup.normalizer (A : Set G)
    let B := A ⊓ Subgroup.normalizer (V : Set G)
    let X := V ⊔ A
    let Y := U ⊔ B
    (∃ e : U × B ≃* Y, ∀ u b, (e (u, b) : G) = (u : G) * (b : G)) ∧
    (Y.subgroupOf X).Normal ∧
    (∃ n > 0, Nat.card U = 2 ^ n ∧ Nat.card B = 2 ^ n) ∧
    B ≠ ⊥ ∧
    (∀ u ∈ U, u ≠ 1 → B = A ⊓ Subgroup.centralizer ({u} : Set G)) ∧
    (∀ b ∈ B, b ≠ 1 → U = V ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ((U = V ∨ A ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ ∨ IsPGroup 2 X) →
      V ≤ Subgroup.centralizer (A : Set G) ∧
      ∃ e : V × A ≃* X, ∀ v a, (e (v, a) : G) = (v : G) * (a : G)) ∧
    (∀ v ∈ V, v ∉ U → Y ⊓ Subgroup.centralizer ({v} : Set G) = U ∧
      ⁅Y, Subgroup.zpowers v⁆ = U) := by
  have hd := ti_pair_disjoint_of_distinct V A hVA hcross
  have hB : A ⊓ Subgroup.normalizer (V : Set G) ≠ ⊥ := by
    intro h
    apply hU
    apply Subgroup.card_eq_one.mp
    rw [ti_pair_mutual_normalizers_card_eq V A hd hV hA hcard, h, Subgroup.card_bot]
  refine ⟨ti_pair_mutual_normalizers_mulEquiv V A hd,
    ti_pair_normal_subgroupOf V A hd hV hA,
    ti_pair_mutual_normalizers_common_rank V A hd hV hA hcard hU,
    hB, ?_, ?_, ?_, ?_⟩
  · intro u hu hu1
    exact ti_pair_opposite_normalizer_eq_centralizer V A hd hV hu.1 hu.2 hu1
  · intro b hb hb1
    exact ti_pair_opposite_normalizer_eq_centralizer A V hd.symm hA hb.1 hb.2 hb1
  · intro h
    have hfull : V ⊓ Subgroup.normalizer (A : Set G) = V := by
      rcases h with hfull | hcentral | hX
      · exact hfull
      · exact ti_pair_full_normalizer_of_centralizer_ne_bot V A hd hA hcentral
      · exact ti_pair_full_normalizer_of_isPGroup V A hd hV hA hcard hU hX
    exact ⟨ti_pair_commute_of_full_normalizer V A hd hV hA hcard hfull,
      ti_pair_mulEquiv_of_full_normalizer V A hd hV hA hcard hfull⟩
  · intro v hv hvU
    exact ⟨ti_pair_centralizer_eq V A hd hA hv hvU,
      ti_pair_commutator_eq V A hd hV hA hcard hv hvU⟩

end CFSG.Quasithin.ChapterI.Section06To08
