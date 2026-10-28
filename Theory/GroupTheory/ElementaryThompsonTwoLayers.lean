module

public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Two moved elementary layers force Thompson containment

Suppose Q has index at most two in S and contains two disjoint elementary
abelian layers centralizing Q. If S preserves each layer and every element
outside Q moves both, the elementary Thompson subgroup of S lies in Q.

For a maximum elementary subgroup A escaping Q, choose a in A outside Q.
The two disjoint nonzero displacement images of a have product order at
least four, whereas elementary replacement bounds its fixed index by two.
This supplies the two-block exclusion in Aschbacher--Smith 14.6.3(4),
printed p.1022, using the existing elementary Thompson fixed-index bound.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

private theorem displacement_range_four
    (E V W : Subgroup G) [IsElementaryAbelian 2 E]
    (hVE : V ≤ E) (hWE : W ≤ E) (hd : Disjoint V W)
    (a : G) (ha : a ∈ normalizer (E : Set G))
    (haV : a ∈ normalizer (V : Set G)) (haW : a ∈ normalizer (W : Set G))
    (hnV : a ∉ centralizer (V : Set G)) (hnW : a ∉ centralizer (W : Set G)) :
    4 ≤ (centralizer ({a} : Set G)).relIndex E := by
  let α := E.normalizerMonoidHom ⟨a,ha⟩
  let f : E →* E := α.toMonoidHom / MonoidHom.id E
  have hk : f.ker = (centralizer ({a} : Set G)).subgroupOf E := by
    ext x
    change α x / x = 1 ↔ (x : G) ∈ centralizer ({a} : Set G)
    rw [div_eq_one,Subtype.ext_iff,mem_centralizer_singleton_iff]
    simp only [α, normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.trans eq_comm
  have hidx : Nat.card f.range = (centralizer ({a} : Set G)).relIndex E := by
    rw [←index_ker,hk]
    rfl
  let V' := (V.subgroupOf E).map f
  let W' := (W.subgroupOf E).map f
  have hmap (B : Subgroup G) (hBE : B ≤ E) (hab : a ∈ normalizer (B : Set G)) :
      (B.subgroupOf E).map f ≤ B.subgroupOf E := by
    rintro _ ⟨x,hx,rfl⟩
    change E.subtype (α x / x) ∈ B
    rw [map_div, div_eq_mul_inv]
    change (α x : G) * (x:G)⁻¹ ∈ B
    simp only [α,normalizerMonoidHom_apply_apply_coe]
    exact B.mul_mem ((hab (x:G)).mp hx) (B.inv_mem hx)
  have hV : V' ≤ V.subgroupOf E := hmap V hVE haV
  have hW : W' ≤ W.subgroupOf E := hmap W hWE haW
  have hne (B : Subgroup G) (hBE : B ≤ E) (hn : a ∉ centralizer (B : Set G)) :
      (B.subgroupOf E).map f ≠ ⊥ := by
    intro hz
    have hh := (Subgroup.map_eq_bot_iff _).mp hz
    rw [hk] at hh
    apply hn
    intro b hb
    exact (mem_centralizer_singleton_iff.mp (hh (show (⟨b,hBE hb⟩ : E) ∈ B.subgroupOf E from hb)))
  have hVtwo : 2 ≤ Nat.card V' := Nat.succ_le_of_lt (V'.one_lt_card_iff_ne_bot.mpr (hne V hVE hnV))
  have hWtwo : 2 ≤ Nat.card W' := Nat.succ_le_of_lt (W'.one_lt_card_iff_ne_bot.mpr (hne W hWE hnW))
  have hdis : Disjoint V' W' := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    exact Subtype.ext (disjoint_iff_inf_le.mp hd ⟨hV hx.1,hW hx.2⟩)
  have hc : W' ≤ centralizer (V' : Set E) := by
    intro x _ y _
    exact mul_comm y x
  have hp := card_sup_eq_mul_of_normalizes_of_disjoint V' W'
    (hc.trans (Subgroup.centralizer_le_normalizer _)) hdis
  have hr : V' ⊔ W' ≤ f.range := sup_le (map_le_range _ _) (map_le_range _ _)
  rw [←hidx]
  calc
    4 ≤ Nat.card V' * Nat.card W' := Nat.mul_le_mul hVtwo hWtwo
    _ = Nat.card (V' ⊔ W' : Subgroup E) := hp.symm
    _ ≤ Nat.card f.range := card_le_of_le hr

/-- Two disjoint invariant elementary layers, both moved outside Q, force J(S) into Q. -/
theorem thompson_le_of_two_moved_layers
    (S Q V W : Subgroup G) (hQS : Q ≤ S) (hi : Q.relIndex S ≤ 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hVQ : V ≤ Q) (hWQ : W ≤ Q) (hVC : V ≤ centralizer (Q : Set G))
    (hWC : W ≤ centralizer (Q : Set G)) (hd : Disjoint V W)
    (hSV : S ≤ normalizer (V : Set G)) (hSW : S ≤ normalizer (W : Set G))
    (hmoveV : ∀ a ∈ S, a ∉ Q → a ∉ centralizer (V : Set G))
    (hmoveW : ∀ a ∈ S, a ∉ Q → a ∉ centralizer (W : Set G)) :
    elementaryAbelianMaxJ S ≤ Q := by
  apply sSup_le
  intro A hA
  by_contra hnot
  obtain ⟨a,ha,haQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let E := V ⊔ W
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.sup_of_le_centralizer (hWC.trans (centralizer_le hVQ))
  have hEC : E ≤ centralizer (Q : Set G) := sup_le hVC hWC
  have hSE : S ≤ normalizer (E : Set G) :=
    (le_inf hSV hSW).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hbound := (maxElementary_fixedIndex_le_relIndex S Q A E hQS
    (sup_le hVQ hWQ) hEC hA).1.trans
    ((maxElementary_fixedIndex_le_relIndex S Q A E hQS
      (sup_le hVQ hWQ) hEC hA).2.trans
        ((relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans hi))
  have hfour := displacement_range_four E V W le_sup_left le_sup_right hd a
    (hSE (hA.1 ha)) (hSV (hA.1 ha)) (hSW (hA.1 ha))
    (hmoveV a (hA.1 ha) haQ) (hmoveW a (hA.1 ha) haQ)
  have hfix : (centralizer ({a} : Set G)).relIndex E ≤ (centralizer (A : Set G)).relIndex E :=
    relIndex_le_of_le_left (centralizer_le (by simpa using ha)) index_ne_zero_of_finite
  omega


end Stellmacher
