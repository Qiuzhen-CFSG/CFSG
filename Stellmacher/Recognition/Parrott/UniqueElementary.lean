module
public import Stellmacher.Recognition.Parrott.OuterInvolutionFixedSpace
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# Uniqueness of Parrott's elementary subgroup under the involution negation

Put H=C_G(z), J=O₂(H), and let E be the actual image of J′ in G. If every
involution of the mapped core lies in E, then E is the unique elementary
abelian subgroup of order32 contained in H. The involution premise is the
explicit contradiction assumption used to prove Parrott's Lemma 3.

For an elementary subgroup A of order32 in H, the supplied C5 semidirect
C4 quotient model bounds the image of A by2. If A contains an involution
y outside the core, the projection kernel consists of core involutions
commuting with y and therefore embeds in C_E(y), of order8. This would
bound |A| by16. Otherwise all of A lies in E, and equal cardinalities
force equality.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 3, p.675. The argument gives uniqueness throughout H,
which implies the Sylow-local uniqueness used in the source. It needs
neither simplicity nor the N₂ hypothesis.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

/-- Under the core-involution negation, the actual derived image is the unique elementary32 in H. -/
public theorem parrott_unique_elementary_of_core_involutions
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ A : Subgroup G, A ≤ H → IsElementaryAbelian 2 A → Nat.card A = 32 → A = E := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ A : Subgroup G, A ≤ H → IsElementaryAbelian 2 A → Nat.card A = 32 → A = E
  intro hcore A hAH hA hAcard
  let : IsElementaryAbelian 2 A := hA
  have hEcard : Nat.card E = 32 := by
    rw [card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)]
    exact (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hcore_mem (x : G) (hxA : x ∈ A) (hxJ : x ∈ J.map H.subtype) : x ∈ E := by
    by_cases hx : x = 1
    · simpa only [hx] using E.one_mem
    · exact hcore x hxJ (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxA) hx)
  by_cases hAJ : A ≤ J.map H.subtype
  · exact eq_of_le_of_card_ge (fun x hx => hcore_mem x hx (hAJ hx)) (by rw [hEcard, hAcard])
  · obtain ⟨y, hyA, hyJ⟩ := SetLike.not_le_iff_exists.mp hAJ
    let yH : H := ⟨y, hAH hyA⟩
    have hyH : yH ∉ J := by
      intro hy
      exact hyJ (mem_map_of_mem H.subtype hy)
    have hy2 : orderOf yH = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        exact elemPow_eq_one_of_isElementaryAbelian y hyA
      · intro hy
        exact hyH (hy ▸ J.one_mem)
    let C := (centralizer ({y} : Set G)).subgroupOf E
    have hCcard : Nat.card C = 8 := parrott_outer_involution_fixed_card z h yH hy2 hyH
    let A' := A.subgroupOf H
    let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAH
    obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
    let modelHom := e.toMonoidHom.comp (QuotientGroup.mk' J)
    let θ := modelHom.comp A'.subtype
    have hθrange : θ.range = A'.map modelHom := by
      rw [MonoidHom.range_comp, range_subtype]
    have himage : Nat.card θ.range ≤ 2 := by
      rw [hθrange]
      exact SemidirectProduct.elementary_two_subgroup_card_le_two φ _
        (IsElementaryAbelian.map modelHom)
    have hkerJ (x : θ.ker) : (((x : A') : H) : G) ∈ J.map H.subtype := by
      have hx : QuotientGroup.mk' J ((x : A') : H) = 1 := by
        apply e.injective
        have hxθ := x.property
        change e (QuotientGroup.mk' J ((x : A') : H)) = 1 at hxθ
        simpa only [map_one] using hxθ
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (N := J) _).mp hx)
    let i : θ.ker → C := fun x =>
      ⟨⟨(((x : A') : H) : G), hcore_mem _ (x : A').property (hkerJ x)⟩,
        mem_centralizer_singleton_iff.mpr (setLike_mul_comm (x : A').property hyA)⟩
    have hi : Function.Injective i := by
      intro x x' hxx
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun c : C => ((c : E) : G)) hxx
    have hkernel : Nat.card θ.ker ≤ 8 := by
      simpa only [hCcard] using Nat.card_le_card_of_injective i hi
    have hA'card : Nat.card A' = 32 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hAcard
    have hprod := θ.ker.card_mul_index
    rw [index_ker, hA'card] at hprod
    have hbound := Nat.mul_le_mul hkernel himage
    rw [hprod] at hbound
    norm_num at hbound

end Stellmacher.Recognition
