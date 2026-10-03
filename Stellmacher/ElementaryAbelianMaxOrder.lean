module

public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Maximum elementary-abelian order and elementary Thompson subgroups

For a finite subgroup `S`, `elementaryAbelianMaxOrder S` is the common order
of the elementary abelian subgroups in `elementaryAbelianMaxSubgroups S`.
Inclusion `S ≤ T` makes this order monotone.  When the two orders agree, every
maximal-order elementary abelian subgroup of `S` remains maximal in `T`, so
`elementaryAbelianMaxJ S ≤ elementaryAbelianMaxJ T`.  The order is also
invariant under ambient automorphisms.  A second comparison starts from the
weaker containment `elementaryAbelianMaxJ S ≤ T`; it is the exact form needed
for the normalizer subgroup occurring in (5.1)(c3).

These are the comparison facts required by the corrected lexicographic choice
in Stellmacher (5.1): first maximize this order, then the order of
`elementaryAbelianMaxJ`, and finally the order of the Sylow intersection.  The
first coordinate is essential; bare monotonicity of the order of
`elementaryAbelianMaxJ` is false even for a normal subgroup of index two.
This correction agrees with Kurzweil--Stellmacher, *The Theory of Finite
Groups*, Section 12.3, pp. 357--358, especially Lemmas 12.3.2--12.3.4, and
repairs the suppressed transfer in the proof of (5.1) in
`refs/latex/stellmacher-n-group.tex`, journal p. 27.
-/

namespace Stellmacher

universe u

variable {G : Type u} [Group G]

/-- A maximal-order elementary abelian subgroup exists in every finite
subgroup. -/
public theorem elementaryAbelianMaxSubgroups_nonempty
    [Finite G] (S : Subgroup G) :
    (elementaryAbelianMaxSubgroups S).Nonempty := by
  classical
  let := Fintype.ofFinite G
  let X : Set (Subgroup G) :=
    {A : Subgroup G | A ≤ S ∧ IsElementaryAbelian 2 A}
  have hX : X.Nonempty := by
    refine ⟨⊥, bot_le, ?_⟩
    have hbot := IsElementaryAbelian.zpowers_of_pow_eq_one
      (p := 2) (G := G) (x := 1) (by simp)
    rw [← Subgroup.zpowers_one_eq_bot]
    exact hbot
  have hXfin : X.Finite := X.toFinite
  obtain ⟨A, hA, hAmax⟩ :=
    hXfin.exists_maximalFor
      (f := fun A : Subgroup G => Nat.card A) X hX
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro B hBS hBe
  by_cases hle : Nat.card A ≤ Nat.card B
  · exact hAmax ⟨hBS, hBe⟩ hle
  · exact Nat.le_of_not_ge hle

/-- The common order of the maximal-order elementary abelian subgroups of
`S`. -/
public noncomputable def elementaryAbelianMaxOrder
    [Finite G] (S : Subgroup G) : Nat :=
  Nat.card ↥(Classical.choose (elementaryAbelianMaxSubgroups_nonempty S))

private theorem card_eq_elementaryAbelianMaxOrder
    [Finite G] (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    Nat.card A = elementaryAbelianMaxOrder S := by
  let A₀ : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty S)
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups S :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty S)
  apply Nat.le_antisymm
  · exact hA₀.2.2 A hA.1 hA.2.1
  · exact hA.2.2 A₀ hA₀.1 hA₀.2.1

/-- Inclusion of finite subgroups cannot decrease the maximum order of an
elementary abelian subgroup. If the maximum orders agree, the elementary
Thompson subgroup of the smaller subgroup lies in that of the larger one. -/
public theorem elementaryAbelianMaxOrder_le_and_j_le_of_eq
    [Finite G] (S T : Subgroup G) (hST : S ≤ T) :
    elementaryAbelianMaxOrder S ≤ elementaryAbelianMaxOrder T ∧
      (elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder T →
        elementaryAbelianMaxJ S ≤ elementaryAbelianMaxJ T) := by
  let A₀ : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty S)
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups S :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty S)
  let B₀ : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty T)
  have hB₀ : B₀ ∈ elementaryAbelianMaxSubgroups T :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty T)
  constructor
  · rw [← card_eq_elementaryAbelianMaxOrder S A₀ hA₀,
      ← card_eq_elementaryAbelianMaxOrder T B₀ hB₀]
    exact hB₀.2.2 A₀ (hA₀.1.trans hST) hA₀.2.1
  · intro heq
    unfold elementaryAbelianMaxJ
    refine sSup_le ?_
    intro A hA
    apply le_sSup
    refine ⟨hA.1.trans hST, hA.2.1, ?_⟩
    intro B hBT hBe
    calc
      Nat.card B ≤ Nat.card B₀ := hB₀.2.2 B hBT hBe
      _ = elementaryAbelianMaxOrder T :=
        card_eq_elementaryAbelianMaxOrder T B₀ hB₀
      _ = elementaryAbelianMaxOrder S := heq.symm
      _ = Nat.card A :=
        (card_eq_elementaryAbelianMaxOrder S A hA).symm

/-- If a subgroup `T` contains the elementary Thompson subgroup of `S`, then
the maximum elementary-abelian order of `S` is at most that of `T`.  Equality
again makes the elementary Thompson subgroup monotone.  This stronger form is
needed in Stellmacher (5.1), where the intermediate subgroup is a normalizer
of `elementaryAbelianMaxJ S` and need not contain all of `S`. -/
public theorem elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    [Finite G] (S T : Subgroup G)
    (hJT : elementaryAbelianMaxJ S ≤ T) :
    elementaryAbelianMaxOrder S ≤ elementaryAbelianMaxOrder T ∧
      (elementaryAbelianMaxOrder S = elementaryAbelianMaxOrder T →
        elementaryAbelianMaxJ S ≤ elementaryAbelianMaxJ T) := by
  let A₀ : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty S)
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups S :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty S)
  let B₀ : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty T)
  have hB₀ : B₀ ∈ elementaryAbelianMaxSubgroups T :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty T)
  have hA₀T : A₀ ≤ T := (le_sSup hA₀).trans hJT
  constructor
  · rw [← card_eq_elementaryAbelianMaxOrder S A₀ hA₀,
      ← card_eq_elementaryAbelianMaxOrder T B₀ hB₀]
    exact hB₀.2.2 A₀ hA₀T hA₀.2.1
  · intro heq
    unfold elementaryAbelianMaxJ
    refine sSup_le ?_
    intro A hA
    apply le_sSup
    refine ⟨(le_sSup hA).trans hJT, hA.2.1, ?_⟩
    intro B hBT hBe
    calc
      Nat.card B ≤ Nat.card B₀ := hB₀.2.2 B hBT hBe
      _ = elementaryAbelianMaxOrder T :=
        card_eq_elementaryAbelianMaxOrder T B₀ hB₀
      _ = elementaryAbelianMaxOrder S := heq.symm
      _ = Nat.card A :=
        (card_eq_elementaryAbelianMaxOrder S A hA).symm

private theorem map_symm_map (e : G ≃* G) (A : Subgroup G) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem map_map_symm (e : G ≃* G) (A : Subgroup G) :
    (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

private theorem maxFamily_map
    (e : G ≃* G) (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    A.map e.toMonoidHom ∈
      elementaryAbelianMaxSubgroups (S.map e.toMonoidHom) := by
  rcases hA with ⟨hAS, hAelem, hAmax⟩
  refine ⟨Subgroup.map_mono hAS, hAelem.map e.toMonoidHom, ?_⟩
  intro B hBS hBelem
  let B' : Subgroup G := B.map e.symm.toMonoidHom
  have hB'S : B' ≤ S := by
    change B.map e.symm.toMonoidHom ≤ S
    apply (Subgroup.map_le_map_iff_of_injective
      (f := e.toMonoidHom) e.injective).mp
    rw [map_map_symm e B]
    exact hBS
  have hB'elem : IsElementaryAbelian 2 B' :=
    hBelem.map e.symm.toMonoidHom
  have hcard := hAmax B' hB'S hB'elem
  have hcardB : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective
      (K := B) (f := e.symm.toMonoidHom) e.symm.injective
  calc
    Nat.card B = Nat.card B' := hcardB.symm
    _ ≤ Nat.card A := hcard
    _ = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective
        (K := A) (f := e.toMonoidHom) e.injective).symm

/-- The maximum elementary-abelian order is invariant under ambient group
automorphisms. -/
public theorem elementaryAbelianMaxOrder_map_equiv
    [Finite G] (e : G ≃* G) (S : Subgroup G) :
    elementaryAbelianMaxOrder (S.map e.toMonoidHom) =
      elementaryAbelianMaxOrder S := by
  let A : Subgroup G :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty S)
  have hA : A ∈ elementaryAbelianMaxSubgroups S :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty S)
  have hmap : A.map e.toMonoidHom ∈
      elementaryAbelianMaxSubgroups (S.map e.toMonoidHom) :=
    maxFamily_map e S A hA
  calc
    elementaryAbelianMaxOrder (S.map e.toMonoidHom) =
        Nat.card (A.map e.toMonoidHom) :=
      (card_eq_elementaryAbelianMaxOrder
        (S.map e.toMonoidHom) (A.map e.toMonoidHom) hmap).symm
    _ = Nat.card A :=
      Subgroup.card_map_of_injective
        (K := A) (f := e.toMonoidHom) e.injective
    _ = elementaryAbelianMaxOrder S :=
      card_eq_elementaryAbelianMaxOrder S A hA

end Stellmacher
