module

public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Preservation of the other elementary plane

An actor normalizing a group covered, on elementary subgroups, by two distinct
elementary planes must normalize the second plane if it normalizes the first.
The proof retains the two actual subgroups and uses their equal finite orders.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem normalizes_other_elementary_plane
    (R A B C : Subgroup G) (hBR : B≤R)
    (hB : IsElementaryAbelian 2 B)
    (hc : Nat.card A=Nat.card B) (hne : B≠A)
    (hcover : ∀ X : Subgroup G, IsElementaryAbelian 2 X → X≤R → X≤A ∨ X≤B)
    (hCR : C≤normalizer (R : Set G)) (hCA : C≤normalizer (A : Set G)) :
    C≤normalizer (B : Set G) := by
  intro c hcC
  apply mem_normalizer_iff_map_conj_eq.mpr
  let f := (MulAut.conj c).toMonoidHom
  have hi : Function.Injective f := (MulAut.conj c).injective
  have hRf : R.map f=R := mem_normalizer_iff_map_conj_eq.mp (hCR hcC)
  have hAf : A.map f=A := mem_normalizer_iff_map_conj_eq.mp (hCA hcC)
  let := hB
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map _
  have hle : B.map f≤R := (map_mono hBR).trans_eq hRf
  rcases hcover (B.map f) inferInstance hle with h | h
  · have he : B.map f=A := eq_of_le_of_card_ge h (by rw [card_map_of_injective hi,hc])
    exact (hne (Subgroup.map_injective hi (he.trans hAf.symm))).elim
  · change B.map f=B
    exact eq_of_le_of_card_ge h (by rw [card_map_of_injective hi])

end Subgroup
