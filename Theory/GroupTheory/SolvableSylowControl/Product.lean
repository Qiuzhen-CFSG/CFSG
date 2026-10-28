module
public import Theory.GroupTheory.SolvableSylowControl

/-!
# Solvable Sylow control in direct products

A Sylow subgroup of a direct product is the product of its two projections.
A solvable overgroup projects to solvable overgroups of those Sylows, so
factorwise normalizer control gives control in the product. This is used
for the original Borel of a marked PSL₂(16) square in 14.6.14.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SolvableSylowControl
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime]

/-- Intrinsic solvable Sylow control is preserved by direct products. -/
theorem prod (hA : SolvableSylowControl p A) (hB : SolvableSylowControl p B) :
    SolvableSylowControl p (A × B) := by
  intro S H hs hSH
  let f := MonoidHom.fst A B
  let g := MonoidHom.snd A B
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup p ((S1 : Subgroup A).prod (S2 : Subgroup B)) := by
    obtain ⟨m,hm⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,hm,hn,pow_add])
  have hS : (S1 : Subgroup A).prod (S2 : Subgroup B) = (S : Subgroup (A × B)) :=
    S.is_maximal' hp (fun x hx => ⟨mem_map_of_mem f hx,mem_map_of_mem g hx⟩)
  let := hs
  have h1 := hA S1 (H.map f) (Group.isSolvable_of_surjective (f.subgroupMap_surjective H))
    (map_mono hSH)
  have h2 := hB S2 (H.map g) (Group.isSolvable_of_surjective (g.subgroupMap_surjective H))
    (map_mono hSH)
  apply le_normalizer_iff.mpr
  intro h hh s hs
  rw [← hS] at hs ⊢
  exact ⟨le_normalizer_iff.mp h1 h.1 (mem_map_of_mem f hh) s.1 hs.1,
    le_normalizer_iff.mp h2 h.2 (mem_map_of_mem g hh) s.2 hs.2⟩
end Theory.GroupTheory.SolvableSylowControl
