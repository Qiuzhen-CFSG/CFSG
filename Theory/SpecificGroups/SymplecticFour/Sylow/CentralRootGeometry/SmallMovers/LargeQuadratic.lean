module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Degree
public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction

/-!
# Large quadratic actors inside the small-mover join

The standard Sylow equations make every small mover quadratic. The maximum
family is either a singleton or the q+1 planes in the point radical. Thus
a join of order at least q² contains a quadratic maximum of that size.
The orthogonal bound 2q < q² excludes any invariant quadratic refinement.

Source: MS93 (5.3)--(5.4), printed p.915. The original-group consumer is
NonbinarySymplectic.CriticalReduction.SmallMoverRefinement.
-/

public noncomputable section
open Subgroup Matrix Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every small mover in the symplectic Sylow acts quadratically. -/
theorem small_quadratic (A : Subgroup (unipotent (F := F))) (hA : Small A) :
    ∀ x ∈ A.map unipotent.subtype, ∀ y ∈ A.map unipotent.subtype,
      ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
        x • (y • v-v)=y • v-v := by
  rcases small_classification_nonstandard A hA with hw | ⟨l,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    obtain ⟨⟨a,b,c,d⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨e,f,g,k⟩,rfl⟩ := element_surjective y
    have ha : a=0 := (element_mem_wing true _ _ _ _).mp (hw hx)
    have he : e=0 := (element_mem_wing true _ _ _ _).mp (hw hy)
    subst a; subst e
    change (element 0 b c d).val.val *ᵥ
        ((element 0 f g k).val.val *ᵥ v-v) =
      (element 0 f g k).val.val *ᵥ v-v
    rw [element_matrix,element_matrix]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    obtain ⟨⟨a,b,c,d⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨e,f,g,k⟩,rfl⟩ := element_surjective y
    have hx' : d=0 ∧ c=l*a := (element_mem_finitePlane l _ _ _ _).mp hx
    have hy' : k=0 ∧ g=l*e := (element_mem_finitePlane l _ _ _ _).mp hy
    obtain ⟨rfl,rfl⟩ := hx'
    obtain ⟨rfl,rfl⟩ := hy'
    change (element a b (l*a) 0).val.val *ᵥ
        ((element e f (l*e) 0).val.val *ᵥ v-v) =
      (element e f (l*e) 0).val.val *ᵥ v-v
    rw [element_matrix,element_matrix]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]
    ring_nf
    simp [CharTwo.two_eq_zero]

/-- A join of order at least q² contains a maximum quadratic actor of order
at least q², including when the join is the nonquadratic point radical. -/
theorem exists_large_quadratic_maximal (T : Subgroup (unipotent (F := F)))
    (hlarge : Nat.card F^2 ≤ Nat.card (join T)) :
    ∃ A ∈ Maximal T, Nat.card F^2 ≤ Nat.card A ∧
      ∀ x ∈ A.map unipotent.subtype, ∀ y ∈ A.map unipotent.subtype,
        ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
          x • (y • v-v)=y • v-v := by
  rcases maximal_singleton_or_point_wing T with ⟨A,hA,hjoin⟩ | ⟨rfl,_,_,_⟩
  · have hm : A ∈ Maximal T := hA ▸ Set.mem_singleton A
    exact ⟨A,hm,hjoin ▸ hlarge,small_quadratic A hm.2.1⟩
  · have hm := (maximal_point_wing_iff (plane (F := F) none)).mpr ⟨none,rfl⟩
    exact ⟨plane none,hm,(card_plane none).ge,small_quadratic _ hm.2.1⟩

/-- The large small-mover join preserves no quadratic refinement. -/
theorem join_no_refinement (hF : 2 < Nat.card F)
    (T : Subgroup (unipotent (F := F))) (hlarge : Nat.card F^2 ≤ Nat.card (join T)) :
    ¬ ∃ c : Theory.SpecificGroups.SymplecticFour.Vector F,
      ∀ a : (join T).map unipotent.subtype, ∀ v,
        refinement c (a.val • v)=refinement c v := by
  obtain ⟨A,hA,hcard,hq⟩ := exists_large_quadratic_maximal T hlarge
  have hc : Nat.card F^2 ≤ Nat.card (A.map unipotent.subtype) := by
    rwa [card_map_of_injective Subtype.val_injective]
  rintro ⟨c,hc'⟩
  exact no_refinement_of_large_quadratic hF _ hc hq
    ⟨c,fun a v => hc' ⟨a.val,map_mono (le_sSup hA) a.property⟩ v⟩
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
