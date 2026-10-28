module

public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Word certificates for images of finitely generated subgroups

Words expressing the image of each source generator in the target generators,
and each target generator in the source images, prove equality of the generated
subgroups. Only the word equations need finite computation. This includes
conjugacy certificates by taking the homomorphism to be an inner automorphism.

Source: the elementary two-containment argument, using the word evaluation API
of `WordSubgroup` and `SubgroupEnumeration`.
-/

namespace Theory.GroupTheory.SubgroupEnumeration

/-- Word witnesses for both containments of an image equality. -/
public structure ClosureWords (n m : Nat) where
  forward : Fin n → List (Fin m)
  backward : Fin m → List (Fin n)

/-- The finite equations certified by a pair of word tables. -/
@[expose] public def ClosureWords.Valid {G : Type*} [Group G] {n m : Nat}
    (data : ClosureWords n m) (a : Fin n → G) (b : Fin m → G) (f : G →* G) : Prop :=
  (∀ k, evalWord b (data.forward k) = f (a k)) ∧
    ∀ k, evalWord (fun j => f (a j)) (data.backward k) = b k

public instance {G : Type*} [Group G] [DecidableEq G] {n m : Nat}
    (data : ClosureWords n m) (a : Fin n → G) (b : Fin m → G) (f : G →* G) :
    Decidable (data.Valid a b f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

/-- Checking the words in both directions proves the exact image equality. -/
public theorem ClosureWords.sound {G : Type*} [Group G] {n m : Nat}
    (data : ClosureWords n m) (a : Fin n → G) (b : Fin m → G) (f : G →* G)
    (valid : data.Valid a b f) :
    (Subgroup.closure (Set.range a)).map f = Subgroup.closure (Set.range b) := by
  obtain ⟨hf, hb⟩ := valid
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change f (a k) ∈ Subgroup.closure (Set.range b)
    rw [← hf k]
    exact evalWord_mem _ _ (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    rw [← hb k]
    exact evalWord_mem _ _ (fun j => Subgroup.mem_map_of_mem f
      (Subgroup.subset_closure (Set.mem_range_self j))) _

end Theory.GroupTheory.SubgroupEnumeration
