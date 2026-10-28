module

public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Lifting centralizers of perfect subgroups

If the kernel of a homomorphism centralizes a perfect subgroup, centralizing
its image is equivalent to centralizing the subgroup itself. Indeed the first
commutator lies in the kernel, the second vanishes, and the three-subgroup
lemma removes the second commutator. Surjectivity and ambient normality of the
perfect subgroup are unnecessary.

This is the centralizer transport used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, B.1.11, printed pp. 72–73.
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- Centralizers of perfect subgroups lift across kernels centralizing them. -/
theorem comap_centralizer_map_eq_of_perfect (f : G →* D) (L : Subgroup G)
    [Group.IsPerfect L] (hker : f.ker ≤ centralizer (L : Set G)) :
    (centralizer (L.map f : Set D)).comap f = centralizer (L : Set G) := by
  let C := (centralizer (L.map f : Set D)).comap f
  apply le_antisymm
  · apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_trans _ hker
    apply (map_eq_bot_iff _).mp
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact map_comap_le _ _
  · intro x hx
    change f x ∈ centralizer (L.map f : Set D)
    rw [mem_centralizer_iff]
    rintro y ⟨l, hl, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx l hl)

/-- The same equality inside an arbitrary overgroup, with relative centralizers. -/
theorem inf_comap_centralizer_map_eq_of_perfect (f : G →* D) (L H : Subgroup G)
    [Group.IsPerfect L] (hker : f.ker ≤ centralizer (L : Set G)) :
    H ⊓ (centralizer (L.map f : Set D)).comap f = H ⊓ centralizer (L : Set G) := by
  rw [comap_centralizer_map_eq_of_perfect f L hker]

end Subgroup
