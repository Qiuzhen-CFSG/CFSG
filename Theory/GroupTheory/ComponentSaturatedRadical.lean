module

public import Theory.GroupTheory.ComponentSaturatedSylow

/-!
# Radical intersections under component saturation

Let Q be a p-subgroup normalized by A, with every A-invariant p-subgroup
contained in Q. For any component L, the intersection R=L∩Q is the p-core
of N_L(R). Indeed the stabilizer N_A(L) normalizes R and N_L(R), hence its
p-core. The commuting component-orbit argument puts this p-core inside Q.
The reverse inclusion follows from R being a normal p-subgroup of N_L(R).
Components may be permuted by A; no normality of L is assumed.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, the radical-normalizer
step following projection saturation.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- The literal component intersection is radical in its component normalizer. -/
theorem IsComponent.pCoreIn_normalizer_intersection_of_saturation
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q) :
    (L ⊓ normalizer ((L ⊓ Q : Subgroup G) : Set G)).pCoreIn p = L ⊓ Q := by
  let R := L ⊓ Q
  let N := L ⊓ normalizer (R : Set G)
  have hAR : A ⊓ normalizer (L : Set G) ≤ normalizer (R : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hAQ)).trans inf_normalizer_le_normalizer_inf
  have hAN : A ⊓ normalizer (L : Set G) ≤ normalizer (N : Set G) :=
    (le_inf inf_le_right (hAR.trans (normalizer (R : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hcoreQ : N.pCoreIn p ≤ Q := hL.stabilizer_saturation hsat _
    ((pCoreIn_le p N).trans inf_le_left) (isPGroup_pCoreIn p N)
    (hAN.trans (normalizer_le_normalizer_characteristic_image N (pCore p N)))
  exact le_antisymm (le_inf ((pCoreIn_le p N).trans inf_le_left) hcoreQ)
    (le_pCoreIn_of_normalizes (hQ.to_le inf_le_right)
      (le_inf inf_le_left R.le_normalizer) inf_le_right)

end Theory.GroupTheory
