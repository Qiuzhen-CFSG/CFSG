module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic

/-!
# The four-group over the last four heptad labels

The chosen four-set consists of labels 3, 4, 5, 6 in the standard heptad.
Its three double transpositions, together with the identity, form a four-group
fixing the other three labels. Pulling this group back along the actual heptad
action defines a subgroup of the actual four-set stabilizer in M23. In
particular its ambient group is the four-set stabilizer, not all of M23.

The identification with the two-core and the calculation of its center are
separate proof obligations. This interface specifies the concrete subgroup
needed for those two independent calculations; it assumes neither of them.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Table 5.3d. The geometric
coordinates and their actions are those of Aschbacher–Smith §5.2.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.FourSetStabilizer
open Subgroup Equiv

/-- The first double transposition on the four chosen labels. -/
def firstDoubleSwap : Perm (Fin 7) := swap 3 4 * swap 5 6

/-- The second double transposition on the four chosen labels. -/
def secondDoubleSwap : Perm (Fin 7) := swap 3 5 * swap 4 6

/-- The four permutations fixing the first three labels and acting as the
identity or a double transposition on the last four. -/
def labelKlein : Subgroup (Perm (Fin 7)) where
  carrier := {p | p = 1 ∨ p = firstDoubleSwap ∨ p = secondDoubleSwap ∨
    p = firstDoubleSwap * secondDoubleSwap}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro _ _ (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro _ (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem mem_labelKlein (p : Perm (Fin 7)) : p ∈ labelKlein ↔
    p = 1 ∨ p = firstDoubleSwap ∨ p = secondDoubleSwap ∨
      p = firstDoubleSwap * secondDoubleSwap := Iff.rfl

private def kleinIndex : Fin 4 → Perm (Fin 7) :=
  ![1, firstDoubleSwap, secondDoubleSwap, firstDoubleSwap * secondDoubleSwap]

private theorem kleinIndex_mem (i : Fin 4) : kleinIndex i ∈ labelKlein := by
  rw [mem_labelKlein]
  fin_cases i <;> decide +kernel

private noncomputable def kleinEquiv : Fin 4 ≃ labelKlein :=
  Equiv.ofBijective (fun i => ⟨kleinIndex i, kleinIndex_mem i⟩) (by
    constructor
    · intro i j hij
      exact (by decide +kernel : Function.Injective kleinIndex) (congrArg Subtype.val hij)
    · rintro ⟨p, hp⟩
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩)

/-- The displayed label group has exactly four elements. -/
theorem labelKlein_card : Nat.card labelKlein = 4 :=
  (Nat.card_congr kleinEquiv.symm).trans (Nat.card_fin 4)

/-- Every element of the label group has square one. -/
theorem labelKlein_square (p : labelKlein) : p ^ 2 = 1 := by
  apply Subtype.ext
  rcases p.property with h | h | h | h <;>
    change p.val ^ 2 = 1 <;> rw [h] <;> decide +kernel

/-- The labelled heptad action restricted to the actual four-set stabilizer. -/
noncomputable def labelAction : fourStabilizer →* Perm (Fin 7) :=
  heptadAction.comp (inclusion fourStabilizer_le)

@[simp] theorem labelAction_apply (g : fourStabilizer) (i : Fin 7) :
    label (labelAction g i) = (g : M23) • label i :=
  heptadAction_apply (inclusion fourStabilizer_le g) i

/-- The inverse image of the displayed four-group, computed inside the
four-set stabilizer. -/
noncomputable def coreCandidate : Subgroup fourStabilizer :=
  labelKlein.comap labelAction

theorem mem_coreCandidate (g : fourStabilizer) : g ∈ coreCandidate ↔
    labelAction g ∈ labelKlein := Iff.rfl

/-- Every pointwise heptad fixer lies in this inverse image. -/
theorem heptadKernel_le_coreCandidate :
    heptadKernelAmbient.subgroupOf fourStabilizer ≤ coreCandidate := by
  intro g hg
  change labelAction g ∈ labelKlein
  have hk : inclusion fourStabilizer_le g ∈ heptadKernel := by
    apply (mem_heptadKernel _).mpr
    exact (mem_heptadKernelAmbient g.val).mp hg
  change heptadAction (inclusion fourStabilizer_le g) ∈ labelKlein
  rw [show heptadAction (inclusion fourStabilizer_le g) = 1 from hk]
  exact labelKlein.one_mem

end Sporadic.Mathieu.M23Geometry.FourSetStabilizer
