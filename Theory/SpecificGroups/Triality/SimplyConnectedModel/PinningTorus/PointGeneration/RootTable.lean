module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPoints

/-!
# The finite D4 reflection calculation

The twenty-four signed coordinate roots are enumerated together with their
integer vectors. A finite integer certificate verifies the reflection formula;
casting that equality to the real root space identifies it with the actual
`typeDRootPairing` reflection permutation. No reflection table is assumed.

Source: the coordinate D4 root system underlying GLS3, Theorem 1.12.1(h).
-/

@[expose] public section
namespace Triality.SimplyConnected.Pinning.PointGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
set_option linter.unusedSimpArgs false
noncomputable section
def rootAt : Fin 24 → RootIndex :=
  ![⟨⟨⟨0, 1⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 1⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨0, 1⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 1⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨0, 2⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 2⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨0, 2⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 2⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨0, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨0, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨0, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨1, 2⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨1, 2⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨1, 2⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨1, 2⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨1, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨1, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨1, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨1, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨2, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨2, 3⟩, by decide⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩,
    ⟨⟨⟨2, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩,
    ⟨⟨⟨2, 3⟩, by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩]

def rootVectorInt : Fin 24 → Fin 4 → ℤ :=
  ![![-1, -1, 0, 0],
    ![-1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![1, 1, 0, 0],
    ![-1, 0, -1, 0],
    ![-1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, 0, 1, 0],
    ![-1, 0, 0, -1],
    ![-1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![1, 0, 0, 1],
    ![0, -1, -1, 0],
    ![0, -1, 1, 0],
    ![0, 1, -1, 0],
    ![0, 1, 1, 0],
    ![0, -1, 0, -1],
    ![0, -1, 0, 1],
    ![0, 1, 0, -1],
    ![0, 1, 0, 1],
    ![0, 0, -1, -1],
    ![0, 0, -1, 1],
    ![0, 0, 1, -1],
    ![0, 0, 1, 1]]

def reflectionIndex : Fin 4 → Fin 24 → Fin 24 :=
  ![![0, 2, 1, 3, 12, 13, 14, 15, 16, 17, 18, 19, 4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23],
    ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19],
    ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 16, 17, 18, 19, 12, 13, 14, 15, 20, 22, 21, 23],
    ![0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6, 17, 16, 19, 18, 13, 12, 15, 14, 23, 21, 22, 20]]

def simpleIndex : Fin 4 → Fin 24 := ![2, 14, 22, 23]

theorem simpleRoot_eq_rootAt (i : Fin 4) : simpleRoot i = rootAt (simpleIndex i) := by
  fin_cases i <;> rfl

theorem rootAt_vector (r : Fin 24) (p : Fin 4) :
    typeDRootVector 4 (rootAt r) p = (rootVectorInt r p : ℝ) := by
  fin_cases r <;> fin_cases p <;>
    norm_num [rootAt, rootVectorInt, typeDRootVector, basisVector, Pi.single_apply] <;>
      simp [Fin.ext_iff]

theorem reflection_certificate : ∀ (i : Fin 4) (r : Fin 24) (p : Fin 4),
    rootVectorInt r p -
      (∑ q : Fin 4, rootVectorInt (simpleIndex i) q * rootVectorInt r q) *
        rootVectorInt (simpleIndex i) p = rootVectorInt (reflectionIndex i r) p := by
  decide

theorem reflection_rootAt (i : Fin 4) (r : Fin 24) :
    (typeDRootPairing 2).reflectionPerm (simpleRoot i) (rootAt r) =
      rootAt (reflectionIndex i r) := by
  rw [simpleRoot_eq_rootAt]
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root]
  apply Subtype.ext
  change typeDRootVector 4 (rootAt r) -
      (typeDRootPairing 2).pairing (rootAt r) (rootAt (simpleIndex i)) •
        typeDRootVector 4 (rootAt (simpleIndex i)) =
          typeDRootVector 4 (rootAt (reflectionIndex i r))
  rw [typeDRootPairing_pairing]
  funext p
  change typeDRootVector 4 (rootAt r) p -
      (∑ q : Fin 4, typeDRootVector 4 (rootAt (simpleIndex i)) q *
        typeDRootVector 4 (rootAt r) q) * typeDRootVector 4 (rootAt (simpleIndex i)) p = _
  simp only [rootAt_vector]
  exact_mod_cast reflection_certificate i r p

theorem rootAt_surjective : Function.Surjective rootAt := by
  rintro ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> subst s <;> subst t
  all_goals fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩
    | exact ⟨11, rfl⟩
    | exact ⟨12, rfl⟩
    | exact ⟨13, rfl⟩
    | exact ⟨14, rfl⟩
    | exact ⟨15, rfl⟩
    | exact ⟨16, rfl⟩
    | exact ⟨17, rfl⟩
    | exact ⟨18, rfl⟩
    | exact ⟨19, rfl⟩
    | exact ⟨20, rfl⟩
    | exact ⟨21, rfl⟩
    | exact ⟨22, rfl⟩
    | exact ⟨23, rfl⟩

end
end Triality.SimplyConnected.Pinning.PointGeneration
