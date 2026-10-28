module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.Data

/-!
# The full coordinate enumeration of the Geck F₄ lattice

The lexicographically ordered integer root table enumerates every root of the
actual real F₄ root pairing once. Together with the four simple Cartan vectors,
this supplies the coordinate equivalence for a full matrix comparison.

Source: the pair, signed-unit and half-sign root families in the standard F₄
model, as used by the integral Geck representation.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

/-- Interpret the doubled integer coordinates in the actual real root space. -/
def rootVector (i : Fin 48) : Fin 4 → ℝ := fun k => (rootCoords i k : ℝ) / 2

private def pairCoords (i j : Fin 4) (s t : Bool) : Fin 4 → ℤ := fun k =>
  (if k = i then (if s then 2 else -2) else 0) +
  (if k = j then (if t then 2 else -2) else 0)

private def unitCoords (i : Fin 4) (s : Bool) : Fin 4 → ℤ := fun k =>
  if k = i then (if s then 2 else -2) else 0

private def halfCoords (s : Fin 4 → Bool) : Fin 4 → ℤ := fun k => if s k then 1 else -1

private theorem pair_cast (i j : Fin 4) (s t : Bool) :
    (fun k => (pairCoords i j s t k : ℝ) / 2) =
      (if s then (1 : ℝ) else -1) • basisVector i +
      (if t then (1 : ℝ) else -1) • basisVector j := by
  ext k
  simp only [pairCoords, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVector, Pi.single_apply]
  split_ifs <;> norm_num

private theorem unit_cast (i : Fin 4) (s : Bool) :
    (fun k => (unitCoords i s k : ℝ) / 2) =
      if s then basisVector i else -basisVector i := by
  ext k
  cases s <;>
    simp only [unitCoords, Bool.false_eq_true, ↓reduceIte, basisVector,
      Pi.single_apply, Pi.neg_apply]
  all_goals split_ifs <;> norm_num

private theorem half_cast (s : Fin 4 → Bool) :
    (fun k => (halfCoords s k : ℝ) / 2) = halfSignVector s := by
  ext k
  simp only [halfCoords, halfSignVector]
  split_ifs <;> norm_num

private theorem rootVector_mem (i : Fin 48) : rootVector i ∈ typeF4Roots := by
  have hc : ∀ n : Fin 48,
      (∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ rootCoords n = pairCoords i j s t) ∨
      (∃ (i : Fin 4) (s : Bool), rootCoords n = unitCoords i s) ∨
      (∃ s : Fin 4 → Bool, rootCoords n = halfCoords s) := by decide +kernel
  rcases hc i with ⟨j, k, s, t, hjk, h⟩ | ⟨j, s, h⟩ | ⟨s, h⟩
  · left; left
    refine ⟨j, k, hjk, if s then 1 else -1, if t then 1 else -1, ?_, ?_, ?_⟩
    · cases s <;> simp
    · cases t <;> simp
    · unfold rootVector
      rw [h]
      exact pair_cast j k s t
  · left; right
    refine ⟨j, ?_⟩
    have he : rootVector i = if s then basisVector j else -basisVector j := by
      unfold rootVector
      rw [h]
      exact unit_cast j s
    cases s
    · exact Or.inr he
    · exact Or.inl he
  · right
    refine ⟨s, ?_⟩
    exact (show rootVector i = halfSignVector s by
      unfold rootVector
      rw [h]
      exact half_cast s).symm

private theorem rootVector_injective : Function.Injective rootVector := by
  have hc : Function.Injective rootCoords := by decide +kernel
  intro i j h
  apply hc
  ext k
  have hk := congrFun h k
  change (rootCoords i k : ℝ) / 2 = (rootCoords j k : ℝ) / 2 at hk
  have hk' : (rootCoords i k : ℝ) = (rootCoords j k : ℝ) := by linarith
  exact_mod_cast hk'

private theorem pair_covered (i j : Fin 4) (s t : Bool) (hij : i ≠ j) :
    ∃ n, rootVector n =
      (if s then (1 : ℝ) else -1) • basisVector i +
      (if t then (1 : ℝ) else -1) • basisVector j := by
  have hc : ∀ (i j : Fin 4) (s t : Bool), i ≠ j →
      ∃ n : Fin 48, rootCoords n = pairCoords i j s t := by decide +kernel
  obtain ⟨n, hn⟩ := hc i j s t hij
  exact ⟨n, by unfold rootVector; rw [hn]; exact pair_cast i j s t⟩

private theorem unit_covered (i : Fin 4) (s : Bool) :
    ∃ n, rootVector n = if s then basisVector i else -basisVector i := by
  have hc : ∀ (i : Fin 4) (s : Bool),
      ∃ n : Fin 48, rootCoords n = unitCoords i s := by decide +kernel
  obtain ⟨n, hn⟩ := hc i s
  exact ⟨n, by unfold rootVector; rw [hn]; exact unit_cast i s⟩

private theorem half_covered (s : Fin 4 → Bool) :
    ∃ n, rootVector n = halfSignVector s := by
  have hc : ∀ s : Fin 4 → Bool, ∃ n : Fin 48,
      rootCoords n = halfCoords s := by decide +kernel
  obtain ⟨n, hn⟩ := hc s
  exact ⟨n, by unfold rootVector; rw [hn]; exact half_cast s⟩

/-- The roots in the order of the full binary matrix tables. -/
def enumeratedRoot (i : Fin 48) : F4Chevalley.Root := ⟨rootVector i, by exact rootVector_mem i⟩

theorem enumeratedRoot_bijective : Function.Bijective enumeratedRoot := by
  constructor
  · intro i j h
    exact rootVector_injective (congrArg Subtype.val h)
  · rintro ⟨r, (h | h) | ⟨s, rfl⟩⟩
    · rcases h with ⟨i, j, hij, s, t, hs, ht, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      all_goals first
        | obtain ⟨n, hn⟩ := pair_covered i j false false hij; exact ⟨n, Subtype.ext hn⟩
        | obtain ⟨n, hn⟩ := pair_covered i j false true hij; exact ⟨n, Subtype.ext hn⟩
        | obtain ⟨n, hn⟩ := pair_covered i j true false hij; exact ⟨n, Subtype.ext hn⟩
        | obtain ⟨n, hn⟩ := pair_covered i j true true hij; exact ⟨n, Subtype.ext hn⟩
    · rcases h with ⟨i, rfl | rfl⟩
      · obtain ⟨n, hn⟩ := unit_covered i true
        exact ⟨n, Subtype.ext hn⟩
      · obtain ⟨n, hn⟩ := unit_covered i false
        exact ⟨n, Subtype.ext hn⟩
    · obtain ⟨n, hn⟩ := half_covered s
      exact ⟨n, Subtype.ext hn⟩

/-- The actual root index is equivalent to the explicit 48-element root table. -/
def rootEquiv : Fin 48 ≃ F4Chevalley.Root :=
  Equiv.ofBijective enumeratedRoot enumeratedRoot_bijective

/-- All 52 coordinates, with Cartan coordinates first and root coordinates last. -/
def basisEquiv : Fin 52 ≃ F4Chevalley.BasisIndex :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr typeF4RootPairing_baseEquiv rootEquiv)

@[simp] theorem basisEquiv_cartan (i : Fin 4) :
    basisEquiv (Fin.castAdd 48 i) = Sum.inl (typeF4RootPairing_baseEquiv i) := by
  change (Equiv.sumCongr typeF4RootPairing_baseEquiv rootEquiv)
    (finSumFinEquiv.symm (Fin.castAdd 48 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem basisEquiv_root (i : Fin 48) :
    basisEquiv (Fin.natAdd 4 i) = Sum.inr (enumeratedRoot i) := by
  change (Equiv.sumCongr typeF4RootPairing_baseEquiv rootEquiv)
    (finSumFinEquiv.symm (Fin.natAdd 4 i)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
