module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Colors11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Normalizer
import Mathlib.Tactic.FinCases

/-!
# Every candidate two-group actor preserves the marked axes

Closure induction extends the four generator color identities to the entire
literal two-group. Conjugation carries a marked generator's distinguished
color transition to the same transition. The checked coordinate tests then
force its image to be that generator or its inverse. This argument bounds all
actors in the two-group, without any selected local-overgroup restriction.
The elementary plane lemmas connect these formulas to the diagonal subgroup.
Source: GLS3 Table 5.3p and the ATLAS certificates in Colors00/01/10/11.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
open Subgroup

def color : Bool → Fin 2 → Fin 2058 → ℕ
  | false, 0 => Colors00.color
  | false, 1 => Colors01.color
  | true, 0 => Colors10.color
  | true, 1 => Colors11.color

def witness : Bool → Fin 2 → Fin 2 → Fin 2058
  | false, 0 => Colors00.witness
  | false, 1 => Colors01.witness
  | true, 0 => Colors10.witness
  | true, 1 => Colors11.witness

private theorem generator_preserves (i : Bool) (j : Fin 2) (k : Fin 4) :
    ∀ x, color i j (representation (twoGenerator i j k) x) = color i j x := by
  cases i <;> fin_cases j
  · exact Colors00.generator_preserves k
  · exact Colors01.generator_preserves k
  · exact Colors10.generator_preserves k
  · exact Colors11.generator_preserves k

theorem color_preserved (i : Bool) (j : Fin 2) (g : He) (hg : g ∈ candidateTwo i j) :
    ∀ x, color i j (representation g x) = color i j x := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact generator_preserves i j k
  | one => intro x; rfl
  | mul a b ha hb ia ib =>
    intro x
    change color i j (representation a (representation b x)) = color i j x
    rw [ia, ib]
  | inv g hg ih =>
    intro x
    have h := ih ((representation g).symm x)
    rw [map_inv, Equiv.Perm.inv_def]
    simpa only [Equiv.apply_symm_apply] using h.symm

private theorem coordinate_test (i : Bool) (j k : Fin 2) (x : Fin 2058) (v : Plane)
    (h0 : color i j x = color i j (witness i j k))
    (h1 : color i j (representation (markedEmbedding i j v) x) =
      color i j (representation (basisGenerator i j k) (witness i j k))) :
    v = coordinateVector k ∨ v = (coordinateVector k)⁻¹ := by
  cases i <;> fin_cases j
  · exact Colors00.coordinate_test k x v h0 h1
  · exact Colors01.coordinate_test k x v h0 h1
  · exact Colors10.coordinate_test k x v h0 h1
  · exact Colors11.coordinate_test k x v h0 h1

theorem coordinates_of_conjugation (i : Bool) (j k : Fin 2) (g : He)
    (hg : g ∈ candidateTwo i j) (v : Plane)
    (hv : markedEmbedding i j v = g * basisGenerator i j k * g⁻¹) :
    v = coordinateVector k ∨ v = (coordinateVector k)⁻¹ := by
  apply coordinate_test i j k (representation g (witness i j k)) v
  · exact color_preserved i j g hg _
  · rw [hv]
    change color i j (representation g (representation (basisGenerator i j k)
      ((representation g).symm (representation g (witness i j k))))) = _
    rw [Equiv.symm_apply_apply]
    exact color_preserved i j g hg _

/-- The sign change on one marked coordinate. -/
def signChange (k : Fin 2) : MulAut Plane :=
  diagonalHom (fun l => if l = k then -1 else 1)

theorem signChange_vector (k l : Fin 2) :
    signChange k (coordinateVector l) =
      if l = k then (coordinateVector l)⁻¹ else coordinateVector l := by
  have h : ∀ k l : Fin 2, signChange k (coordinateVector l) =
      if l = k then (coordinateVector l)⁻¹ else coordinateVector l := by decide +kernel
  exact h k l

theorem mem_diagonal_of_vectors (a : MulAut Plane)
    (h : ∀ k, a (coordinateVector k) = coordinateVector k ∨
      a (coordinateVector k) = (coordinateVector k)⁻¹) : a ∈ diagonal := by
  classical
  let u : Fin 2 → (ZMod 3)ˣ := fun k => if a (coordinateVector k) = coordinateVector k then 1 else -1
  have he : ∀ (u : Fin 2 → (ZMod 3)ˣ) (k : Fin 2),
      diagonalHom u (coordinateVector k) =
        if u k = 1 then coordinateVector k else (coordinateVector k)⁻¹ := by
    decide +kernel
  have hv (k : Fin 2) : diagonalHom u (coordinateVector k) = a (coordinateVector k) := by
    rw [he]
    by_cases hak : a (coordinateVector k) = coordinateVector k
    · simp [u, hak]
    · have hn : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide +kernel
      simpa [u, hak, hn] using ((h k).resolve_left hak).symm
  exact ⟨u, planeAut_ext (hv 0) (hv 1)⟩

theorem diagonal_le_of_signChanges (H : Subgroup (MulAut Plane))
    (h : ∀ k, signChange k ∈ H) : diagonal ≤ H := by
  rintro a ⟨u, rfl⟩
  have hu : ∀ u : Fin 2 → (ZMod 3)ˣ,
      diagonalHom u = signChange 0 ^ (if u 0 = 1 then 0 else 1 : ℕ) *
        signChange 1 ^ (if u 1 = 1 then 0 else 1 : ℕ) := by
    have hh : ∀ (u : Fin 2 → (ZMod 3)ˣ) (x : Plane),
        diagonalHom u x =
          (signChange 0 ^ (if u 0 = 1 then 0 else 1 : ℕ) *
            signChange 1 ^ (if u 1 = 1 then 0 else 1 : ℕ)) x := by decide +kernel
    intro u
    exact MulEquiv.ext (hh u)
  rw [hu]
  exact H.mul_mem (H.pow_mem (h 0) _) (H.pow_mem (h 1) _)

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
