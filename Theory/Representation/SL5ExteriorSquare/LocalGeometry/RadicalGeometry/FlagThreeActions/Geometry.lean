module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FlagThreeActions.UpperThree
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Coordinates for the two flag three-spaces

The charts embed F₂³ as the marked spans (12,13,23) and (12,13,14).
Preservation of the natural complete flag forces upper triangular matrices;
the diagonal entries are one over F₂. The exterior minors give the explicit
upper-unitriangular parameters on both charts.

Source: Aschbacher--Smith 12.5.7/10, printed pp.820--821.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private lemma flag_lower {g : Group} (hg : g ∈ flagGroup) {i j : Fin 5} (h : j < i) :
    g.val i j = 0 := by
  have hk : j.val + 1 < 5 := by omega
  have hp : g ∈ parabolic (j.val + 1) := (Subgroup.mem_iInf.mp hg) ⟨j.val + 1, hk⟩
  have hv : Pi.single j (1 : ZMod 2) ∈ naturalFlag (j.val + 1) := by
    intro l hl
    have hn : l ≠ j := by intro he; subst l; omega
    simp [hn]
  have hh := (hp _).mpr hv i (by omega)
  change g.val.mulVec (Pi.single j 1) i = 0 at hh
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh

private lemma flag_diag {g : Group} (hg : g ∈ flagGroup) (i : Fin 5) : g.val i i = 1 := by
  have ht : g.val.IsUpperTriangular := fun _ _ h => flag_lower hg h
  have hd := Matrix.det_of_isUpperTriangular ht
  have hn : ∏ j : Fin 5, g.val j j ≠ 0 := by rw [← hd, g.property]; decide
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ _)
  exact ((by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _).resolve_left hi

namespace FlagThreeActions

/-- The third wedge index: true selects V₃, false selects V₃'. -/
def third (s : Bool) : Fin 10 := if s then 4 else 2
noncomputable def space (s : Bool) : Submodule (ZMod 2) V := coordinateSpan {0,1,third s}

noncomputable def embedding (s : Bool) : Three →ₗ[ZMod 2] V where
  toFun v := v 0 • basis 0 + v 1 • basis 1 + v 2 • basis (third s)
  map_add' v w := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c v := by simp [smul_add, smul_smul]

private lemma coordinates_basis' (i : Fin 10) : coordinates (basis i) = Pi.single i 1 :=
by
  ext j
  change basis.equivFun (basis i) j = (Pi.single i 1 : Coordinates) j
  simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

lemma coordinates_embedding (s : Bool) (v : Three) :
    coordinates (embedding s v) =
      if s then ![v 0,v 1,0,0,v 2,0,0,0,0,0] else ![v 0,v 1,v 2,0,0,0,0,0,0,0] := by
  cases s <;> ext i <;> fin_cases i <;>
    simp [embedding, third, coordinates_basis', -coordinates_apply, -basis_apply]

lemma embedding_mem (s : Bool) (v : Three) : embedding s v ∈ space s := by
  rw [space, mem_coordinateSpan]
  intro i hi
  rw [coordinates_embedding]
  cases s <;> fin_cases i <;> simp_all [third]

lemma embedding_injective (s : Bool) : Function.Injective (embedding s) := by
  intro v w he
  have hh := congrArg coordinates he
  rw [coordinates_embedding, coordinates_embedding] at hh
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  have h2 := congrFun hh (third s)
  ext i
  cases s <;> fin_cases i <;> simpa [third] using (by assumption)

lemma embedding_surjective (s : Bool) (w : space s) : ∃ v, embedding s v = w.val := by
  refine ⟨![coordinates w 0,coordinates w 1,coordinates w (third s)], ?_⟩
  apply coordinates.injective
  rw [coordinates_embedding]
  have hh := (mem_coordinateSpan _ _).mp w.property
  cases s <;> ext i <;> fin_cases i <;> simp [third, -coordinates_apply]
  all_goals symm; apply hh; decide

/-- Actual coordinates on the specified exterior subspace. -/
noncomputable def chart (s : Bool) : Three ≃ₗ[ZMod 2] space s :=
  LinearEquiv.ofBijective ((embedding s).codRestrict (space s) (embedding_mem s))
    ⟨fun _ _ h => embedding_injective s (congrArg Subtype.val h), by
      intro w
      obtain ⟨v, hv⟩ := embedding_surjective s w
      exact ⟨v, Subtype.ext hv⟩⟩

/-- The three off-diagonal entries of the genuine restricted exterior action. -/
def parameters (s : Bool) (g : Group) : Three :=
  if s then ![g.val 1 2, g.val 0 1 * g.val 1 2 + g.val 0 2, g.val 0 1]
  else ![g.val 1 2, g.val 1 3, g.val 2 3]

/-- Equivariance of the chart with the explicit upper-unitriangular action. -/
lemma action_embedding (s : Bool) {g : Group} (hg : g ∈ flagGroup) (v : Three) :
    exteriorAction 2 g (embedding s v) = embedding s (upper (parameters s g) v) := by
  apply coordinates.injective
  rw [coordinates_action, coordinates_embedding, coordinates_embedding]
  cases s <;> ext i <;> fin_cases i <;>
    simp [actionMatrix, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      parameters, upper, flag_lower hg, flag_diag hg, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  <;> ring
end FlagThreeActions
end Representation.SL5ExteriorSquare
