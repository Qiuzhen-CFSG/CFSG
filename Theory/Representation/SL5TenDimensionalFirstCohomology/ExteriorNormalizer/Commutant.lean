module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Commuting algebra of the binary exterior square and cube

An elementary transvection adds at most one exterior coordinate to any output
coordinate. Its commuting equations force all off-diagonal entries of an
endomorphism to vanish, and connect all diagonal entries. Thus the full commuting
algebra consists of scalars. Over F₂ its group of units is trivial.

The sparse tables below are checked against the actual determinant minors.
The remaining finite checks concern only basis indices, never arbitrary maps.
Source application: Aschbacher--Smith, G.9.3(13), printed pp.354, 356--357.
-/

namespace Representation.SL5TenDimensional.ExteriorNormalizer
open scoped BigOperators

set_option maxRecDepth 10000

/-- Elementary transvections, with the identity on the diagonal. -/
private def elementary (i j : Fin 5) : Group :=
  if h : i ≠ j then Matrix.SpecialLinearGroup.transvection h 1 else 1

private theorem elementary_entry (i j b c : Fin 5) : (elementary i j).val b c =
    (if b = c then 1 else 0) + (if i ≠ j ∧ b = i ∧ c = j then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    simp [elementary, Matrix.one_apply]
  · simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Extra source coordinate of each elementary action. -/
private def source : Fin 2 → Fin 5 → Fin 5 → Fin 10 → Option (Fin 10) := ![
  ![
    ![![none, none, none, none, none, none, none, none, none, none],
      ![none, some 4, some 5, some 6, none, none, none, none, none, none],
      ![some 4, none, some 7, some 8, none, none, none, none, none, none],
      ![some 5, some 7, none, some 9, none, none, none, none, none, none],
      ![some 6, some 8, some 9, none, none, none, none, none, none, none]],
    ![![none, none, none, none, some 1, some 2, some 3, none, none, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![some 1, none, none, none, none, some 7, some 8, none, none, none],
      ![some 2, none, none, none, some 7, none, some 9, none, none, none],
      ![some 3, none, none, none, some 8, some 9, none, none, none, none]],
    ![![none, none, none, none, some 0, none, none, some 2, some 3, none],
      ![none, some 0, none, none, none, none, none, some 5, some 6, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, some 2, none, none, some 5, none, none, none, some 9, none],
      ![none, some 3, none, none, some 6, none, none, some 9, none, none]],
    ![![none, none, none, none, none, some 0, none, some 1, none, some 3],
      ![none, none, some 0, none, none, none, none, some 4, none, some 6],
      ![none, none, some 1, none, none, some 4, none, none, none, some 8],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, none, some 3, none, none, some 6, none, some 8, none, none]],
    ![![none, none, none, none, none, none, some 0, none, some 1, some 2],
      ![none, none, none, some 0, none, none, none, none, some 4, some 5],
      ![none, none, none, some 1, none, none, some 4, none, none, some 7],
      ![none, none, none, some 2, none, none, some 5, none, some 7, none],
      ![none, none, none, none, none, none, none, none, none, none]]
  ],
  ![
    ![![none, none, none, none, none, none, none, none, none, none],
      ![none, none, none, some 6, some 7, some 8, none, none, none, none],
      ![none, some 6, some 7, none, none, some 9, none, none, none, none],
      ![some 6, none, some 8, none, some 9, none, none, none, none, none],
      ![some 7, some 8, none, some 9, none, none, none, none, none, none]],
    ![![none, none, none, none, none, none, some 3, some 4, some 5, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, some 3, some 4, none, none, none, none, none, some 9, none],
      ![some 3, none, some 5, none, none, none, none, some 9, none, none],
      ![some 4, some 5, none, none, none, none, some 9, none, none, none]],
    ![![none, none, none, none, none, none, some 1, some 2, none, some 5],
      ![none, none, none, some 1, some 2, none, none, none, none, some 8],
      ![none, none, none, none, none, none, none, none, none, none],
      ![some 1, none, none, none, some 5, none, none, some 8, none, none],
      ![some 2, none, none, some 5, none, none, some 8, none, none, none]],
    ![![none, none, none, none, none, none, some 0, none, some 2, some 4],
      ![none, none, none, some 0, none, some 2, none, none, none, some 7],
      ![none, some 0, none, none, none, some 4, none, none, some 7, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, some 2, none, some 4, none, none, some 7, none, none, none]],
    ![![none, none, none, none, none, none, none, some 0, some 1, some 3],
      ![none, none, none, none, some 0, some 1, none, none, none, some 6],
      ![none, none, some 0, none, none, some 3, none, none, some 6, none],
      ![none, none, some 1, none, some 3, none, none, some 6, none, none],
      ![none, none, none, none, none, none, none, none, none, none]]
  ]
 ]

private theorem matrix_entry (a : Fin 2) (i j : Fin 5) (s t : Fin 10) :
    actionMatrix a (elementary i j) s t = (if s = t then 1 else 0) +
      (source a i j s).elim 0 (fun u => if u = t then 1 else 0) := by
  fin_cases a
  · change (Matrix.of fun b c : Fin 2 =>
      (elementary i j).val (frame 0 s c) (frame 0 t b)).det = _
    simp only [Matrix.det_fin_two, Matrix.of_apply, elementary_entry]
    revert i j s t
    decide +kernel
  · change (Matrix.of fun b c : Fin 3 =>
      (elementary i j).val (frame 1 s c) (frame 1 t b)).det = _
    simp only [Matrix.det_fin_three, Matrix.of_apply, elementary_entry]
    revert i j s t
    decide +kernel

private theorem matrix_transpose (a : Fin 2) (i j : Fin 5) :
    (actionMatrix a (elementary i j)).transpose = actionMatrix a (elementary j i) := by
  ext s t
  simp only [Matrix.transpose_apply, matrix_entry]
  revert a i j s t
  decide +kernel

private theorem mul_entry (a : Fin 2) (i j : Fin 5)
    (M : Matrix (Fin 10) (Fin 10) (ZMod 2)) (s t : Fin 10) :
    (actionMatrix a (elementary i j) * M) s t =
      M s t + (source a i j s).elim 0 (fun u => M u t) := by
  simp only [Matrix.mul_apply, matrix_entry, add_mul, Finset.sum_add_distrib]
  cases source a i j s <;> simp

private theorem commuting_entries (a : Fin 2)
    (M : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ i j, M * actionMatrix a (elementary i j) =
      actionMatrix a (elementary i j) * M) (i j : Fin 5) (s t : Fin 10) :
    (source a j i t).elim 0 (fun u => M s u) =
      (source a i j s).elim 0 (fun u => M u t) := by
  have he := congrFun (congrFun (h i j) s) t
  have hl : (M * actionMatrix a (elementary i j)) s t =
      M s t + (source a j i t).elim 0 (fun u => M s u) := by
    have ht := mul_entry a j i M.transpose t s
    rw [← matrix_transpose a i j, ← Matrix.transpose_mul] at ht
    exact ht
  rw [hl, mul_entry] at he
  exact add_left_cancel he

private theorem off_diagonal_witness :
    ∀ (a : Fin 2) (s t : Fin 10), s ≠ t → ∃ (i j : Fin 5) (q : Fin 10),
      source a j i q = some t ∧ source a i j s = none := by
  decide +kernel

private def Adjacent (a : Fin 2) (s t : Fin 10) : Prop :=
  ∃ i j : Fin 5, source a j i s = some t ∧ source a i j t = some s

private instance (a : Fin 2) (s t : Fin 10) : Decidable (Adjacent a s t) :=
  inferInstanceAs (Decidable (∃ i j : Fin 5,
    source a j i s = some t ∧ source a i j t = some s))

private theorem connected : ∀ (a : Fin 2) (s : Fin 10),
    s = 0 ∨ Adjacent a 0 s ∨ ∃ t, Adjacent a 0 t ∧ Adjacent a t s := by
  decide +kernel

private theorem matrix_scalar (a : Fin 2) (M : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ i j, M * actionMatrix a (elementary i j) =
      actionMatrix a (elementary i j) * M) : M = M 0 0 • 1 := by
  have hoff (s t : Fin 10) (hst : s ≠ t) : M s t = 0 := by
    obtain ⟨i, j, q, hq, hs⟩ := off_diagonal_witness a s t hst
    simpa only [hq, hs, Option.elim_some, Option.elim_none] using
      commuting_entries a M h i j s q
  have hadj (s t : Fin 10) (hst : Adjacent a s t) : M s s = M t t := by
    obtain ⟨i, j, ht, hs⟩ := hst
    simpa only [ht, hs, Option.elim_some] using
      (commuting_entries a M h i j t s).symm
  have hdiag (s : Fin 10) : M s s = M 0 0 := by
    rcases connected a s with rfl | hs | ⟨t, ht, hs⟩
    · rfl
    · exact (hadj 0 s hs).symm
    · exact ((hadj 0 t ht).trans (hadj t s hs)).symm
  ext s t
  by_cases hst : s = t
  · subst t
    simp [hdiag]
  · simp [hst, hoff s t hst]

/-- Every endomorphism commuting with the exterior action is scalar. -/
public theorem commuting_endomorphism_scalar (a : Fin 2)
    (f : ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a))
    (h : ∀ g : Group, f * exteriorAction (degree a) g = exteriorAction (degree a) g * f) :
    ∃ c : ZMod 2, f = c • LinearMap.id := by
  let M := LinearMap.toMatrix (basis a) (basis a) f
  have hm : M = M 0 0 • 1 := matrix_scalar a M (fun i j => by
    have he := congrArg (LinearMap.toMatrix (basis a) (basis a)) (h (elementary i j))
    simpa only [LinearMap.toMatrix_mul, toMatrix_action] using he)
  refine ⟨M 0 0, ?_⟩
  apply (LinearMap.toMatrix (basis a) (basis a)).injective
  simpa using hm

/-- A unit centralizing either exterior image is the identity. -/
public theorem centralizing_unit_eq_one (a : Fin 2)
    (x : (ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a))ˣ)
    (h : ∀ g : Group, x * (exteriorAction (degree a)).asGroupHom g * x⁻¹ =
      (exteriorAction (degree a)).asGroupHom g) : x = 1 := by
  have hc (g : Group) : (x : ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a)) *
      exteriorAction (degree a) g = exteriorAction (degree a) g * x :=
    congrArg Units.val (mul_inv_eq_iff_eq_mul.mp (h g))
  obtain ⟨c, hc⟩ := commuting_endomorphism_scalar a x.val hc
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · have hz : x.val = 0 := by simpa using hc
    have hid : (1 : ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a)) = 0 := by
      calc
        1 = x.val * ↑x⁻¹ := x.val_inv.symm
        _ = 0 := by rw [hz, zero_mul]
    have hb := LinearMap.congr_fun hid (basis a 0)
    exact False.elim ((basis a).ne_zero 0 (by simpa using hb))
  · apply Units.ext
    simpa only [one_smul, Units.val_one, Module.End.one_eq_id] using hc

/-- The centralizer of each exterior image in the full linear group is trivial. -/
public theorem centralizer_eq_bot (a : Fin 2) :
    Subgroup.centralizer ((exteriorAction (degree a)).asGroupHom.range :
      Set (ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a))ˣ) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  apply centralizing_unit_eq_one a x
  intro g
  apply mul_inv_eq_iff_eq_mul.mpr
  exact (Subgroup.mem_centralizer_iff.mp hx _ ⟨g, rfl⟩).symm

end Representation.SL5TenDimensional.ExteriorNormalizer
