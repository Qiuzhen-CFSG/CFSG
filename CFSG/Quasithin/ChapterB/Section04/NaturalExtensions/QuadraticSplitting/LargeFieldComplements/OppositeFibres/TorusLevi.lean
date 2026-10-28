module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.Models

/-!
# The scalar centralizer and full-Levi factorization

In the supplied quotient coordinates, the full Levi preserves the coordinate
axis and its complementary defining-field line. A square root in the finite
characteristic-two field supplies a scalar torus element with the same line
action; dividing by it leaves an element of K. Conversely both factors preserve
the two subspaces, giving the literal product K₀ = KH.

The scalar torus centralizes every block-preserving matrix. Commutation with the
two elementary axis transvections forces a centralizing matrix's axis block to
be scalar. Its determinant then forces the line entry to be the inverse square.
Thus the constructed torus is exactly C_{K₀}(K), including over F₄. These matrix
facts require neither opposite marking nor quadraticity or fixed lifts.

Source: Aschbacher–Smith B.4.9(1), printed p.93 (PDF p.104), combined
manuscript of 1 March 2004. The exported inclusion discharges the full-Levi
premise of `opposite_coordinate_fullLevi_complement_of_matrix_facts`.
-/

@[expose] public section

open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V} {d : DoubleNatural F 3 ρ}
  (m : QuotientCoordinates d) (j : Fin 3)
namespace QuotientCoordinates

private theorem marked_apply (g : G) (z : Fin 3 → F.Carrier) :
    m.action.linearEquiv (d.space.quotientRepresentation g (m.action.linearEquiv.symm z)) =
      (m.action.groupEquiv g).val.mulVec z := by
  rw [m.action.intertwines, m.action.linearEquiv.apply_symm_apply]
  rfl

private theorem levi_row {g : G} (hg : g ∈ m.oppositeFullLevi j)
    (i : Fin 3) (hi : i ≠ j) : (m.action.groupEquiv g).val j i = 0 := by
  let z := m.action.linearEquiv.symm (Pi.single i (1 : F.Carrier))
  have hz : z ∈ m.axis j := by
    apply (m.largeField_mem_axis j z).mpr
    simp [z, hi.symm]
  have h := (m.largeField_mem_axis j _).mp ((hg.1 z).mpr hz)
  rw [marked_apply] at h
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

private theorem levi_col {g : G} (hg : g ∈ m.oppositeFullLevi j)
    (i : Fin 3) (hi : i ≠ j) : (m.action.groupEquiv g).val i j = 0 := by
  let z := m.action.linearEquiv.symm (Pi.single j (1 : F.Carrier))
  have hz : z ∈ m.line j := by
    apply (m.largeField_mem_line j z).mpr
    exact ⟨1, by simp [z]⟩
  obtain ⟨c,hc⟩ := (m.largeField_mem_line j _).mp ((hg.2 z).mpr hz)
  rw [marked_apply] at hc
  have h := congrFun hc i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
    smul_zero] using h.symm

private theorem levi_line_action {g : G} (hg : g ∈ m.oppositeFullLevi j)
    (c : F.Carrier) :
    (m.action.groupEquiv g).val.mulVec (c • Pi.single j 1) =
      ((m.action.groupEquiv g).val j j * c) • Pi.single j 1 := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext i
  by_cases hi : i = j
  · subst i
    simp [mul_comm]
  · simp [hi, levi_col m j hg i hi]

private theorem levi_line_nonzero {g : G} (hg : g ∈ m.oppositeFullLevi j) :
    (m.action.groupEquiv g).val j j ≠ 0 := by
  intro hz
  have h := levi_line_action m j hg 1
  simp only [hz, zero_mul, zero_smul, one_smul] at h
  have he : (Pi.single j (1 : F.Carrier) : Fin 3 → F.Carrier) = 0 := by
    apply (m.action.groupEquiv g).toLin'.injective
    change (m.action.groupEquiv g).val.mulVec _ = (m.action.groupEquiv g).val.mulVec 0
    simpa only [Matrix.mulVec_zero] using h
  have := congrFun he j
  simp at this

/-- The special-linear Levi fixes the complementary quotient line pointwise. -/
theorem oppositeK_le_fullLevi : m.K j ≤ m.oppositeFullLevi j := by
  refine le_inf inf_le_left ?_
  apply le_subspaceStabilizer
  intro k hk z hz
  rw [hk.2.2 z hz]
  exact hz

private theorem scalar_commutes_levi (a : F.Carrierˣ) {g : G}
    (hg : g ∈ m.oppositeFullLevi j) :
    Commute (m.oppositeTorusHom j a) g := by
  apply m.action.groupEquiv.injective
  simp only [map_mul, m.oppositeTorusHom_marking]
  apply Subtype.ext
  change Matrix.diagonal _ * _ = _ * Matrix.diagonal _
  ext r s
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hr : r = j <;> by_cases hs : s = j
  · subst r; subst s; simp [mul_comm]
  · subst r; simp [hs, levi_row m j hg s hs]
  · subst s; simp [hr, levi_col m j hg r hr]
  · simp [hr, hs, mul_comm]

/-- Scalars on each of the two blocks centralize the entire full Levi. -/
theorem oppositeTorus_le_centralizer_fullLevi :
    m.oppositeTorus j ≤ Subgroup.centralizer (m.oppositeFullLevi j : Set G) := by
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  exact (scalar_commutes_levi m j a hg).symm.eq

private theorem exists_scalar_line (c : F.Carrier) (hc : c ≠ 0) :
    ∃ a : F.Carrierˣ, (↑a⁻¹ : F.Carrier)^2 = c := by
  obtain ⟨b,hb⟩ := isSquare_of_charTwo' c
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
    exact hc hb
  refine ⟨(Units.mk0 b hb0)⁻¹, ?_⟩
  simpa only [inv_inv, Units.val_mk0, pow_two] using hb.symm

/-- Remove the action on the complementary line by an actual scalar torus
element. This gives the literal source factorization, including over F₄. -/
theorem oppositeFullLevi_factor {g : G} (hg : g ∈ m.oppositeFullLevi j) :
    ∃ k ∈ m.K j, ∃ h ∈ m.oppositeTorus j, g = k*h := by
  obtain ⟨a,ha⟩ := exists_scalar_line ((m.action.groupEquiv g).val j j)
    (levi_line_nonzero m j hg)
  let h := m.oppositeTorusHom j a
  have hh : h ∈ m.oppositeTorus j := ⟨a,rfl⟩
  have hhL := m.oppositeTorus_le_fullLevi j hh
  have heq : ∀ z ∈ m.line j,
      d.space.quotientRepresentation g z = d.space.quotientRepresentation h z := by
    intro z hz
    apply m.action.linearEquiv.injective
    obtain ⟨c,hc⟩ := (m.largeField_mem_line j z).mp hz
    rw [m.action.intertwines, m.action.intertwines]
    change (m.action.groupEquiv g).val.mulVec _ = (m.action.groupEquiv h).val.mulVec _
    rw [← hc, levi_line_action m j hg c]
    change _ = (m.action.groupEquiv (m.oppositeTorusHom j a)).val.mulVec _
    rw [m.oppositeTorusHom_marking]
    ext i
    change _ = linearNatural F 3 (oppositeScalarMatrix F j a) (c • Pi.single j 1) i
    rw [oppositeScalarMatrix_apply]
    by_cases hi : i = j
    · subst i
      simp only [ite_true, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ha]
    · simp [hi]
  refine ⟨g*h⁻¹, ⟨?_, Subgroup.mem_top _, ?_⟩, h, hh, by group⟩
  · exact (subspaceStabilizer _ _).mul_mem hg.1 ((subspaceStabilizer _ _).inv_mem hhL.1)
  · intro z hz
    change d.space.quotientRepresentation (g*h⁻¹) z = z
    rw [map_mul, Module.End.mul_apply]
    rw [heq _ (((m.oppositeFullLevi j).inv_mem hhL).2 z |>.mpr hz)]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl


private theorem root_mem_K {r s : Fin 3} (hrs : r ≠ s) (hrj : r ≠ j) (hsj : s ≠ j) :
    m.action.groupEquiv.symm (SpecialLinearGroup.transvection hrs (1 : F.Carrier)) ∈ m.K j := by
  refine ⟨?_, Subgroup.mem_top _, ?_⟩
  · intro z
    rw [m.largeField_mem_axis, m.largeField_mem_axis, m.action.intertwines,
      m.action.groupEquiv.apply_symm_apply]
    change ((1 + Matrix.single r s (1 : F.Carrier)).mulVec (m.action.linearEquiv z)) j = 0 ↔ _
    simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, hrj.symm]
  · intro z hz
    apply m.action.linearEquiv.injective
    rw [m.action.intertwines, m.action.groupEquiv.apply_symm_apply]
    obtain ⟨c,hc⟩ := (m.largeField_mem_line j z).mp hz
    rw [← hc]
    change (1 + Matrix.single r s (1 : F.Carrier)).mulVec _ = _
    simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, hsj]

private theorem centralizer_root {g : G}
    (hg : g ∈ Subgroup.centralizer (m.K j : Set G))
    {r s : Fin 3} (hrs : r ≠ s) (hrj : r ≠ j) (hsj : s ≠ j) :
    Matrix.transvection r s (1 : F.Carrier) * (m.action.groupEquiv g).val =
      (m.action.groupEquiv g).val * Matrix.transvection r s 1 := by
  have h := Subgroup.mem_centralizer_iff.mp hg _ (root_mem_K m j hrs hrj hsj)
  have he := congrArg m.action.groupEquiv h
  simp only [map_mul, m.action.groupEquiv.apply_symm_apply] at he
  exact congrArg Subtype.val he

private theorem centralizer_axis_diag {g : G}
    (hg : g ∈ Subgroup.centralizer (m.K j : Set G))
    {r s : Fin 3} (hrj : r ≠ j) (hsj : s ≠ j) :
    (m.action.groupEquiv g).val r r = (m.action.groupEquiv g).val s s := by
  by_cases hrs : r = s
  · subst r; rfl
  · have h := congr_fun₂ (centralizer_root m j hg hrs hrj hsj) r s
    simpa only [Matrix.transvection_mul_apply_same, Matrix.mul_transvection_apply_same,
      one_mul, add_right_inj] using h.symm

private theorem centralizer_axis_offdiag {g : G}
    (hg : g ∈ Subgroup.centralizer (m.K j : Set G))
    {r s : Fin 3} (hrs : r ≠ s) (hrj : r ≠ j) (hsj : s ≠ j) :
    (m.action.groupEquiv g).val r s = 0 := by
  have h := congr_fun₂ (centralizer_root m j hg hrs.symm hsj hrj) r r
  rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hrs,
    Matrix.mul_transvection_apply_same, one_mul] at h
  exact (add_left_cancel (h.symm.trans (add_zero _).symm))

private theorem centralizer_diagonal {g : G} (hg : g ∈ m.oppositeFullLevi j)
    (hc : g ∈ Subgroup.centralizer (m.K j : Set G)) (i : Fin 3) (hi : i ≠ j) :
    (m.action.groupEquiv g).val =
      Matrix.diagonal (fun r => if r = j then (m.action.groupEquiv g).val j j
        else (m.action.groupEquiv g).val i i) := by
  ext r s
  by_cases hrs : r = s
  · subst s
    rw [Matrix.diagonal_apply_eq]
    by_cases hrj : r = j
    · simp [hrj]
    · simp only [if_neg hrj]
      exact centralizer_axis_diag m j hc hrj hi
  · rw [Matrix.diagonal_apply_ne _ hrs]
    by_cases hrj : r = j
    · subst r
      exact levi_row m j hg s (Ne.symm hrs)
    · by_cases hsj : s = j
      · subst s
        exact levi_col m j hg r hrs
      · exact centralizer_axis_offdiag m j hc hrs hrj hsj

private theorem centralizer_mem_torus {g : G} (hg : g ∈ m.oppositeFullLevi j)
    (hc : g ∈ Subgroup.centralizer (m.K j : Set G)) : g ∈ m.oppositeTorus j := by
  obtain ⟨i,hi⟩ := exists_ne j
  let a := (m.action.groupEquiv g).val i i
  have hd := centralizer_diagonal m j hg hc i hi
  have hdet : (m.action.groupEquiv g).val j j * a^2 = 1 := by
    have h := (m.action.groupEquiv g).property
    rw [hd, Matrix.det_diagonal] at h
    fin_cases j <;> simpa [Fin.prod_univ_succ, pow_two, mul_comm, mul_left_comm, mul_assoc, a] using h
  have ha : a ≠ 0 := by
    intro h
    simp [h] at hdet
  let u := Units.mk0 a ha
  have hj : (m.action.groupEquiv g).val j j = (↑u⁻¹ : F.Carrier)^2 := by
    change _ = a⁻¹^2
    rw [inv_pow]
    exact (mul_eq_one_iff_eq_inv₀ (pow_ne_zero 2 ha)).mp hdet
  refine ⟨u, ?_⟩
  apply m.action.groupEquiv.injective
  rw [m.oppositeTorusHom_marking]
  apply Subtype.ext
  change Matrix.diagonal _ = _
  rw [hd]
  congr 1
  funext r
  by_cases hr : r = j <;> simp [hr, hj, u, a]

/-- The scalar torus is the centralizer of K in the full Levi. -/
theorem oppositeTorus_eq_centralizer : m.oppositeTorus j =
    m.oppositeFullLevi j ⊓ Subgroup.centralizer (m.K j : Set G) := by
  apply le_antisymm
  · exact le_inf (m.oppositeTorus_le_fullLevi j)
      ((m.oppositeTorus_le_centralizer_fullLevi j).trans
        (Subgroup.centralizer_le (m.oppositeK_le_fullLevi j)))
  · intro g hg
    exact centralizer_mem_torus m j hg.1 hg.2


/-- Membership in the full Levi is precisely a literal product of an
axis special-linear element and a scalar torus element. -/
theorem oppositeFullLevi_mem_iff_mul (g : G) :
    g ∈ m.oppositeFullLevi j ↔
      ∃ k ∈ m.K j, ∃ h ∈ m.oppositeTorus j, g = k * h := by
  constructor
  · exact m.oppositeFullLevi_factor j
  · rintro ⟨k, hk, h, hh, rfl⟩
    exact (m.oppositeFullLevi j).mul_mem
      (m.oppositeK_le_fullLevi j hk) (m.oppositeTorus_le_fullLevi j hh)

/-- The subgroup form of the source factorization K₀ = KH. -/
theorem oppositeFullLevi_eq_sup : m.oppositeFullLevi j = m.K j ⊔ m.oppositeTorus j := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk, h, hh, rfl⟩ := m.oppositeFullLevi_factor j hg
    exact (m.K j ⊔ m.oppositeTorus j).mul_mem
      (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hh)
  · exact sup_le (m.oppositeK_le_fullLevi j) (m.oppositeTorus_le_fullLevi j)

/-- Discharges the full-Levi matrix premise of the opposite-coordinate
complement construction in B.4.9(1). -/
theorem oppositeFullLevi_le_sup : m.oppositeFullLevi j ≤ m.K j ⊔ m.oppositeTorus j :=
  (m.oppositeFullLevi_eq_sup j).le

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
