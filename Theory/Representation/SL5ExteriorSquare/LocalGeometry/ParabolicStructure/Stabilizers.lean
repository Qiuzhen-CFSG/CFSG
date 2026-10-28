module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Setup
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Bivectors
import Mathlib.Tactic.FinCases

/-!
# Stabilizers of the standard binary exterior subspaces

The stabilizers of Λ²Γ₂, Λ²Γ₃, Γ₁ ∧ Γ, and Λ²Γ₄ are exactly the
natural parabolics for Γ₂, Γ₃, Γ₁, and Γ₄. Lower-left zero blocks characterize
the natural parabolics, and the corresponding minor conditions give the forward
inclusions. The ranges of the alternating coefficient matrices recover Γ₂,
Γ₃, and Γ₄. The common line in the supports of Γ₁ ∧ Γ recovers Γ₁.

We also establish strictness and invariance of 0 < V₁ < V₇ < V. The separate
chief-factor assertion additionally requires irreducibility of each factor.

Source: Aschbacher–Smith, Lemma 12.5.2, printed p.817/PDF p.834.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private def actionEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) (g : Group) : W ≃ₗ[ZMod 2] W where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv v := by
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

theorem mem_subspaceStabilizer_iff_preserves {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) (U : Submodule (ZMod 2) W) (g : Group) :
    g ∈ subspaceStabilizer ρ U ↔ ∀ v ∈ U, ρ g v ∈ U := by
  constructor
  · intro h v hv
    exact (h v).mpr hv
  · intro h v
    have hm : U.map (ρ g) = U := Submodule.eq_of_le_of_finrank_eq
      (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)
      ((actionEquiv ρ g).finrank_map_eq U)
    constructor
    · intro hv
      rw [← hm] at hv
      obtain ⟨w, hw, he⟩ := hv
      exact (actionEquiv ρ g).injective he ▸ hw
    · exact h v

theorem mem_parabolic_iff_lowerLeft_zero (k : ℕ) (g : Group) :
    g ∈ parabolic k ↔ ∀ i j : Fin 5, k ≤ i.val → j.val < k → g.val i j = 0 := by
  rw [parabolic, mem_subspaceStabilizer_iff_preserves]
  constructor
  · intro h i j hi hj
    have hv : Pi.single j (1 : ZMod 2) ∈ naturalFlag k := by
      intro l hl
      have hne : l ≠ j := by intro he; subst l; omega
      simp [hne]
    have hh := h _ hv i hi
    change g.val.mulVec (Pi.single j 1) i = 0 at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  · intro h v hv i hi
    change ∑ j, g.val i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < k
    · rw [h i j hi hj, zero_mul]
    · rw [hv j (Nat.le_of_not_gt hj), mul_zero]

theorem mem_exteriorStabilizer_coordinateSpan_iff (S : Finset (Fin 10)) (g : Group) :
    g ∈ exteriorStabilizer (coordinateSpan S) ↔
      ∀ s t : Fin 10, s ∉ S → t ∈ S → actionMatrix g s t = 0 := by
  rw [exteriorStabilizer, mem_subspaceStabilizer_iff_preserves]
  constructor
  · intro h s t hs ht
    have hb : basis t ∈ coordinateSpan S := Submodule.subset_span ⟨t, ht, rfl⟩
    have hh := (mem_coordinateSpan S _).mp (h _ hb) s hs
    simpa only [coordinates_action, coordinates_basis, Matrix.mulVec_single_one,
      Matrix.col_apply] using hh
  · intro h v hv
    apply (mem_coordinateSpan S _).mpr
    intro s hs
    rw [coordinates_action]
    change ∑ t, actionMatrix g s t * coordinates v t = 0
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ S
    · rw [h s t hs ht, zero_mul]
    · rw [(mem_coordinateSpan S v).mp hv t ht, mul_zero]

private theorem pair_increasing (t : Fin 10) : (pair t 0).val < (pair t 1).val :=
  (by decide : ∀ t : Fin 10, (pair t 0).val < (pair t 1).val) t

private theorem parabolic_le_stabilizer_exteriorFlag (k : ℕ) (S : Finset (Fin 10))
    (hS : ∀ t, t ∈ S ↔ (pair t 1).val < k) :
    parabolic k ≤ exteriorStabilizer (coordinateSpan S) := by
  intro g hg
  have h := (mem_parabolic_iff_lowerLeft_zero k g).mp hg
  rw [mem_exteriorStabilizer_coordinateSpan_iff]
  intro s t hs ht
  have hs1 : k ≤ (pair s 1).val := Nat.le_of_not_gt (fun he => hs ((hS s).mpr he))
  have ht1 := (hS t).mp ht
  have ht0 := (pair_increasing t).trans ht1
  simp only [actionMatrix, h _ _ hs1 ht0, h _ _ hs1 ht1,
    mul_zero, zero_mul, sub_self]

private theorem parabolic_le_stabilizer_wedgeFlag (k : ℕ) (S : Finset (Fin 10))
    (hS : ∀ t, t ∈ S ↔ (pair t 0).val < k) :
    parabolic k ≤ exteriorStabilizer (coordinateSpan S) := by
  intro g hg
  have h := (mem_parabolic_iff_lowerLeft_zero k g).mp hg
  rw [mem_exteriorStabilizer_coordinateSpan_iff]
  intro s t hs ht
  have hs0 : k ≤ (pair s 0).val := Nat.le_of_not_gt (fun he => hs ((hS s).mpr he))
  have hs1 := hs0.trans (pair_increasing s).le
  have ht0 := (hS t).mp ht
  simp only [actionMatrix, h _ _ hs0 ht0, h _ _ hs1 ht0,
    zero_mul, sub_self]

/-- The two-space parabolic preserves Λ²Γ₂. -/
theorem parabolic_two_le_stabilizer_V₁ : parabolic 2 ≤ exteriorStabilizer V₁ :=
  parabolic_le_stabilizer_exteriorFlag 2 {0} (by decide)

/-- The three-space parabolic preserves Λ²Γ₃. -/
theorem parabolic_three_le_stabilizer_V₃ : parabolic 3 ≤ exteriorStabilizer V₃ :=
  parabolic_le_stabilizer_exteriorFlag 3 {0, 1, 4} (by decide)

/-- The line parabolic preserves Γ₁ ∧ Γ. -/
theorem parabolic_one_le_stabilizer_V₄ : parabolic 1 ≤ exteriorStabilizer V₄ :=
  parabolic_le_stabilizer_wedgeFlag 1 {0, 1, 2, 3} (by decide)

/-- The four-space parabolic preserves Λ²Γ₄. -/
theorem parabolic_four_le_stabilizer_V₆ : parabolic 4 ≤ exteriorStabilizer V₆ :=
  parabolic_le_stabilizer_exteriorFlag 4 {0, 1, 2, 4, 5, 7} (by decide)

/-- The two-space parabolic preserves Γ₂ ∧ Γ. -/
theorem parabolic_two_le_stabilizer_V₇ : parabolic 2 ≤ exteriorStabilizer V₇ :=
  parabolic_le_stabilizer_wedgeFlag 2 {0, 1, 2, 3, 4, 5, 6} (by decide)

private theorem alternatingMatrix_row_zero (c : Coordinates) (k : ℕ)
    (hc : ∀ t, k ≤ (pair t 1).val → c t = 0)
    (i j : Fin 5) (hi : k ≤ i.val) : alternatingMatrix c i j = 0 := by
  fin_cases i
  · change k ≤ 0 at hi
    fin_cases j
    · rfl
    · exact hc 0 (by change k ≤ 1; omega)
    · exact hc 1 (by change k ≤ 2; omega)
    · exact hc 2 (by change k ≤ 3; omega)
    · exact hc 3 (by change k ≤ 4; omega)
  · change k ≤ 1 at hi
    fin_cases j
    · exact hc 0 (by change k ≤ 1; omega)
    · rfl
    · exact hc 4 (by change k ≤ 2; omega)
    · exact hc 5 (by change k ≤ 3; omega)
    · exact hc 6 (by change k ≤ 4; omega)
  · change k ≤ 2 at hi
    fin_cases j
    · exact hc 1 (by change k ≤ 2; omega)
    · exact hc 4 (by change k ≤ 2; omega)
    · rfl
    · exact hc 7 (by change k ≤ 3; omega)
    · exact hc 8 (by change k ≤ 4; omega)
  · change k ≤ 3 at hi
    fin_cases j
    · exact hc 2 (by change k ≤ 3; omega)
    · exact hc 5 (by change k ≤ 3; omega)
    · exact hc 7 (by change k ≤ 3; omega)
    · rfl
    · exact hc 9 (by change k ≤ 4; omega)
  · change k ≤ 4 at hi
    fin_cases j
    · exact hc 3 (by change k ≤ 4; omega)
    · exact hc 6 (by change k ≤ 4; omega)
    · exact hc 8 (by change k ≤ 4; omega)
    · exact hc 9 (by change k ≤ 4; omega)
    · rfl

theorem range_bivectorMatrix_le_flag (k : ℕ) (S : Finset (Fin 10))
    (hS : ∀ t ∈ S, (pair t 1).val < k) (v : V) (hv : v ∈ coordinateSpan S) :
    LinearMap.range (bivectorMatrix v).mulVecLin ≤ naturalFlag k := by
  rintro _ ⟨x, rfl⟩ i hi
  change ∑ j, bivectorMatrix v i j * x j = 0
  apply Finset.sum_eq_zero
  intro j _
  have hz : bivectorMatrix v i j = 0 := alternatingMatrix_row_zero _ k
    (fun t ht => (mem_coordinateSpan S v).mp hv t (by
      intro hm
      have := hS t hm
      omega)) i j hi
  rw [hz, zero_mul]

private theorem basis_support_left (t : Fin 10) :
    Pi.single (pair t 0) (1 : ZMod 2) ∈ LinearMap.range (bivectorMatrix (basis t)).mulVecLin := by
  refine ⟨Pi.single (pair t 1) 1, ?_⟩
  change (bivectorMatrix (basis t)).mulVec _ = _
  rw [Matrix.mulVec_single_one]
  unfold bivectorMatrix
  rw [coordinates_basis]
  ext i
  fin_cases t <;> fin_cases i <;> rfl

private theorem basis_support_right (t : Fin 10) :
    Pi.single (pair t 1) (1 : ZMod 2) ∈ LinearMap.range (bivectorMatrix (basis t)).mulVecLin := by
  refine ⟨Pi.single (pair t 0) 1, ?_⟩
  change (bivectorMatrix (basis t)).mulVec _ = _
  rw [Matrix.mulVec_single_one]
  unfold bivectorMatrix
  rw [coordinates_basis]
  ext i
  fin_cases t <;> fin_cases i <;> rfl

theorem exteriorStabilizer_le_parabolic_of_support (k : ℕ) (S : Finset (Fin 10))
    (hS : ∀ t ∈ S, (pair t 1).val < k)
    (hcover : ∀ j : Fin 5, j.val < k → ∃ t ∈ S, j = pair t 0 ∨ j = pair t 1) :
    exteriorStabilizer (coordinateSpan S) ≤ parabolic k := by
  intro g hg
  apply (mem_parabolic_iff_lowerLeft_zero k g).mpr
  intro i j hi hj
  obtain ⟨t, ht, hjt⟩ := hcover j hj
  have hb : basis t ∈ coordinateSpan S := Submodule.subset_span ⟨t, ht, rfl⟩
  have hgb := (hg (basis t)).mpr hb
  have hjb : Pi.single j (1 : ZMod 2) ∈ LinearMap.range (bivectorMatrix (basis t)).mulVecLin := by
    rcases hjt with rfl | rfl
    · exact basis_support_left t
    · exact basis_support_right t
  have hm : specialLinearNatural 5 g (Pi.single j 1) ∈
      LinearMap.range (bivectorMatrix (exteriorAction 2 g (basis t))).mulVecLin := by
    rw [range_bivectorMatrix_action]
    exact ⟨_, hjb, rfl⟩
  have hz := range_bivectorMatrix_le_flag k S hS _ hgb hm i hi
  change g.val.mulVec (Pi.single j 1) i = 0 at hz
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hz

theorem exteriorStabilizer_V₁_eq_parabolic : exteriorStabilizer V₁ = parabolic 2 := by
  apply le_antisymm _ parabolic_two_le_stabilizer_V₁
  exact exteriorStabilizer_le_parabolic_of_support 2 {0} (by decide) (by decide)

theorem exteriorStabilizer_V₃_eq_parabolic : exteriorStabilizer V₃ = parabolic 3 := by
  apply le_antisymm _ parabolic_three_le_stabilizer_V₃
  exact exteriorStabilizer_le_parabolic_of_support 3 {0, 1, 4} (by decide) (by decide)

theorem exteriorStabilizer_V₆_eq_parabolic : exteriorStabilizer V₆ = parabolic 4 := by
  apply le_antisymm _ parabolic_four_le_stabilizer_V₆
  exact exteriorStabilizer_le_parabolic_of_support 4 {0, 1, 2, 4, 5, 7} (by decide) (by decide)

/-- Every nonzero bivector in Γ₁ ∧ Γ has Γ₁ in its support. -/
theorem first_vector_mem_support_V₄ (v : V) (hv : v ∈ V₄) (hn : v ≠ 0) :
    Pi.single 0 (1 : ZMod 2) ∈ LinearMap.range (bivectorMatrix v).mulVecLin := by
  have hz := (mem_coordinateSpan {0, 1, 2, 3} v).mp hv
  have hex : ∃ t, coordinates v t ≠ 0 := by
    by_contra h
    apply hn
    apply coordinates.injective
    ext t
    simpa using not_exists.mp h t
  obtain ⟨t, ht⟩ := hex
  have htS : t ∈ ({0, 1, 2, 3} : Finset (Fin 10)) := by
    by_contra h
    exact ht (hz t h)
  have ht1 : coordinates v t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  have hz4 := hz 4 (by decide)
  have hz5 := hz 5 (by decide)
  have hz6 := hz 6 (by decide)
  have hz7 := hz 7 (by decide)
  have hz8 := hz 8 (by decide)
  have hz9 := hz 9 (by decide)
  refine ⟨Pi.single (pair t 1) 1, ?_⟩
  change (bivectorMatrix v).mulVec _ = _
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases t <;> fin_cases i <;>
    simp_all [bivectorMatrix, alternatingMatrix, pair, Matrix.col_apply]

private theorem second_coordinate_support_basis_one
    (x : Fin 5 → ZMod 2) (hx : x ∈ LinearMap.range (bivectorMatrix (basis 1)).mulVecLin) :
    x 1 = 0 := by
  obtain ⟨w, rfl⟩ := hx
  change (bivectorMatrix (basis 1)).mulVec w 1 = 0
  unfold bivectorMatrix
  rw [coordinates_basis]
  simp [alternatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The common line in the supports of Γ₁ ∧ Γ recovers its natural stabilizer. -/
theorem exteriorStabilizer_V₄_eq_parabolic : exteriorStabilizer V₄ = parabolic 1 := by
  apply le_antisymm _ parabolic_one_le_stabilizer_V₄
  intro g hg
  have hsupport (t : Fin 10) (ht : t ∈ ({0, 1, 2, 3} : Finset (Fin 10))) :
      specialLinearNatural 5 g (Pi.single 0 1) ∈
        LinearMap.range (bivectorMatrix (basis t)).mulVecLin := by
    let w := exteriorAction 2 g⁻¹ (basis t)
    have hw : w ∈ V₄ := ((exteriorStabilizer V₄).inv_mem hg (basis t)).mpr
      (Submodule.subset_span ⟨t, ht, rfl⟩)
    have hgw : exteriorAction 2 g w = basis t := by
      change (exteriorAction 2 g * exteriorAction 2 g⁻¹) (basis t) = basis t
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hwn : w ≠ 0 := by
      intro h
      have he := congrArg (exteriorAction 2 g) h
      rw [hgw, map_zero] at he
      exact basis.ne_zero t he
    rw [← hgw, range_bivectorMatrix_action]
    exact ⟨_, first_vector_mem_support_V₄ w hw hwn, rfl⟩
  have hzero := hsupport 0 (by decide)
  change specialLinearNatural 5 g (Pi.single 0 1) ∈
    LinearMap.range (bivectorMatrix decomposable).mulVecLin at hzero
  rw [range_bivectorMatrix_decomposable] at hzero
  have hone := second_coordinate_support_basis_one _ (hsupport 1 (by decide))
  apply (mem_parabolic_iff_lowerLeft_zero 1 g).mpr
  intro i j hi hj
  have hj0 : j = 0 := Fin.ext (by omega)
  subst j
  have he : specialLinearNatural 5 g (Pi.single 0 1) i = 0 := by
    by_cases hi2 : 2 ≤ i.val
    · exact hzero i hi2
    · have hi1 : i = 1 := Fin.ext (by omega)
      simpa only [hi1] using hone
  change g.val.mulVec (Pi.single 0 1) i = 0 at he
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using he

/-- Every source parabolic contains the marked upper-triangular subgroup. -/
theorem flagGroup_le_parabolic (k : ℕ) (hk : k < 5) : flagGroup ≤ parabolic k :=
  iInf_le (fun j : Fin 5 => parabolic j.val) ⟨k, hk⟩

/-- The standard five source subspaces are invariant under the marked flag group. -/
theorem flagGroup_stabilizes_standard :
    flagGroup ≤ exteriorStabilizer V₁ ∧ flagGroup ≤ exteriorStabilizer V₃ ∧
    flagGroup ≤ exteriorStabilizer V₄ ∧ flagGroup ≤ exteriorStabilizer V₆ ∧
    flagGroup ≤ exteriorStabilizer V₇ := by
  exact ⟨(flagGroup_le_parabolic 2 (by decide)).trans parabolic_two_le_stabilizer_V₁,
    (flagGroup_le_parabolic 3 (by decide)).trans parabolic_three_le_stabilizer_V₃,
    (flagGroup_le_parabolic 1 (by decide)).trans parabolic_one_le_stabilizer_V₄,
    (flagGroup_le_parabolic 4 (by decide)).trans parabolic_four_le_stabilizer_V₆,
    (flagGroup_le_parabolic 2 (by decide)).trans parabolic_two_le_stabilizer_V₇⟩

/-- The filtration in the first source clause is strictly increasing. Irreducibility
of its factors is a separate representation-theoretic assertion. -/
theorem standard_chief_chain_strict :
    (⊥ : Submodule (ZMod 2) V) < V₁ ∧ V₁ < V₇ ∧ V₇ < ⊤ := by
  have h17 : V₁ ≤ V₇ := Submodule.span_mono (Set.image_mono (by
    intro i hi
    have he : i = 0 := by simpa using hi
    subst i
    simp))
  have hn0 : V₁ ≠ ⊥ := by
    intro h
    have he := standard_dimensions.1
    rw [h, finrank_bot] at he
    omega
  have hn17 : V₁ ≠ V₇ := by
    intro h
    have he := standard_dimensions.1
    rw [h, standard_dimensions.2.2.2.2.1] at he
    omega
  have hn7 : V₇ ≠ ⊤ := by
    intro h
    have hmem : basis 9 ∈ V₇ := h ▸ Submodule.mem_top
    have he := (mem_coordinateSpan _ _).mp hmem 9 (by decide)
    rw [coordinates_basis] at he
    norm_num at he
  exact ⟨lt_of_le_of_ne bot_le hn0.symm, lt_of_le_of_ne h17 hn17,
    lt_of_le_of_ne le_top hn7⟩

/-- Both proper terms of the source chief filtration are invariant under its
literal group M₁, the stabilizer of V₁. -/
theorem standard_chief_chain_invariant :
    exteriorStabilizer V₁ ≤ exteriorStabilizer V₇ := by
  rw [exteriorStabilizer_V₁_eq_parabolic]
  exact parabolic_two_le_stabilizer_V₇

end Representation.SL5ExteriorSquare
