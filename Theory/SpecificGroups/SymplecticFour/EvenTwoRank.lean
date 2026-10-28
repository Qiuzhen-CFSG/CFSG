module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Two-rank of symplectic four-space over an even field

In standard Sylow coordinates `(b,u,w,v)`, the square-one condition implies
`b*v = 0`. Applying this to products shows that each elementary abelian
subgroup has either `b = 0` throughout or `v = 0` throughout. Its remaining
three coordinates bound its order by q³. The symmetric-matrix plane radical
has exactly q³ elements and attains this bound.

Sylow conjugacy therefore gives two-rank 3n for Sp₄(2ⁿ). Triviality of the
actual center in characteristic two transports the calculation to its central
quotient. For n ≥ 2, root-generated perfectness identifies the genuine derived
carriers with the whole groups. No automorphism-rank assertion is made here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the rank
table on printed p.356 and the inspection in 16.3.9, printed p.1180; the paired
symplectic models occur in 16.1.7(3a,d), printed p.1172.
-/

public section

open Matrix Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.EvenTwoRank
variable {F : Type*} [Field F] [CharP F 2]

private def b (g : unipotent (F := F)) : F := g.val.val (.inl 0) (.inl 1)
private def u (g : unipotent (F := F)) : F := g.val.val (.inl 0) (.inr 0)
private def w (g : unipotent (F := F)) : F := g.val.val (.inl 1) (.inr 0)
private def v (g : unipotent (F := F)) : F := g.val.val (.inl 1) (.inr 1)

private theorem matrix_eq (g : unipotent (F := F)) :
    g.val.val = fromBlocks !![1, b g; 0, 1]
      !![u g, w g + b g * v g; w g, v g] 0 !![1, 0; b g, 1] := by
  have hg := (mem_unipotent_iff g.val).mp g.property
  have hz := (mem_borel_iff g.val).mp hg.1
  have h (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M => M i j)
    (SymplecticGroup.mem_iff'.mp g.val.property)
  have h00 := h (.inl 0) (.inr 0)
  have h01 := h (.inl 0) (.inr 1)
  have h10 := h (.inl 1) (.inr 0)
  have h11 := h (.inl 1) (.inr 1)
  have h23 := h (.inr 0) (.inr 1)
  simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, hz.1, hz.2, hg.2.1, hg.2.2, Matrix.transpose_apply] at h00 h01 h10 h11
  simp only [h01, mul_zero, neg_zero, zero_add, neg_inj] at h11
  have h30 : g.val.val (.inr 1) (.inr 0) = b g := by
    have he : b g + g.val.val (.inr 1) (.inr 0) = 0 := by
      simpa only [b, h00, mul_one, CharTwo.neg_eq] using h10
    exact (CharTwo.add_eq_zero.mp he).symm
  have h03 : g.val.val (.inl 0) (.inr 1) = w g + b g * v g := by
    simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_two, h00, h01, h11, h30,
      Matrix.transpose_apply] at h23
    have he : g.val.val (.inl 0) (.inr 1) = w g - b g * v g := by
      dsimp [w, v]
      linear_combination h23
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using he
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, hg.2.1, hg.2.2, hz.1, hz.2, h00, h01, h11, h30, h03,
      b, u, w, v]

private theorem ext_coordinates {g h : unipotent (F := F)}
    (hb : b g = b h) (hu : u g = u h) (hw : w g = w h) (hv : v g = v h) : g = h := by
  apply Subtype.ext
  apply Subtype.ext
  rw [matrix_eq g, matrix_eq h, hb, hu, hw, hv]

private theorem b_mul (g h : unipotent (F := F)) : b (g * h) = b g + b h := by
  change (g.val.val * h.val.val) (.inl 0) (.inl 1) = _
  rw [matrix_eq g, matrix_eq h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, add_comm]

private theorem v_mul (g h : unipotent (F := F)) : v (g * h) = v g + v h := by
  change (g.val.val * h.val.val) (.inl 1) (.inr 1) = _
  rw [matrix_eq g, matrix_eq h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, add_comm]

private theorem involution_coordinates (g : unipotent (F := F)) (hg : g ^ 2 = 1) :
    b g * v g = 0 := by
  rw [pow_two] at hg
  have he := congrArg (fun x : unipotent (F := F) => x.val.val (.inl 1) (.inr 0)) hg
  change (g.val.val * g.val.val) (.inl 1) (.inr 0) = 0 at he
  rw [matrix_eq g] at he
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, CharTwo.add_self_eq_zero, mul_comm, ← add_assoc] using he

/-- In characteristic two, the elementary subgroups lie in one of two
three-coordinate families in the standard Sylow group. -/
private theorem elementary_coordinate_alternative
    (A : Subgroup (unipotent (F := F))) [IsElementaryAbelian 2 A] :
    (∀ a : A, b a.val = 0) ∨ (∀ a : A, v a.val = 0) := by
  have hs (a : A) : b a.val * v a.val = 0 := involution_coordinates a.val
    (congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a))
  by_cases hb : ∀ a : A, b a.val = 0
  · exact Or.inl hb
  · push Not at hb
    obtain ⟨a, ha⟩ := hb
    have hav : v a.val = 0 := (mul_eq_zero.mp (hs a)).resolve_left ha
    refine Or.inr (fun c => ?_)
    by_cases hc : b c.val = 0
    · have hac := hs (a * c)
      change b (a.val * c.val) * v (a.val * c.val) = 0 at hac
      rw [b_mul, v_mul, hc, hav, add_zero, zero_add] at hac
      exact (mul_eq_zero.mp hac).resolve_left ha
    · exact (mul_eq_zero.mp (hs c)).resolve_left hc

/-- Every elementary abelian subgroup of the standard Sylow has order at most q³. -/
theorem elementary_card_le [Finite F]
    (A : Subgroup (unipotent (F := F))) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ Nat.card F ^ 3 := by
  have hc : Nat.card (F × F × F) = Nat.card F ^ 3 := by
    simp only [Nat.card_prod]
    ring
  rw [← hc]
  rcases elementary_coordinate_alternative A with hb | hv
  · apply Nat.card_le_card_of_injective (fun a : A => (u a.val, w a.val, v a.val))
    intro a c h
    apply Subtype.ext
    exact ext_coordinates ((hb a).trans (hb c).symm)
      (congrArg Prod.fst h) (congrArg (fun t => t.2.1) h) (congrArg (fun t => t.2.2) h)
  · apply Nat.card_le_card_of_injective (fun a : A => (b a.val, u a.val, w a.val))
    intro a c h
    apply Subtype.ext
    exact ext_coordinates (congrArg Prod.fst h) (congrArg (fun t => t.2.1) h)
      (congrArg (fun t => t.2.2) h) ((hv a).trans (hv c).symm)

private def symmetricCoordinates : Plane.symmetricMatrices F ≃ (F × F × F) where
  toFun B := (B.val 0 0, B.val 0 1, B.val 1 1)
  invFun t := ⟨!![t.1, t.2.1; t.2.1, t.2.2], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    exact B.property.apply 1 0
  right_inv _ := rfl

omit [CharP F 2] in
/-- The plane radical has exactly three independent field coordinates. -/
theorem card_plane_radical [Finite F] :
    Nat.card (Plane.radical (F := F)) = Nat.card F ^ 3 := by
  rw [Nat.card_congr Plane.radicalEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Plane.symmetricMatrices F) ≃ _),
    Nat.card_congr (symmetricCoordinates (F := F)), Nat.card_prod, Nat.card_prod]
  ring

/-- The symmetric-matrix radical realizes the lower two-rank bound. -/
theorem three_mul_le_rank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    3 * n ≤ primeRank 2 (Sp F) := by
  let : CommGroup (Plane.radical (F := F)) := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding Plane.radical_sq
    (show Nat.card (Plane.radical (F := F)) = 2 ^ (3 * n) by
      rw [card_plane_radical, hF, ← pow_mul, Nat.mul_comm n 3])
    ((planeLocal (F := F)).subtype.comp (Plane.radical (F := F)).subtype)
  exact Subtype.val_injective.comp Subtype.val_injective

omit [CharP F 2] in
/-- The exact two-rank of the matrix group, with characteristic supplied by
its field cardinality. This also covers the whole binary group. -/
theorem rank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    primeRank 2 (Sp F) = 3 * n := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  apply le_antisymm _ (three_mul_le_rank hF)
  rw [(unipotentSylow hF hn).primeRank_eq]
  change primeRank 2 (unipotent (F := F)) ≤ _
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  have hc := elementary_card_le A
  rwa [hF, ← pow_mul, Nat.mul_comm n 3] at hc

omit [CharP F 2] in
/-- Exact rank of the quotient by the actual symplectic center. -/
theorem projective_rank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    primeRank 2 (Sp F ⧸ center (Sp F)) = 3 * n := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  rw [← primeRank_equiv 2 (EvenProjective.equiv (F := F))]
  exact rank hF hn

omit [Field F] [CharP F 2] in
private theorem card_gt_two {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : 2 < Nat.card F := by
  rw [hF]
  exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)

omit [CharP F 2] in
/-- Inclusion identifies the genuine derived matrix group with the full group. -/
noncomputable def derivedEquiv [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : commutator (Sp F) ≃* Sp F := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact derivedEquivFull_of_card_gt_two (card_gt_two hF hn)

omit [CharP F 2] in
/-- The nonbinary projective group is perfect, with no change of quotient. -/
theorem projective_perfect [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    Group.IsPerfect (Sp F ⧸ center (Sp F)) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let := perfect_of_card_gt_two (card_gt_two hF hn)
  infer_instance

omit [CharP F 2] in
/-- Inclusion identifies the derived subgroup of the actual projective quotient. -/
noncomputable def projectiveDerivedEquiv [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    commutator (Sp F ⧸ center (Sp F)) ≃* (Sp F ⧸ center (Sp F)) := by
  let := projective_perfect hF hn
  exact (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv

omit [CharP F 2] in
/-- Exact two-rank of the genuine nonbinary derived matrix group. -/
theorem derived_rank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    primeRank 2 (commutator (Sp F)) = 3 * n := by
  rw [primeRank_equiv 2 (derivedEquiv hF hn)]
  exact rank hF (by omega)

omit [CharP F 2] in
/-- Exact two-rank of the genuine derived subgroup of the projective quotient. -/
theorem projective_derived_rank [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    primeRank 2 (commutator (Sp F ⧸ center (Sp F))) = 3 * n := by
  rw [primeRank_equiv 2 (projectiveDerivedEquiv hF hn)]
  exact projective_rank hF (by omega)
end Theory.SpecificGroups.SymplecticFour.EvenTwoRank
