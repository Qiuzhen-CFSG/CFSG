module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu

/-!
# Binary fixed masks in the literal max1 kernel

The certified pair labels intertwine the marked generators with their star
permutations, using left conjugation. Generation extends this identity to the
whole local subgroup. Every basis vector occurs as a pair label, so the action
on all 2048 binary masks follows. The resulting bijection identifies element
and simultaneous centralizers in the actual local kernel with fixed masks.

This is the coordinate step for the octad bounds used in Aschbacher–Smith
A.3.12(17) and 1.3.9; the local model is GLS3 Table 5.3i. The numerical labels
and generator identities are the certified ATLAS max1 data in
`Janko4.Cardinality.QuotientCount.Image.StarData` and `Coordinates`.
-/

public section

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.LiteralBinary
open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount
open Janko4.Cardinality.QuotientCount.Image Janko4.Cardinality.KernelCount
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

@[expose] def maskValue (m : ℕ) : localKernel hA hB :=
  coordinates hA hB (fun i => m.testBit i.val)

private lemma maskValue_zero : maskValue hA hB 0 = 1 := by
  apply Subtype.ext
  simp [maskValue, coordinates_val, binaryProduct_zero]

private lemma maskValue_xor (m n : ℕ) :
    maskValue hA hB (Nat.xor m n) = maskValue hA hB m * maskValue hA hB n := by
  change maskValue hA hB (m ^^^ n) = _
  simp only [maskValue, coordinates_mul, Nat.testBit_xor]

private lemma maskValue_fold (l : List ℕ) :
    maskValue hA hB (l.foldr Nat.xor 0) = (l.map (maskValue hA hB)).prod := by
  induction l with
  | nil => exact maskValue_zero hA hB
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      maskValue_xor] using congrArg (maskValue hA hB a * ·) ih

private lemma maskValue_maskImage (masks : Fin 11 → ℕ) (m : ℕ) :
    (maskValue hA hB (maskImage masks m) : max1Subgroup hA hB) =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (masks i).testBit j.val)) (fun i => m.testBit i.val) := by
  rw [maskImage, maskValue_fold]
  simp only [List.map_ofFn, SubmonoidClass.coe_list_prod]
  rw [binaryProduct]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · change (maskValue hA hB 0 : max1Subgroup hA hB) = 1
    rw [maskValue_zero]
    rfl

private lemma right_compatible_x (i j : Fin 24) :
    action hA hB (localX hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightX i) (rightX j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightX, maskValue_maskImage]
  exact right_conj_coordinates_x hA hB _

private lemma right_compatible_y (i j : Fin 24) :
    action hA hB (localY hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightY i) (rightY j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightY, maskValue_maskImage]
  exact right_conj_coordinates_y hA hB _

private def Compatible (p : Equiv.Perm (localKernel hA hB) × Equiv.Perm (Fin 24)) : Prop :=
  ∀ i j, p.1 (maskValue hA hB (pairLabel i j)) =
    maskValue hA hB (pairLabel (p.2 i) (p.2 j))

private lemma compatible_inv {p : Equiv.Perm (localKernel hA hB) × Equiv.Perm (Fin 24)}
    (h : Compatible hA hB p) : Compatible hA hB p⁻¹ := by
  intro i j
  apply p.1.injective
  simpa using (h (p.2⁻¹ i) (p.2⁻¹ j)).symm

theorem maskValue_injective_bounded {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : maskValue hA hB m = maskValue hA hB n) : m = n := by
  have hb := coordinates_injective hA hB h
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]


@[expose] noncomputable def starProjection : max1Subgroup hA hB →* Equiv.Perm (Fin 24) :=
  StarGroup.subtype.comp ((actionImageEquivStarGroup hA hB).toMonoidHom.comp
    (action hA hB).rangeRestrict)

private theorem projection_x : starProjection hA hB (localX hA hB) = starX :=
  actionImageEquivStarGroup_x hA hB

private theorem projection_y : starProjection hA hB (localY hA hB) = starY :=
  actionImageEquivStarGroup_y hA hB

/-- The star permutation intertwines the actual left-conjugation action on all pair labels. -/
theorem starProjection_compatible (g : max1Subgroup hA hB) :
    ∀ i j, action hA hB g (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (starProjection hA hB g i) (starProjection hA hB g j)) := by
  change Compatible hA hB (action hA hB g, starProjection hA hB g)
  have hg : g ∈ Subgroup.closure {localX hA hB, localY hA hB} := by
    rw [localXY_generate]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · rw [projection_x]
      have hr : Compatible hA hB (action hA hB (localX hA hB)⁻¹, rightX) :=
        right_compatible_x hA hB
      simpa only [Prod.inv_mk, ← map_inv, inv_inv, starX] using compatible_inv hA hB hr
    · obtain rfl := Set.mem_singleton_iff.mp hg
      rw [projection_y]
      have hr : Compatible hA hB (action hA hB (localY hA hB)⁻¹, rightY) :=
        right_compatible_y hA hB
      simpa only [Prod.inv_mk, ← map_inv, inv_inv, starY] using compatible_inv hA hB hr
  | one => intro i j; simp only [map_one, Equiv.Perm.one_apply]
  | mul g h hg hh ihg ihh =>
    intro i j
    change (action hA hB (g * h)) _ = _
    rw [map_mul, map_mul]
    change action hA hB g (action hA hB h _) = _
    rw [ihh, ihg]
    rfl
  | inv g hg ih =>
    simpa only [Prod.inv_mk, map_inv] using compatible_inv hA hB ih


private theorem maskValue_basis (i : Fin 11) :
    (maskValue hA hB (2 ^ i.val) : max1Subgroup hA hB) = basis hA hB i := by
  simp only [maskValue, coordinates_val, Nat.testBit_two_pow]
  convert binaryProduct_single (basis hA hB) i using 2
  funext j
  simp only [Fin.ext_iff, eq_comm]

/-- Columns of the binary action read from the actual star permutation. -/
@[expose] def starMasks (p : Equiv.Perm (Fin 24)) (i : Fin 11) : ℕ :=
  pairLabel (p (basisPair i).1) (p (basisPair i).2)

/-- Evaluated masks intertwine the entire conjugation action, not just its generators. -/
theorem action_maskValue (g : max1Subgroup hA hB) (m : ℕ) :
    action hA hB g (maskValue hA hB m) =
      maskValue hA hB (maskImage (starMasks (starProjection hA hB g)) m) := by
  have hb (i : Fin 11) :
      (MulAut.conj g) (basis hA hB i) =
        (maskValue hA hB (starMasks (starProjection hA hB g) i) : max1Subgroup hA hB) := by
    have h := starProjection_compatible hA hB g (basisPair i).1 (basisPair i).2
    rw [pairLabel_basisPair] at h
    have h' := congrArg (fun n : localKernel hA hB => (n : max1Subgroup hA hB)) h
    simpa only [action_apply, maskValue_basis, MulAut.conj_apply, starMasks] using h'
  apply Subtype.ext
  rw [maskValue_maskImage, action_apply]
  change (MulAut.conj g).toMonoidHom (binaryProduct (basis hA hB) _) = _
  rw [map_binaryProduct]
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hb, maskValue, coordinates_val]

/-- Every action column has eleven binary digits, so its XOR sum does too. -/
theorem maskImage_starMasks_lt (p : Equiv.Perm (Fin 24)) (m : ℕ) :
    maskImage (starMasks p) m < 2048 := by
  have h (l : List ℕ) (hl : ∀ n ∈ l, n < 2 ^ 11) :
      l.foldr Nat.xor 0 < 2 ^ 11 := by
    induction l with
    | nil => decide
    | cons a l ih =>
      exact Nat.xor_lt_two_pow (hl a (List.mem_cons_self ..))
        (ih (fun n hn => hl n (List.mem_cons_of_mem a hn)))
  apply h
  intro n hn
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
  split_ifs
  · exact pairLabel_lt _ _
  · decide

/-- A finite mask parametrization of the actual elementary kernel. -/
noncomputable def maskEquiv : Fin 2048 ≃ localKernel hA hB :=
  Equiv.ofBijective (fun m => maskValue hA hB m.val) (by
    have hi : Function.Injective (fun m : Fin 2048 => maskValue hA hB m.val) := by
      intro m n he
      exact Fin.ext (maskValue_injective_bounded hA hB m.isLt n.isLt he)
    exact (Nat.bijective_iff_injective_and_card _).mpr
      ⟨hi, by rw [Nat.card_fin, localKernel_card]⟩)

/-- Commuting in the actual local subgroup is exactly a fixed binary mask. -/
theorem commute_mask_iff (g : max1Subgroup hA hB) (m : Fin 2048) :
    g * (maskEquiv hA hB m : max1Subgroup hA hB) =
      (maskEquiv hA hB m : max1Subgroup hA hB) * g ↔
    maskImage (starMasks (starProjection hA hB g)) m.val = m.val := by
  have he : action hA hB g (maskValue hA hB m.val) = maskValue hA hB m.val ↔
      maskImage (starMasks (starProjection hA hB g)) m.val = m.val := by
    rw [action_maskValue]
    exact ⟨maskValue_injective_bounded hA hB (maskImage_starMasks_lt _ _) m.isLt,
      fun h => congrArg (maskValue hA hB) h⟩
  rw [← he]
  change g * (maskValue hA hB m.val : max1Subgroup hA hB) =
    (maskValue hA hB m.val : max1Subgroup hA hB) * g ↔ _
  constructor
  · intro h
    apply Subtype.ext
    rw [action_apply]
    exact mul_inv_eq_iff_eq_mul.mpr h
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)


/-- Cardinality of an element centralizer as the literal finite mask count. -/
theorem elementFixed_card (g : max1Subgroup hA hB) :
    Nat.card ((Subgroup.centralizer ({g} : Set (max1Subgroup hA hB))).subgroupOf
      (localKernel hA hB)) =
    Nat.card {m : Fin 2048 // maskImage (starMasks (starProjection hA hB g)) m.val = m.val} := by
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (maskEquiv hA hB)
  intro m
  change _ ↔ (maskEquiv hA hB m : max1Subgroup hA hB) ∈ Subgroup.centralizer {g}
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_mask_iff hA hB g m).symm.trans eq_comm

/-- Simultaneous centralizers correspond to simultaneous fixed masks. -/
theorem commonFixed_card (s : Set (max1Subgroup hA hB)) :
    Nat.card ((Subgroup.centralizer s).subgroupOf (localKernel hA hB)) =
    Nat.card {m : Fin 2048 // ∀ g ∈ s,
      maskImage (starMasks (starProjection hA hB g)) m.val = m.val} := by
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (maskEquiv hA hB)
  intro m
  change _ ↔ ∀ g ∈ s, g * (maskEquiv hA hB m : max1Subgroup hA hB) =
    (maskEquiv hA hB m : max1Subgroup hA hB) * g
  exact forall₂_congr (fun g _ => (commute_mask_iff hA hB g m).symm)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.LiteralBinary
