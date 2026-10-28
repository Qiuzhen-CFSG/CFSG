module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Groups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Literal diagonal-block quotients of the binary five-space parabolics

The natural matrix action identifies each SL₅(2) parabolic with the actual
linear subspace stabilizer. Restriction to the first k coordinates and the
explicit tail-coordinate map on the quotient give its two diagonal blocks.
The general binary block-action theorem identifies their kernel with O₂.
Thus the four source parabolics have genuine, marked quotient equivalences,
including the order of both factors in the 2+3 and 3+2 cases.

The two large-block subgroups fix the small diagonal block pointwise. Their
identification with the solvable residual is left to the residual calculation;
it is not built into their definitions.

Source: Aschbacher–Smith, Lemma 12.5.2, printed p.817/PDF p.834.
-/

@[expose] public section

open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi

/-- Compare the matrix and linear-map stabilizers through their actual natural action. -/
noncomputable def parabolicLinearEquiv (k : ℕ) :
    parabolic k ≃* BinaryLinear.parabolic (naturalFlag k) where
  toFun g := ⟨slEquivLinear 5 g.val, g.property⟩
  invFun g := ⟨(slEquivLinear 5).symm g.val, by
    intro v
    have h := g.property v
    change slEquivLinear 5 ((slEquivLinear 5).symm g.val) v ∈ naturalFlag k ↔ _
    simpa using h⟩
  left_inv g := Subtype.ext ((slEquivLinear 5).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((slEquivLinear 5).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((slEquivLinear 5).map_mul g.val h.val)

/-- Projection onto the last 5−k coordinates. -/
def naturalTail (k : ℕ) (hk : k ≤ 5) :
    (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin (5 - k) → ZMod 2) where
  toFun v j := v ⟨k + j.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem naturalTail_ker (k : ℕ) (hk : k ≤ 5) :
    (naturalTail k hk).ker = naturalFlag k := by
  ext v
  change (fun j : Fin (5-k) => v ⟨k+j.val, by omega⟩) = 0 ↔ _
  constructor
  · intro h i hi
    have he := congrFun h ⟨i.val-k, by omega⟩
    simpa [Nat.add_sub_of_le hi] using he
  · intro h
    funext j
    exact h _ (by dsimp; omega)

theorem naturalTail_surjective (k : ℕ) (hk : k ≤ 5) :
    Function.Surjective (naturalTail k hk) := by
  intro w
  refine ⟨fun i => if h : k ≤ i.val then w ⟨i.val-k, by omega⟩ else 0, ?_⟩
  funext j
  simp [naturalTail]

/-- Quotient coordinates induced by the literal tail projection. -/
noncomputable def naturalQuotientEquiv (k : ℕ) (hk : k ≤ 5) :
    ((Fin 5 → ZMod 2) ⧸ naturalFlag k) ≃ₗ[ZMod 2] (Fin (5-k) → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (naturalTail_ker k hk).symm).trans
    ((naturalTail k hk).quotKerEquivOfSurjective (naturalTail_surjective k hk))

@[simp] theorem naturalQuotientEquiv_mk (k : ℕ) (hk : k ≤ 5) (v : Fin 5 → ZMod 2) :
    naturalQuotientEquiv k hk ((naturalFlag k).mkQ v) = naturalTail k hk v := rfl

/-- The quotient by O₂, with both diagonal blocks marked in their original order. -/
noncomputable def parabolicQuotientEquiv (k : ℕ) (hk : k ≤ 5) :
    (parabolic k ⧸ pCore 2 (parabolic k)) ≃*
      SL(k, ZMod 2) × SL(5-k, ZMod 2) :=
  (QuotientGroup.congr _ _ (parabolicLinearEquiv k)
    (pCore_map_iso 2 (parabolicLinearEquiv k))).trans
    ((quotientTwoCoreEquivOfCoordinates (naturalFlag k) (naturalFlagEquiv k hk)
      (naturalQuotientEquiv k hk)).trans
      ((slEquivLinear k).symm.prodCongr (slEquivLinear (5-k)).symm))

/-- The surjective diagonal-block map on the actual matrix parabolic. -/
noncomputable def parabolicLeviHom (k : ℕ) (hk : k ≤ 5) :
    parabolic k →* SL(k, ZMod 2) × SL(5-k, ZMod 2) :=
  (parabolicQuotientEquiv k hk).toMonoidHom.comp (QuotientGroup.mk' _)

theorem parabolicLeviHom_surjective (k : ℕ) (hk : k ≤ 5) :
    Function.Surjective (parabolicLeviHom k hk) :=
  (parabolicQuotientEquiv k hk).surjective.comp (QuotientGroup.mk'_surjective _)

theorem parabolicLeviHom_ker (k : ℕ) (hk : k ≤ 5) :
    (parabolicLeviHom k hk).ker = pCore 2 (parabolic k) := by
  ext g
  change parabolicQuotientEquiv k hk (QuotientGroup.mk' _ g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

theorem parabolicLeviHom_fst_apply (k : ℕ) (hk : k ≤ 5) (g : parabolic k)
    (v : Fin k → ZMod 2) :
    (parabolicLeviHom k hk g).1.val.mulVec v =
      naturalFlagEquiv k hk (subspaceAction (naturalFlag k) (parabolicLinearEquiv k g)
        ((naturalFlagEquiv k hk).symm v)) := by
  change slEquivLinear k ((slEquivLinear k).symm _) v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem parabolicLeviHom_snd_apply (k : ℕ) (hk : k ≤ 5) (g : parabolic k)
    (v : Fin 5 → ZMod 2) :
    (parabolicLeviHom k hk g).2.val.mulVec (naturalTail k hk v) =
      naturalTail k hk (g.val.val.mulVec v) := by
  change slEquivLinear (5-k) ((slEquivLinear (5-k)).symm _)
    (naturalQuotientEquiv k hk ((naturalFlag k).mkQ v)) = _
  rw [MulEquiv.apply_symm_apply]
  change naturalQuotientEquiv k hk (quotientAction (naturalFlag k)
    (parabolicLinearEquiv k g) ((naturalQuotientEquiv k hk).symm
      (naturalQuotientEquiv k hk ((naturalFlag k).mkQ v)))) = _
  rw [LinearEquiv.symm_apply_apply, quotientAction_mk, naturalQuotientEquiv_mk]
  rfl


theorem parabolicLeviHom_fst_entry (k : ℕ) (hk : k ≤ 5) (g : parabolic k)
    (i j : Fin k) :
    (parabolicLeviHom k hk g).1.val i j = g.val.val (Fin.castLE hk i) (Fin.castLE hk j) := by
  have h := congrFun (parabolicLeviHom_fst_apply k hk g (Pi.single j 1)) i
  have he : ((naturalFlagEquiv k hk).symm (Pi.single j 1)).val =
      Pi.single (Fin.castLE hk j) 1 := by
    funext a
    change (if h : a.val < k then (Pi.single j 1 : Fin k → ZMod 2) ⟨a.val, h⟩ else 0) =
      (Pi.single (Fin.castLE hk j) 1 : Fin 5 → ZMod 2) a
    by_cases ha : a.val < k
    · simp only [dif_pos ha, Pi.single_apply]
      congr 1
      exact propext (by simp [Fin.ext_iff, eq_comm])
    · have hne : a ≠ Fin.castLE hk j := by intro h; subst a; exact ha j.isLt
      simp [ha, hne]
  change _ = (g.val.val.mulVec (((naturalFlagEquiv k hk).symm (Pi.single j 1)).val))
    (Fin.castLE hk i) at h
  simpa [he, Matrix.mulVec_single] using h

theorem parabolicLeviHom_snd_entry (k : ℕ) (hk : k ≤ 5) (g : parabolic k)
    (i j : Fin (5-k)) :
    (parabolicLeviHom k hk g).2.val i j =
      g.val.val ⟨k+i.val, by omega⟩ ⟨k+j.val, by omega⟩ := by
  have he : naturalTail k hk (Pi.single ⟨k+j.val, by omega⟩ 1) = Pi.single j 1 := by
    funext a
    simp [naturalTail, Pi.single_apply, Fin.ext_iff, eq_comm]
  have h := congrFun (parabolicLeviHom_snd_apply k hk g
    (Pi.single ⟨k+j.val, by omega⟩ 1)) i
  rw [he] at h
  simpa [Matrix.mulVec_single, naturalTail] using h

/-- The actual unipotent radical: it fixes Γ_k pointwise and acts trivially modulo Γ_k. -/
noncomputable def parabolicUnipotent (k : ℕ) : Subgroup Group :=
  (BinaryLinear.radical (naturalFlag k)).comap (slEquivLinear 5).toMonoidHom

theorem parabolic_twoCore_eq_unipotent (k : ℕ) :
    (pCore 2 (parabolic k)).map (parabolic k).subtype = parabolicUnipotent k := by
  apply Subgroup.map_injective (f := (slEquivLinear 5).toMonoidHom) (slEquivLinear 5).injective
  rw [Subgroup.map_map]
  have he : (slEquivLinear 5).toMonoidHom.comp (parabolic k).subtype =
      (BinaryLinear.parabolic (naturalFlag k)).subtype.comp
        (parabolicLinearEquiv k).toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, pCore_map_iso, map_twoCore_eq_radical]
  exact (Subgroup.map_comap_eq_self_of_surjective (slEquivLinear 5).surjective _).symm


theorem mem_parabolic_twoCore_iff (k : ℕ) (hk : k ≤ 5) (g : parabolic k) :
    g ∈ pCore 2 (parabolic k) ↔
      (∀ i j : Fin k, g.val.val (Fin.castLE hk i) (Fin.castLE hk j) =
        (1 : Matrix (Fin k) (Fin k) (ZMod 2)) i j) ∧
      (∀ i j : Fin (5-k), g.val.val ⟨k+i.val, by omega⟩ ⟨k+j.val, by omega⟩ =
        (1 : Matrix (Fin (5-k)) (Fin (5-k)) (ZMod 2)) i j) := by
  rw [← parabolicLeviHom_ker k hk]
  change parabolicLeviHom k hk g = 1 ↔ _
  constructor
  · intro h
    constructor
    · intro i j
      rw [← parabolicLeviHom_fst_entry, h]
      rfl
    · intro i j
      rw [← parabolicLeviHom_snd_entry k hk, h]
      rfl
  · rintro ⟨ha, hd⟩
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      rw [parabolicLeviHom_fst_entry]
      exact ha i j
    · apply Subtype.ext
      ext i j
      rw [parabolicLeviHom_snd_entry]
      exact hd i j

/-- The 2+3 Levi quotient in source clause (1), in coordinate-block order. -/
noncomputable def parabolicTwoQuotientEquiv :
    (parabolic 2 ⧸ pCore 2 (parabolic 2)) ≃* SL(2, ZMod 2) × SL(3, ZMod 2) :=
  parabolicQuotientEquiv 2 (by decide)

/-- The 3+2 Levi quotient in source clause (2), in coordinate-block order. -/
noncomputable def parabolicThreeQuotientEquiv :
    (parabolic 3 ⧸ pCore 2 (parabolic 3)) ≃* SL(3, ZMod 2) × SL(2, ZMod 2) :=
  parabolicQuotientEquiv 3 (by decide)

local instance : Unique SL(1, ZMod 2) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩

/-- The line-parabolic quotient, given by its last four coordinates. -/
noncomputable def parabolicOneQuotientEquiv :
    (parabolic 1 ⧸ pCore 2 (parabolic 1)) ≃* SL(4, ZMod 2) :=
  (parabolicQuotientEquiv 1 (by decide)).trans MulEquiv.uniqueProd

/-- The hyperplane-parabolic quotient, given by its first four coordinates. -/
noncomputable def parabolicFourQuotientEquiv :
    (parabolic 4 ⧸ pCore 2 (parabolic 4)) ≃* SL(4, ZMod 2) :=
  (parabolicQuotientEquiv 4 (by decide)).trans
    (show (SL(4, ZMod 2) × SL(1, ZMod 2)) ≃* SL(4, ZMod 2) from MulEquiv.prodUnique)


/-- The quotient equivalence agrees with the diagonal-block homomorphism on representatives. -/
@[simp] theorem parabolicQuotientEquiv_mk (k : ℕ) (hk : k ≤ 5) (g : parabolic k) :
    parabolicQuotientEquiv k hk (QuotientGroup.mk' _ g) = parabolicLeviHom k hk g := rfl

@[simp] theorem parabolicOneQuotientEquiv_mk (g : parabolic 1) :
    parabolicOneQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 1 (by decide) g).2 := rfl

@[simp] theorem parabolicFourQuotientEquiv_mk (g : parabolic 4) :
    parabolicFourQuotientEquiv (QuotientGroup.mk' _ g) =
      (parabolicLeviHom 4 (by decide) g).1 := rfl

/-- The small diagonal block of the two-space parabolic. -/
noncomputable def parabolicTwoSmallBlock : parabolic 2 →* SL(2, ZMod 2) :=
  (MonoidHom.fst SL(2, ZMod 2) SL(3, ZMod 2)).comp (parabolicLeviHom 2 (by decide))

/-- The small diagonal block of the three-space parabolic. -/
noncomputable def parabolicThreeSmallBlock : parabolic 3 →* SL(2, ZMod 2) :=
  (MonoidHom.snd SL(3, ZMod 2) SL(2, ZMod 2)).comp (parabolicLeviHom 3 (by decide))

/-- The subgroup with identity small block and unrestricted three-dimensional block.
Its equality with the source solvable residual is a further theorem. -/
noncomputable def parabolicTwoLargeBlock : Subgroup Group :=
  parabolicTwoSmallBlock.ker.map (parabolic 2).subtype

/-- The same subgroup in the reversed 3+2 block orientation. -/
noncomputable def parabolicThreeLargeBlock : Subgroup Group :=
  parabolicThreeSmallBlock.ker.map (parabolic 3).subtype

theorem parabolicTwoLargeBlock_le : parabolicTwoLargeBlock ≤ parabolic 2 := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem parabolicThreeLargeBlock_le : parabolicThreeLargeBlock ≤ parabolic 3 := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- The first small block is literally the first 2×2 submatrix. -/
theorem parabolicTwoSmallBlock_entry (g : parabolic 2) (i j : Fin 2) :
    (parabolicTwoSmallBlock g).val i j = g.val.val (Fin.castLE (by decide) i)
      (Fin.castLE (by decide) j) :=
  parabolicLeviHom_fst_entry 2 (by decide) g i j

/-- The second small block is literally the last 2×2 submatrix. -/
theorem parabolicThreeSmallBlock_entry (g : parabolic 3) (i j : Fin 2) :
    (parabolicThreeSmallBlock g).val i j = g.val.val ⟨3+i.val, by omega⟩
      ⟨3+j.val, by omega⟩ :=
  parabolicLeviHom_snd_entry 3 (by decide) g i j

end Representation.SL5ExteriorSquare
