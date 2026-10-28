module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.RankOneTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.StructuralCommutation
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Orthogonal rank-one groups and source Cartan actions

Upper and lower transvections generate each full rank-one image, also over
F₂. The structural positive commutations and orthogonal Weyl stabilizers
therefore imply centralization of the positive orthogonal root groups.
The longest word preserves each rank-one image and interchanges root signs;
this gives the negative centralizations and all three commuting rank-one
pairs of Fong--Seitz II (9.25).

The literal diagonal matrices give the simple-root Cartan characters and
their inverses on negative roots. The orthogonal centralizations give the
two trivial characters, retaining the Frobenius shift on the third short
root. All parameters use the same source field and its actual fixed field.
The remaining mixed characters and cross-Weyl torus equations are still
source reconstruction obligations, as are the compatible rank-one pinnings.

Source: Fong--Seitz II §7, (9.25), (9.31), printed pp.218--219.
The source table uses right conjugation; the equations here use left
conjugation, hence inverse characters. No restriction q>2 is imposed.
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y]
  {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

private theorem sl2_image_commute (f : SL2 F →* Y) (x : Y)
    (hU : ∀ a, Commute (f (uni a)) x) (hw : Commute (f (weyl F)) x)
    (g : SL2 F) : Commute (f g) x := by
  have he : (MulAut.conj x).toMonoidHom.comp f = f := by
    apply sl2_hom_ext_root_weyl
    · intro a
      exact (hU a).symm.mul_inv_cancel
    · exact hw.symm.mul_inv_cancel
  have hh : x * f g * x⁻¹ = f g := DFunLike.congr_fun he g
  apply Eq.symm
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    congrArg (fun y => y*x) hh

/-- Upper and lower root images generate the entire rank-one image, including
SL₂(F₂). -/
theorem sl2_range_eq_root_sup (f : SL2 F →* Y) :
    f.range = (f.comp (Matrix.SpecialLinearGroup.upperUnipotentHom F)).range ⊔
      ((MulAut.conj (f (weyl F))).toMonoidHom.comp
        (f.comp (Matrix.SpecialLinearGroup.upperUnipotentHom F))).range := by
  let U := f.comp (Matrix.SpecialLinearGroup.upperUnipotentHom F)
  let V := (MulAut.conj (f (weyl F))).toMonoidHom.comp U
  have hw : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right weyl_sq
  apply le_antisymm
  · rintro x ⟨g,rfl⟩
    change f g ∈ U.range ⊔ V.range
    apply Matrix.SL2.transvection_induction (fun g => f g ∈ U.range ⊔ V.range)
    · intro i j hij t
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact (show U.range ≤ U.range ⊔ V.range from le_sup_left)
          (show f (uni t) ∈ U.range from ⟨.ofAdd t,rfl⟩)
      · rw [lower_transvection_eq_weyl_uni]
        apply (show V.range ≤ U.range ⊔ V.range from le_sup_right)
        refine ⟨.ofAdd t, ?_⟩
        change f (weyl F) * f (uni t) * (f (weyl F))⁻¹ = _
        rw [← map_inv, hw, ← map_mul, ← map_mul]
      · exact (hij rfl).elim
    · intro a b ha hb
      rw [map_mul]
      exact (U.range ⊔ V.range).mul_mem ha hb
  · apply sup_le
    · rintro x ⟨t,rfl⟩
      exact ⟨Matrix.SpecialLinearGroup.upperUnipotentHom F t,rfl⟩
    · rintro x ⟨t,rfl⟩
      refine ⟨weyl F * uni t.toAdd * (weyl F)⁻¹, ?_⟩
      change f (weyl F * uni t.toAdd * (weyl F)⁻¹) =
        f (weyl F) * f (uni t.toAdd) * (f (weyl F))⁻¹
      simp only [map_mul, map_inv]

namespace RankOnePair
variable (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)

/-- The `hₐ(t)` word scales the first short source root by `t²`. -/
theorem hA_short0 (t : Fˣ) (a : F) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) * p.s 0 a *
      ((p.signedRoots e).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      p.s 0 (t.val ^ 2 * a) := by
  rw [p.hA_parameter]
  change p.shortMap (tor t) * p.shortMap (uni a) * (p.shortMap (tor t))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, Borel_conj_uni]
  · rfl
  · exact (mem_Borel_iff _).mpr (by simp [tor])

/-- The `hᵦ(u)` word scales the first long source root by `u²`. -/
theorem hB_long0 (t : Kˣ) (a : K) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) * p.l 0 a *
      ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
      p.l 0 (t.val ^ 2 * a) := by
  rw [p.hB_parameter]
  change p.longMap (tor t) * p.longMap (uni a) * (p.longMap (tor t))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, Borel_conj_uni]
  · rfl
  · exact (mem_Borel_iff _).mpr (by simp [tor])

theorem hA_negativeShort0 (t : Fˣ) (a : F) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) *
      p.dihedral.A (p.s 0 a) *
      ((p.signedRoots e).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      p.dihedral.A (p.s 0 (t.val⁻¹ ^ 2 * a)) := by
  let h := (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t)
  let hi := (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t⁻¹)
  have hconj : p.dihedral.A h = hi := by
    change p.dihedral.a * h * p.dihedral.a⁻¹ = hi
    simpa [h, hi, p.nA_one, p.dihedral.a_inv] using p.nA_hA e t
  have hconj_inv : p.dihedral.A h⁻¹ = hi⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hconj
  have hroot := p.hA_short0 e t⁻¹ a
  change h * p.dihedral.A (p.s 0 a) * h⁻¹ = _
  calc
    _ = p.dihedral.A (p.dihedral.A h * p.s 0 a * p.dihedral.A h⁻¹) := by
      rw [map_mul, map_mul, p.dihedral.A_A, p.dihedral.A_A]
    _ = p.dihedral.A (hi * p.s 0 a * hi⁻¹) := by rw [hconj, hconj_inv]
    _ = p.dihedral.A (p.s 0 (↑(t⁻¹) ^ 2 * a)) := by
      simpa [hi] using congrArg p.dihedral.A hroot
    _ = _ := by
      congr 2
      simp

theorem hB_negativeLong0 (t : Kˣ) (a : K) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) *
      p.dihedral.B (p.l 0 a) *
      ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
      p.dihedral.B (p.l 0 (t.val⁻¹ ^ 2 * a)) := by
  let h := (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t)
  let hi := (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t⁻¹)
  have hconj : p.dihedral.B h = hi := by
    change p.dihedral.b * h * p.dihedral.b⁻¹ = hi
    simpa [h, hi, p.nB_one, p.dihedral.b_inv] using p.nB_hB e t
  have hconj_inv : p.dihedral.B h⁻¹ = hi⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hconj
  have hroot := p.hB_long0 e t⁻¹ a
  change h * p.dihedral.B (p.l 0 a) * h⁻¹ = _
  calc
    _ = p.dihedral.B (p.dihedral.B h * p.l 0 a * p.dihedral.B h⁻¹) := by
      rw [map_mul, map_mul, p.dihedral.B_B, p.dihedral.B_B]
    _ = p.dihedral.B (hi * p.l 0 a * hi⁻¹) := by rw [hconj, hconj_inv]
    _ = p.dihedral.B (p.l 0 (↑(t⁻¹) ^ 2 * a)) := by
      simpa [hi] using congrArg p.dihedral.B hroot
    _ = _ := by
      congr 2
      simp

theorem shortMap_commute_long2 (c : p.PositiveCommutations) (g : SL2 F) (t : K) :
    Commute (p.shortMap g) (p.l 2 t) := by
  apply sl2_image_commute p.shortMap (p.l 2 t)
  · exact fun a => c.short0_long2 a t
  · have hh := p.orthogonalLong t
    change p.dihedral.a * p.l 2 t * p.dihedral.a⁻¹ = p.l 2 t at hh
    change p.dihedral.a * p.l 2 t = p.l 2 t * p.dihedral.a
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      congrArg (fun y => y*p.dihedral.a) hh

theorem longMap_commute_short2 (c : p.PositiveCommutations) (g : SL2 K) (t : F) :
    Commute (p.longMap g) (p.s 2 t) := by
  apply sl2_image_commute p.longMap (p.s 2 t)
  · exact fun a => c.long0_short2 a t
  · have hh := p.orthogonalShort t
    change p.dihedral.b * p.s 2 t * p.dihedral.b⁻¹ = p.s 2 t at hh
    change p.dihedral.b * p.s 2 t = p.s 2 t * p.dihedral.b
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      congrArg (fun y => y*p.dihedral.b) hh

theorem W_shortMap (g : SL2 F) :
    p.dihedral.W (p.shortMap g) = p.dihedral.A (p.shortMap g) := by
  have he : p.dihedral.W.toMonoidHom.comp p.shortMap =
      p.dihedral.A.toMonoidHom.comp p.shortMap := by
    apply sl2_hom_ext_root_weyl
    · exact p.W_shortBase
    · change p.dihedral.W p.dihedral.a = p.dihedral.A p.dihedral.a
      have hh := p.dihedral.A_longest
      change p.dihedral.a * p.dihedral.longest * p.dihedral.a⁻¹ = p.dihedral.longest at hh
      have hc : Commute p.dihedral.a p.dihedral.longest := by
        change p.dihedral.a * p.dihedral.longest = p.dihedral.longest * p.dihedral.a
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using
          congrArg (fun y => y*p.dihedral.a) hh
      change p.dihedral.longest * p.dihedral.a * p.dihedral.longest⁻¹ =
        p.dihedral.a * p.dihedral.a * p.dihedral.a⁻¹
      rw [hc.symm.mul_inv_cancel, mul_inv_cancel_right]
  exact DFunLike.congr_fun he g

theorem W_longMap (g : SL2 K) :
    p.dihedral.W (p.longMap g) = p.dihedral.B (p.longMap g) := by
  have he : p.dihedral.W.toMonoidHom.comp p.longMap =
      p.dihedral.B.toMonoidHom.comp p.longMap := by
    apply sl2_hom_ext_root_weyl
    · exact p.W_longBase
    · change p.dihedral.W p.dihedral.b = p.dihedral.B p.dihedral.b
      have hh := p.dihedral.B_longest
      change p.dihedral.b * p.dihedral.longest * p.dihedral.b⁻¹ = p.dihedral.longest at hh
      have hc : Commute p.dihedral.b p.dihedral.longest := by
        change p.dihedral.b * p.dihedral.longest = p.dihedral.longest * p.dihedral.b
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using
          congrArg (fun y => y*p.dihedral.b) hh
      change p.dihedral.longest * p.dihedral.b * p.dihedral.longest⁻¹ =
        p.dihedral.b * p.dihedral.b * p.dihedral.b⁻¹
      rw [hc.symm.mul_inv_cancel, mul_inv_cancel_right]
  exact DFunLike.congr_fun he g


theorem shortMap_commute_signedLong2 (c : p.PositiveCommutations)
    (g : SL2 F) (positive : Bool) (t : K) :
    Commute (p.shortMap g) (p.signedValue positive (p.l 2 t)) := by
  cases positive
  · have hh := (p.shortMap_commute_long2 c
        (weyl F * g * (weyl F)⁻¹) t).map p.dihedral.W.toMonoidHom
    change Commute (p.dihedral.W (p.shortMap (weyl F * g * (weyl F)⁻¹)))
      (p.dihedral.W (p.l 2 t)) at hh
    have he : p.shortMap (weyl F * g * (weyl F)⁻¹) =
        p.dihedral.A (p.shortMap g) := by simp only [map_mul, map_inv]; rfl
    rw [p.W_shortMap, he, p.dihedral.A_A] at hh
    exact hh
  · exact p.shortMap_commute_long2 c g t

theorem longMap_commute_signedShort2 (c : p.PositiveCommutations)
    (g : SL2 K) (positive : Bool) (t : F) :
    Commute (p.longMap g) (p.signedValue positive (p.s 2 t)) := by
  cases positive
  · have hh := (p.longMap_commute_short2 c
        (weyl K * g * (weyl K)⁻¹) t).map p.dihedral.W.toMonoidHom
    change Commute (p.dihedral.W (p.longMap (weyl K * g * (weyl K)⁻¹)))
      (p.dihedral.W (p.s 2 t)) at hh
    have he : p.longMap (weyl K * g * (weyl K)⁻¹) =
        p.dihedral.B (p.longMap g) := by simp only [map_mul, map_inv]; rfl
    rw [p.W_longMap, he, p.dihedral.B_B] at hh
    exact hh
  · exact p.longMap_commute_short2 c g t

/-- The two full orthogonal rank-one images commute. -/
theorem shortMap_commute_longTail (c : p.PositiveCommutations)
    (g : SL2 F) (h : SL2 K) :
    Commute (p.shortMap g) (p.dihedral.B (p.dihedral.A (p.longMap h))) := by
  let f := p.dihedral.B.toMonoidHom.comp (p.dihedral.A.toMonoidHom.comp p.longMap)
  apply Commute.symm
  change Commute (f h) (p.shortMap g)
  apply sl2_image_commute f (p.shortMap g)
  · intro a
    exact (p.shortMap_commute_long2 c g a).symm
  · have hneg : f (weyl K * uni 1 * (weyl K)⁻¹) = p.dihedral.W (p.l 2 1) := by
      change p.dihedral.B (p.dihedral.A (p.longMap (weyl K * uni 1 * (weyl K)⁻¹))) = _
      have he : p.longMap (weyl K * uni 1 * (weyl K)⁻¹) =
          p.dihedral.B (p.l 0 1) := by simp only [map_mul, map_inv]; rfl
      rw [he, ← p.W_longBase, p.dihedral.A_W, p.dihedral.B_W]
      rfl
    rw [← weyl_root_word, map_mul, map_mul, hneg]
    exact (((p.shortMap_commute_long2 c g 1).symm).mul_left
      (p.shortMap_commute_signedLong2 c g false 1).symm).mul_left
        (p.shortMap_commute_long2 c g 1).symm

theorem longMap_commute_shortTail (c : p.PositiveCommutations)
    (g : SL2 K) (h : SL2 F) :
    Commute (p.longMap g) (p.dihedral.A (p.dihedral.B (p.shortMap h))) := by
  let f := p.dihedral.A.toMonoidHom.comp (p.dihedral.B.toMonoidHom.comp p.shortMap)
  apply Commute.symm
  change Commute (f h) (p.longMap g)
  apply sl2_image_commute f (p.longMap g)
  · intro a
    exact (p.longMap_commute_short2 c g a).symm
  · have hneg : f (weyl F * uni 1 * (weyl F)⁻¹) = p.dihedral.W (p.s 2 1) := by
      change p.dihedral.A (p.dihedral.B (p.shortMap (weyl F * uni 1 * (weyl F)⁻¹))) = _
      have he : p.shortMap (weyl F * uni 1 * (weyl F)⁻¹) =
          p.dihedral.A (p.s 0 1) := by simp only [map_mul, map_inv]; rfl
      rw [he, ← p.W_shortBase, p.dihedral.B_W, p.dihedral.A_W]
      rfl
    rw [← weyl_root_word, map_mul, map_mul, hneg]
    exact (((p.longMap_commute_short2 c g 1).symm).mul_left
      (p.longMap_commute_signedShort2 c g false 1).symm).mul_left
        (p.longMap_commute_short2 c g 1).symm

/-- The middle orthogonal pair is transported by the same short Weyl element. -/
theorem shortMiddle_commute_longMiddle (c : p.PositiveCommutations)
    (g : SL2 F) (h : SL2 K) :
    Commute (p.dihedral.B (p.shortMap g)) (p.dihedral.A (p.longMap h)) := by
  have hh := ((p.longMap_commute_shortTail c h g).symm).map p.dihedral.A.toMonoidHom
  change Commute (p.dihedral.A (p.dihedral.A (p.dihedral.B (p.shortMap g))))
    (p.dihedral.A (p.longMap h)) at hh
  simpa only [p.dihedral.A_A] using hh


theorem hA_signedLong2 (c : p.PositiveCommutations) (t : Fˣ) (positive : Bool) (a : K) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) *
      (p.signedRoots e).longSigned positive 2 (e.fixed a) *
        ((p.signedRoots e).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      (p.signedRoots e).longSigned positive 2 (e.fixed a) := by
  rw [p.hA_parameter, p.signedRoots_long]
  exact (p.shortMap_commute_signedLong2 c (tor t) positive a).mul_inv_cancel

theorem hB_signedShort2 (c : p.PositiveCommutations) (t : Kˣ) (positive : Bool) (a : F) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) *
      (p.signedRoots e).shortSigned positive 2 (e.extension a) *
        ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
      (p.signedRoots e).shortSigned positive 2 (e.extension a) := by
  rw [p.hB_parameter, p.signedRoots_short, p.markedShort_two]
  exact (p.longMap_commute_signedShort2 c (tor t) positive (σ a)).mul_inv_cancel

theorem hA_signedShort0 (t : Fˣ) (positive : Bool) (a : F) :
    (p.signedRoots e).hA (Units.map e.extension.toMonoidHom t) *
      (p.signedRoots e).shortSigned positive 0 (e.extension a) *
        ((p.signedRoots e).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      (p.signedRoots e).shortSigned positive 0
        (e.extension ((if positive then t.val ^ 2 else t.val⁻¹ ^ 2) * a)) := by
  rw [p.signedRoots_short, p.signedRoots_short, p.markedShort_zero, p.markedShort_zero]
  cases positive
  · simpa only [signedValue, Bool.false_eq_true, if_false, p.W_shortBase]
      using p.hA_negativeShort0 e t a
  · exact p.hA_short0 e t a

theorem hB_signedLong0 (t : Kˣ) (positive : Bool) (a : K) :
    (p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t) *
      (p.signedRoots e).longSigned positive 0 (e.fixed a) *
        ((p.signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
      (p.signedRoots e).longSigned positive 0
        (e.fixed ((if positive then t.val ^ 2 else t.val⁻¹ ^ 2) * a)) := by
  rw [p.signedRoots_long, p.signedRoots_long]
  cases positive
  · simpa only [signedValue, Bool.false_eq_true, if_false, p.W_longBase]
      using p.hB_negativeLong0 e t a
  · exact p.hB_long0 e t a

end RankOnePair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
