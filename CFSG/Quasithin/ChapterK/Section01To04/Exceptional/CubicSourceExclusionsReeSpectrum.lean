module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsReeWeights
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.Source
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
/-!
# The order-thirteen bound on the literal exceptional Ree factors

The short-ideal action of the binary Ree group is defined over its field of
two elements. Its order-thirteen displacement is divisible by twelve.
The existing torus count puts it between twenty and twenty-four, so all
twenty-four short-root characters move. Their independent weight vectors
give the same bound on the end-node factor. The enlarged moving-weight
pairs give twenty-four for the two larger basic weights.

The actual binary embedding, exceptional powers and short-root conjugacy
transport this to displacement at least twelve for short-root involutions.
This is the strengthened local estimate needed for the saturated cubic actor,
not a claim of the complete Ree exclusion.
Source: GM04 Lemma 8.8, internal p.57; Aschbacher--Smith K.3, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.ReeSpectrum
open Matrix
private theorem rank_map_field {K F n : Type*} [Field K] [Field F]
    [Fintype n] [DecidableEq n] (f : K →+* F) (M : Matrix n n K) :
    (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, he⟩ := M.exists_rank_normal_form
  have hVe : IsUnit (V.map f).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUe : IsUnit (U.map f).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det (V.map f) (M.map f) hVe,
    ← Matrix.rank_mul_eq_left_of_isUnit_det (U.map f) _ hUe]
  rw [← Matrix.map_mul, ← Matrix.map_mul, he]
  simp only [← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ f.map_zero f.map_one, Matrix.map_zero _ f.map_zero]
  rw [Matrix.rank_submatrix]
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
    Matrix.rank_diagonal]
  have hc : Fintype.card {i : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) //
      ((fun _ : Fin M.rank => (1 : F)) ⊕ᵥ (fun _ : Fin (Fintype.card n - M.rank) => 0)) i ≠ 0} =
      M.rank := by
    let e' : {i : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) //
        ((fun _ : Fin M.rank => (1 : F)) ⊕ᵥ (fun _ : Fin (Fintype.card n - M.rank) => 0)) i ≠ 0} ≃ Fin M.rank :=
      { toFun := fun i => match i with
          | ⟨Sum.inl j, _⟩ => j
          | ⟨Sum.inr _, h⟩ => False.elim (h rfl)
        invFun := fun j => ⟨Sum.inl j, one_ne_zero⟩
        left_inv := by
          rintro ⟨i, h⟩
          cases i with
          | inl i => rfl
          | inr i => exact (h rfl).elim
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e').trans (Fintype.card_fin _)
  exact hc

open Theory.AlgebraicGroup Representation Subgroup
open ReeF4 ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
open ReeF4.FixedSpaceEstimate.BasicInvolutions
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
open scoped Classical
noncomputable section

private def nativeMatrix (x : ReeF4.Model 0) :
    Matrix ShortIndex ShortIndex (CoefficientField 0) :=
  (matrixRepresentation 0 x : Matrix Coordinate Coordinate (CoefficientField 0)).submatrix
    Subtype.val Subtype.val

private theorem nativeMatrix_map {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (f : CoefficientField 0 →+* F) (x : ReeF4.Model 0) :
    (nativeMatrix x).map f = shortAction (Classification.splitEmbedding f (toSplitGroup 0 x)) := by
  have hm : (pointMatrix (Classification.splitEmbedding f (toSplitGroup 0 x)) :
      Matrix Coordinate Coordinate F) =
      (matrixRepresentation 0 x : Matrix Coordinate Coordinate (CoefficientField 0)).map f := by
    rw [pointMatrix_splitEmbedding, Units.coe_map, matrixRepresentation_apply, toSplitGroup_apply]
    change f.mapMatrix (x.val.val : Matrix Coordinate Coordinate (CoefficientField 0)) = _
    exact RingHom.mapMatrix_apply f _
  change _ = shortBlock (pointMatrix (Classification.splitEmbedding f (toSplitGroup 0 x)) :
    Matrix Coordinate Coordinate F)
  rw [hm]
  rfl

private def nativeAction : ReeF4.Model 0 →* Matrix ShortIndex ShortIndex (CoefficientField 0) where
  toFun := nativeMatrix
  map_one' := by
    simp only [nativeMatrix, map_one, Units.val_one]
    exact Matrix.submatrix_one _ Subtype.val_injective
  map_mul' x y := by
    let f : CoefficientField 0 →+* AlgebraicClosure (CoefficientField 0) := algebraMap _ _
    have hi : Function.Injective (f.mapMatrix : Matrix ShortIndex ShortIndex (CoefficientField 0) →+* Matrix ShortIndex ShortIndex (AlgebraicClosure (CoefficientField 0))) := by
      intro A B h
      ext i j
      exact f.injective (congrArg (fun M => M i j) h)
    apply hi
    change (nativeMatrix (x * y)).map f = (nativeMatrix x * nativeMatrix y).map f
    rw [Matrix.map_mul, nativeMatrix_map, nativeMatrix_map, nativeMatrix_map, map_mul,
      map_mul, map_mul]

private def binaryAction : ReeF4.Model 0 →* Matrix ShortIndex ShortIndex (ZMod 2) :=
  ((GaloisField.equivZmodP (p := 2)).toRingHom.mapMatrix.toMonoidHom).comp nativeAction

private def binaryRep : Representation (ZMod 2) (ReeF4.Model 0) (ShortIndex → ZMod 2) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp binaryAction

private theorem native_thirteen_div (x : ReeF4.Model 0) (hx : orderOf x = 13) :
    12 ∣ (nativeMatrix x - 1).rank := by
  have hdiv := Representation.BinaryOffender.orderOf_two_dvd_fixedCodim_of_isPGroup
    binaryRep (by decide : Nat.Prime 13) (by decide) (zpowers x)
    (IsPGroup.of_card (p := 13) (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx))
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_thirteen] at hdiv
  change 12 ∣ Module.finrank (ZMod 2)
    ((ShortIndex → ZMod 2) ⧸ invariants (binaryRep.comp (zpowers x).subtype)) at hdiv
  rw [cyclic_fixedCodim_eq_rank] at hdiv
  have he : binaryRep x - 1 = (binaryAction x - 1).mulVecLin := by
    change Matrix.toLinAlgEquiv' (binaryAction x) - 1 = _
    ext v i
    simp [Matrix.toLinAlgEquiv'_apply]
  have hr : Module.finrank (ZMod 2) (LinearMap.range (binaryRep x - 1)) =
      (binaryAction x - 1).rank :=
    congrArg (fun T : Module.End (ZMod 2) (ShortIndex → ZMod 2) =>
      Module.finrank (ZMod 2) (LinearMap.range T)) he
  rw [hr] at hdiv
  have hm : binaryAction x - 1 =
      (nativeMatrix x - 1).map (GaloisField.equivZmodP (p := 2)).toRingHom := by
    change _ = (GaloisField.equivZmodP (p := 2)).toRingHom.mapMatrix (nativeMatrix x - 1)
    simp only [RingHom.mapMatrix_apply, Matrix.map_sub _ (GaloisField.equivZmodP (p := 2)).toRingHom.map_sub,
      Matrix.map_one _ (GaloisField.equivZmodP (p := 2)).toRingHom.map_zero
        (GaloisField.equivZmodP (p := 2)).toRingHom.map_one]
    rfl
  rw [hm, rank_map_field] at hdiv
  exact hdiv

private theorem displacement_rank_conj {F G n : Type*} [Field F] [Group G]
    [Fintype n] [DecidableEq n] (ρ : G →* Matrix n n F) (c x : G) :
    (ρ (c * x * c⁻¹) - 1).rank = (ρ x - 1).rank := by
  have he : ρ (c * x * c⁻¹) - 1 = ρ c * (ρ x - 1) * ρ c⁻¹ := by
    simp only [mul_sub, sub_mul, mul_one, ← map_mul, mul_inv_cancel,
      map_one]
  have hc : IsUnit (ρ c).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ((Group.isUnit c).map ρ)
  have hi : IsUnit (ρ c⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ((Group.isUnit c⁻¹).map ρ)
  rw [he, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hi,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hc]

private theorem short_torus_rank_thirteen {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (f : CoefficientField 0 →+* F) (x : ReeF4.Model 0) (hx : orderOf x = 13)
    (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ)
    (he : Classification.splitEmbedding f (toSplitGroup 0 x) =
      c * corootTorusElement t * c⁻¹) :
    (shortAction (corootTorusElement t) - 1).rank = 24 := by
  have heq : (shortAction (corootTorusElement t) - 1).rank = (nativeMatrix x - 1).rank := by
    have hm : (nativeMatrix x - 1).map f =
        shortAction (Classification.splitEmbedding f (toSplitGroup 0 x)) - 1 := by
      rw [Matrix.map_sub _ f.map_sub, Matrix.map_one _ f.map_zero f.map_one,
        nativeMatrix_map]
    rw [← rank_map_field f (nativeMatrix x - 1), hm, he, displacement_rank_conj]
  have hd : 12 ∣ (shortAction (corootTorusElement t) - 1).rank := heq ▸ native_thirteen_div x hx
  have hb := TorusCoverage.Balance.balance f x (Or.inr hx) c t he
  have ho := parameter_orderOf_of_conjugate f x c t he
  have hne : t ≠ 1 := by intro ht; simp [ht, hx] at ho
  have hp : ∀ i, t i ^ 13 = 1 := by
    intro i
    have hpow := pow_orderOf_eq_one t
    rw [ho, hx] at hpow
    exact congrFun hpow i
  have hc := primeSpectrumBound F 13 (Or.inr rfl) t hne hp hb
  have hr := short_torus_rank_count t
  obtain ⟨a, ha⟩ := hd
  omega

theorem end_thirteen_displacement {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (B : AlgebraicFactor F) (hB : B.HasBasicHighestWeight (0, 1))
    (f : CoefficientField 0 →+* F) (x : ReeF4.Model 0) (hx : orderOf x = 13) :
    24 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp (toSplitGroup 0))).ρ.comp
        (zpowers x).subtype)) := by
  classical
  obtain ⟨c, t, he⟩ := TorusCoverage.placement F f x (Or.inr hx)
  rw [binary_fixedCodim_eq_torus_rank B f x c t he]
  have hr := short_torus_rank_thirteen f x hx c t he
  have hz : fixedWeightCount EndNode.endOrbitWeight t = 0 := by
    have := short_torus_rank_count t
    omega
  have hmove (i : Fin 24) : corootCharacter t (EndNode.endOrbitWeight i) ≠ 1 := by
    intro hi
    have hm : i ∈ Finset.univ.filter (fun j => corootCharacter t (EndNode.endOrbitWeight j) = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hempty := Finset.card_eq_zero.mp hz
    rw [hempty] at hm
    exact Finset.notMem_empty i hm
  have hocc (i : Fin 24) : ∃ v, ZeroAndMiddle.IsCorootWeightVector B (EndNode.endOrbitWeight i) v := by
    rw [← EndNode.endOrbitWord_spec i, EndNode.endHighestWeight_eq_basicCoefficient]
    exact highestWeight_word_occurs B (0, 1) hB (EndNode.endOrbitWord i)
  simpa only [Fintype.card_fin] using
    displacement_ge_of_weights B t EndNode.endOrbitWeight EndNode.endOrbitWeight_injective hocc hmove


theorem binary_thirteen_displacement {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic) (hdim : 26 ≤ Module.finrank F B.Space)
    (f : CoefficientField 0 →+* F) (x : ReeF4.Model 0) (hx : orderOf x = 13) :
    24 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp (toSplitGroup 0))).ρ.comp
        (zpowers x).subtype)) := by
  obtain ⟨⟨a, b⟩, hw⟩ := B.isExceptionalBasic_iff.mp hB
  fin_cases a <;> fin_cases b
  · have hd := finrank_eq_one_of_trivial B (zero_basicHighestWeight_not_isNontrivial B hw)
    omega
  · exact end_thirteen_displacement B hw f x hx
  all_goals
    obtain ⟨c, t, he, ht⟩ := binaryOddTorusCoverage f x (Or.inr hx)
    rw [binary_fixedCodim_eq_torus_rank B f x c t he]
  · exact middle_torus_displacement_twenty_four B 0 hw t ht.ne_one
  · exact middle_torus_displacement_twenty_four B 1 hw t ht.ne_one

private theorem bound_of_thirteen_inversion {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    {m : ℕ} (f : CoefficientField m →+* F) (B : AlgebraicFactor F)
    (hB : B.IsExceptionalBasic) (hdim : 26 ≤ Module.finrank F B.Space)
    (i : ZMod (2 * m + 1)) (t : ReeF4.Model m)
    (e : CoefficientField 0 →+* CoefficientField m) (x : ReeF4.Model 0) (hx : orderOf x = 13)
    (c : ReeF4.Model m)
    (hinv : t * (c * Subfield.reeMap (by simp) e x * c⁻¹) * t⁻¹ =
      (c * Subfield.reeMap (by simp) e x * c⁻¹)⁻¹) :
    12 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp
        ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ.comp
          (zpowers t).subtype)) := by
  let j : ReeF4.Model 0 →* ReeF4.Model m := Subfield.reeMap (by simp) e
  let ρ : Representation F (ReeF4.Model m) B.Space :=
    (B.restrict ((Classification.splitEmbedding f).comp
      ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ
  have horder : orderOf (c * j x * c⁻¹) = 13 :=
    (((MulAut.conj c).orderOf_eq (j x)).trans
      (orderOf_injective j (Subfield.reeMap_injective (by simp) e) x)).trans
        hx
  have ho : Odd (orderOf (c * j x * c⁻¹)) := by rw [horder]; decide
  have hb := cyclic_fixedCodim_le_twice_of_inverts ρ t (c * j x * c⁻¹) ho hinv
  rw [cyclic_fixedCodim_conj, cyclic_fixedCodim_eq_rank] at hb
  have hr := binary_thirteen_displacement B hB hdim (f.comp e) x
    hx
  let σ : Representation F (ReeF4.Model 0) B.Space :=
    (B.restrict ((Classification.splitEmbedding (f.comp e)).comp (toSplitGroup 0))).ρ
  change 24 ≤ Module.finrank F (B.Space ⧸ invariants (σ.comp (zpowers x).subtype)) at hr
  rw [cyclic_fixedCodim_eq_rank σ x] at hr
  have he := restricted_action_binary_subfield B f e x i.val
  change ρ (j x) = _ at he
  rw [he] at hb
  change Module.finrank F (LinearMap.range (σ x - 1)) ≤
    2 * Module.finrank F (B.Space ⧸ invariants (ρ.comp (zpowers t).subtype)) at hb
  change 12 ≤ Module.finrank F (B.Space ⧸ invariants (ρ.comp (zpowers t).subtype))
  omega

private theorem short_inverts_thirteen {m : ℕ} (hm : 1 ≤ m) (t : ReeF4.Model m)
    (ht : EvenInvolutionGeometry.IsShortRootInvolution t) :
    ∃ (e : CoefficientField 0 →+* CoefficientField m) (x : ReeF4.Model 0) (c : ReeF4.Model m),
      orderOf x = 13 ∧
      t * (c * Subfield.reeMap (by simp) e x * c⁻¹) * t⁻¹ =
        (c * Subfield.reeMap (by simp) e x * c⁻¹)⁻¹ := by
  obtain ⟨e⟩ := Subfield.nonempty_coefficientHom (k := 0) (m := m) (by simp)
  obtain ⟨a, ha, hc⟩ := ht
  obtain ⟨c, hinv⟩ := InversionCoverage.mapped_conjugate_inversion
    (Subfield.reeMap (by simp) e) InversionCoverage.binaryThirteen_inverted
    (((InversionCoverage.binaryRootNormalization m hm) e a ha).2.trans hc)
  exact ⟨e, InversionCoverage.binaryThirteen, c, InversionCoverage.binaryThirteen_order, hinv⟩

theorem basic_short_involution_bound {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    {m : ℕ} (hm : 1 ≤ m) (f : CoefficientField m →+* F) (B : AlgebraicFactor F)
    (hB : B.IsExceptionalBasic) (hdim : 26 ≤ Module.finrank F B.Space)
    (i : ZMod (2 * m + 1)) (t : ReeF4.Model m)
    (ht : EvenInvolutionGeometry.IsShortRootInvolution t) :
    12 ≤ Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp
        ((exceptionalEndomorphism m ^ i.val).comp (toSplitGroup m)))).ρ.comp
          (zpowers t).subtype)) := by
  obtain ⟨e, x, c, hx, hinv⟩ := short_inverts_thirteen hm t ht
  exact bound_of_thirteen_inversion f B hB hdim i t e x hx c hinv

end

end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions.ReeSpectrum
