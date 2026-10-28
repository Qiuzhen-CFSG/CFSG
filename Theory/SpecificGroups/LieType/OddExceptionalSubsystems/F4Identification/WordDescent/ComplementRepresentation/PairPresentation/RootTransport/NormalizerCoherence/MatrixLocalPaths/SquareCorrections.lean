module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths
public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.AlgebraicGroup.RootSystems.GeckDiagramAction
public import Theory.AlgebraicGroup.RootSystems.WeylGroupCoxeterPresentation

/-! Concrete Tits word corrections for the F4 matrix cover.

The simple Tits squares are literal diagonal coroot matrices. Their conjugates
are again products of simple squares by the integral grading transport formula.
Relative normality therefore passes to the quotient of the concrete Tits
normalizer by the square subgroup. Coxeter deletion in that quotient compares
any two words with equal Weyl product, and finiteness converts subgroup
membership back to a positive list of squares.

Source: GLS3, Theorem 2.9.3, `refs/KGroup/GLS3/chapter2.tex`, lines 1429--1441.
-/

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
private abbrev P := typeF4RootPairing
private abbrev b := typeF4RootPairing_base
private abbrev Idx := b.support ⊕ typeF4Roots

private lemma sign_formula {F : Type*} [Field F] (i : b.support) (j : typeF4Roots) :
    (-1 : F) ^ P.chainBotCoeff i j *
      (-1 : F) ^ P.chainBotCoeff i (P.reflectionPerm i j) =
        (-1 : F) ^ (-P.pairingIn ℤ j i) := by
  have href : P.chainBotCoeff i (P.reflectionPerm i j) = P.chainTopCoeff i j := by
    simpa using (diagram_chainBotCoeff (RootPairing.Equiv.reflection P i)
      i (P.reflectionPerm i j)).symm
  rw [href]
  by_cases h : LinearIndependent ℝ ![P.root i, P.root j]
  · rw [← P.chainTopCoeff_sub_chainBotCoeff h]
    rw [zpow_sub₀ (neg_ne_zero.mpr one_ne_zero), zpow_natCast, zpow_natCast]
    simp [div_eq_mul_inv, ← inv_pow, mul_comm]
  · rw [P.chainBotCoeff_of_not_linearIndependent h,
      P.chainTopCoeff_of_not_linearIndependent h]
    obtain he | he := RootPairing.IsReduced.eq_or_eq_neg (P := P) j i (by
      simpa only [LinearIndependent.pair_symm_iff] using h)
    · have hi : j = i := P.root.injective he
      subst j
      simp
    · let := P.indexNeg
      have hi : j = -(i : typeF4Roots) := P.root.injective (by
        simpa only [P.root_reflectionPerm, P.reflection_apply_self,
          P.indexNeg_neg] using he)
      subst j
      simp

private lemma cancellation_torus {F : Type*} [Field F] (i : b.support) :
    specializeMatrix (S := F) (titsLift i * titsLift i) =
      (integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ))).val := by
  have heval (a : b.support ⊕ typeF4Roots) :
      (chevalleyBasisTorusUnit (P := P)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) a : F) =
        (-1 : F) ^ (-chevalleyBasisWeight (P := P) a i) := by
    simp [chevalleyBasisTorusUnit, integralChevalleySimpleCorootParameter]
  ext x y
  change specializeMatrix (titsLift i * titsLift i) x y = Matrix.diagonal _ x y
  rw [Matrix.diagonal_apply]
  cases y with
  | inl j =>
    have hc : (titsLift i * titsLift i) *ᵥ u j = u j := by
      rw [← Matrix.mulVec_mulVec, titsLift_mulVec_u, Matrix.mulVec_sub,
        Matrix.mulVec_smul, titsLift_mulVec_u, titsLift_mulVec_u]
      have hii : |b.cartanMatrix i i| = 2 := by simp
      rw [hii]
      module
    have h := congrArg (Int.castRingHom F) (congrFun hc x)
    by_cases hx : x = Sum.inl j
    · subst x
      simpa [specializeMatrix, u, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight] using h
    · simpa [specializeMatrix, u, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, hx, Ne.symm hx] using h
  | inr j =>
    have hr : (titsLift i * titsLift i) *ᵥ v (b := b) j =
        ((-1 : ℤ) ^ P.chainBotCoeff i j *
          (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)) •
          v (b := b) j := by
      let := P.indexNeg
      rw [← Matrix.mulVec_mulVec, titsLift_mulVec_v, Matrix.mulVec_smul,
        titsLift_mulVec_v, P.reflectionPerm_self, smul_smul]
    have h := congrArg (Int.castRingHom F) (congrFun hr x)
    by_cases hx : x = Sum.inr j
    · subst x
      simpa [specializeMatrix, v, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, sign_formula] using h
    · simpa [specializeMatrix, v, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, hx, Ne.symm hx] using h

private def corootDiagonal (F : Type*) [Field F] (r : typeF4Roots) (t : Fˣ) :
    (Matrix Idx Idx F)ˣ where
  val := Matrix.diagonal fun a => (t ^ chevalleyBasisWeight (P := P) a r : Fˣ)
  inv := Matrix.diagonal fun a => ((t ^ chevalleyBasisWeight (P := P) a r)⁻¹ : Fˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Idx => (1 : F))
    · apply congrArg Matrix.diagonal
      funext a
      exact (t ^ chevalleyBasisWeight (P := P) a r).val_inv
    · exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    trans Matrix.diagonal (fun _ : Idx => (1 : F))
    · apply congrArg Matrix.diagonal
      funext a
      exact (t ^ chevalleyBasisWeight (P := P) a r).inv_val
    · exact Matrix.diagonal_one

private lemma corootDiagonal_simple (F : Type*) [Field F]
    (i : b.support) (t : Fˣ) :
    corootDiagonal F (i : typeF4Roots) t =
      integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i t⁻¹) := by
  apply Units.ext
  apply congrArg Matrix.diagonal
  funext a
  congr 1
  cases a with
  | inl q => simp [chevalleyBasisTorusUnit,
      integralChevalleySimpleCorootParameter]
  | inr q => simp [chevalleyBasisTorusUnit,
      integralChevalleySimpleCorootParameter]

private lemma corootDiagonal_mul (F : Type*) [Field F]
    (r : typeF4Roots) (t u : Fˣ) :
    corootDiagonal F r (t * u) = corootDiagonal F r t * corootDiagonal F r u := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  simp only [Units.val_mul, mul_zpow]

private lemma corootDiagonal_transport (F : Type*) [Field F]
    (A : (Matrix Idx Idx F)ˣ) (B : Matrix (b.support ⊕ typeF4Roots)
      (b.support ⊕ typeF4Roots) ℤ) (σ : typeF4Roots → typeF4Roots)
    (hA : A.val = specializeMatrix B)
    (hB : RespectsChevalleyGrading (P := P) B σ)
    (r : typeF4Roots) (t : Fˣ) :
    A * corootDiagonal F (σ r) t * A⁻¹ = corootDiagonal F r t := by
  apply (mul_right_cancel_iff (a := A)).mp
  rw [inv_mul_cancel_right]
  apply Units.ext
  change A.val * Matrix.diagonal _ = Matrix.diagonal _ * A.val
  rw [hA]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : B row col = 0
  · simp [specializeMatrix, hz]
  · rw [hB row col hz r]
    exact mul_comm _ _

private lemma corootDiagonal_word (F : Type*) [Field F]
    (word : List b.support) (r : typeF4Roots) (t : Fˣ) :
    rootCurveTitsWord (P := P) (S := F) word * corootDiagonal F r t *
      (rootCurveTitsWord (P := P) (S := F) word)⁻¹ =
      corootDiagonal F (reflectionWord (P := P) word r) t := by
  have h := corootDiagonal_transport F
    (rootCurveTitsWord (P := P) (S := F) word)
    (titsWord (P := P) word) (inverseReflectionWord (P := P) word) rfl
    (titsWord_respectsChevalleyGrading word) (reflectionWord (P := P) word r) t
  simpa only [inverseReflectionWord_right_inverse] using h

private lemma cancellation_torus_unit (F : Type*) [Field F]
    (i : b.support) :
    (titsEvaluation F [i, i]).val =
      (corootDiagonal F (i : typeF4Roots) (-1 : Fˣ)).val := by
  change (coverEvaluation F (transportTitsWord F [i, i])).val.val = _
  rw [coverEvaluation_transportTitsWord]
  change specializeMatrix (S := F) (titsWord (P := P) [i, i]) = _
  rw [show titsWord (P := P) [i, i] = titsLift i * titsLift i by simp [titsWord]]
  rw [cancellation_torus]
  simpa using congrArg Units.val (corootDiagonal_simple F i (-1 : Fˣ)).symm

private lemma weight_neg (a : Idx) (r : typeF4Roots) :
    chevalleyBasisWeight (P := P) a (-r) =
      -chevalleyBasisWeight (P := P) a r := by
  cases a with
  | inl i => simp [chevalleyBasisWeight]
  | inr s => exact P.pairingIn_reflectionPerm_self_right ℤ s r

private lemma weight_reflect (a : Idx) (r s : typeF4Roots) :
    chevalleyBasisWeight (P := P) a (P.reflectionPerm s r) =
      chevalleyBasisWeight (P := P) a r -
        P.pairingIn ℤ s r * chevalleyBasisWeight (P := P) a s := by
  cases a with
  | inl i => simp [chevalleyBasisWeight]
  | inr k =>
    change P.pairingIn ℤ k (P.reflectionPerm s r) = _
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    simp only [map_sub, map_mul, RootPairing.algebraMap_pairingIn,
      chevalleyBasisWeight]
    simp only [← P.root_coroot_eq_pairing, P.coroot_reflectionPerm,
      P.coreflection_apply_coroot, map_sub, map_smul, smul_eq_mul]

private lemma corootDiagonal_neg (F : Type*) [Field F]
    (r : typeF4Roots) (t : Fˣ) :
    corootDiagonal F (-r) t = corootDiagonal F r t⁻¹ := by
  apply Units.ext
  apply congrArg Matrix.diagonal
  funext a
  rw [weight_neg, zpow_neg, inv_zpow]

private lemma corootDiagonal_reflect (F : Type*) [Field F]
    (r s : typeF4Roots) (t : Fˣ) :
    corootDiagonal F (P.reflectionPerm s r) t =
      corootDiagonal F r t *
        corootDiagonal F s (t ^ (-P.pairingIn ℤ s r)) := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  simp only [weight_reflect, zpow_sub, zpow_mul, zpow_neg, Units.val_mul,
    inv_zpow]

private def corootDiagonalHom (F : Type*) [Field F] (r : typeF4Roots) :
    Fˣ →* (Matrix Idx Idx F)ˣ where
  toFun := corootDiagonal F r
  map_one' := by
    apply Units.ext
    ext a b
    simp [corootDiagonal]
  map_mul' := corootDiagonal_mul F r

private lemma corootDiagonal_zpow (F : Type*) [Field F]
    (r : typeF4Roots) (t : Fˣ) (n : ℤ) :
    corootDiagonal F r (t ^ n) = (corootDiagonal F r t) ^ n := by
  exact MonoidHom.map_zpow (corootDiagonalHom F r) t n

private def diagonalSubgroup (F : Type*) [Field F] :
    Subgroup (Matrix Idx Idx F)ˣ :=
  Subgroup.closure (Set.range fun i : b.support =>
    corootDiagonal F (i : typeF4Roots) (-1 : Fˣ))

private lemma corootDiagonal_mem_diagonalSubgroup
    (F : Type*) [Field F] [Finite F] (r : typeF4Roots) :
    corootDiagonal F r (-1 : Fˣ) ∈ diagonalSubgroup F := by
  apply b.induction_reflect r
  · intro i hi
    have hneg : P.reflectionPerm i i = -i := P.root.injective (by
      rw [P.root_reflectionPerm]
      simp)
    rw [hneg]
    rw [corootDiagonal_neg]
    simpa using hi
  · intro i hi
    let j : Fin 4 := typeF4RootPairing_baseEquiv.symm ⟨i, hi⟩
    have hj : (sourceIndex j : typeF4Roots) = i := congrArg Subtype.val
      (typeF4RootPairing_baseEquiv.apply_symm_apply ⟨i, hi⟩)
    rw [← hj]
    exact Subgroup.subset_closure ⟨sourceIndex j, rfl⟩
  · intro i j hi hj
    rw [corootDiagonal_reflect]
    apply Subgroup.mul_mem _ (hi)
    rw [corootDiagonal_zpow]
    let k : Fin 4 := typeF4RootPairing_baseEquiv.symm ⟨j, hj⟩
    have hk : (sourceIndex k : typeF4Roots) = j := congrArg Subtype.val
      (typeF4RootPairing_baseEquiv.apply_symm_apply ⟨j, hj⟩)
    rw [← hk]
    exact (diagonalSubgroup F).zpow_mem
      (Subgroup.subset_closure ⟨sourceIndex k, rfl⟩) _

private lemma diagonalSubgroup_exists_word
    (F : Type*) [Field F] [Finite F] {x : (Matrix Idx Idx F)ˣ}
    (hx : x ∈ diagonalSubgroup F) :
    ∃ d : List b.support, x = (d.map (fun q =>
      corootDiagonal F (q : typeF4Roots) (-1 : Fˣ))).prod := by
  have hm : x ∈ Submonoid.closure (Set.range fun i : b.support =>
      corootDiagonal F (i : typeF4Roots) (-1 : Fˣ)) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  clear hx
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], by simp⟩
  | one => exact ⟨[], by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨v, hv⟩ := ihx
    obtain ⟨w, hw⟩ := ihy
    refine ⟨v ++ w, ?_⟩
    simp [hv, hw, List.prod_append]


private def squareSubgroup (F : Type*) [Field F] : Subgroup (Cover F) :=
  Subgroup.closure (Set.range fun i : b.support => titsEvaluation F [i, i])

private lemma cover_square_word_mem (F : Type*) [Field F]
    (d : List b.support) :
    titsEvaluation F (squareWord d) ∈ squareSubgroup F := by
  induction d with
  | nil => simp [squareWord]
  | cons i d ih =>
    rw [squareWord_cons, titsEvaluation_append]
    exact (squareSubgroup F).mul_mem
      (Subgroup.subset_closure ⟨i, rfl⟩) ih

private lemma cover_square_word_eval (F : Type*) [Field F]
    (d : List b.support) :
    (titsEvaluation F (squareWord d)).val =
      (d.map (fun q => corootDiagonal F (q : typeF4Roots) (-1 : Fˣ))).prod.val := by
  induction d with
  | nil => simp [squareWord]
  | cons i d ih =>
    rw [squareWord_cons, titsEvaluation_append]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [cancellation_torus_unit, ih]
    simp

private lemma exists_cover_square_word (F : Type*) [Field F] [Finite F]
    (r : typeF4Roots) :
    ∃ d : List b.support,
      (titsEvaluation F (squareWord d)).val =
        (corootDiagonal F r (-1 : Fˣ)).val := by
  obtain ⟨d, hd⟩ := diagonalSubgroup_exists_word F
    (corootDiagonal_mem_diagonalSubgroup F r)
  refine ⟨d, ?_⟩
  rw [cover_square_word_eval]
  exact congrArg Units.val hd.symm

private lemma titsEvaluation_val_rootCurve (F : Type*) [Field F]
    (w : List b.support) :
    (titsEvaluation F w).val =
      (rootCurveTitsWord (P := P) (S := F) w).val := by
  change (coverEvaluation F (transportTitsWord F w)).val.val = _
  rw [coverEvaluation_transportTitsWord]


private lemma square_conjugate_mem (F : Type*) [Field F] [Finite F]
    (i j : b.support) :
    titsEvaluation F [i] * titsEvaluation F [j, j] *
        (titsEvaluation F [i])⁻¹ ∈ squareSubgroup F := by
  let r : typeF4Roots := (j : typeF4Roots)
  let rr : typeF4Roots := P.reflectionPerm (i : typeF4Roots) r
  obtain ⟨d, hd⟩ := exists_cover_square_word F rr
  have hs : rootCurveTitsWord (P := P) (S := F) [j, j] =
      corootDiagonal F (j : typeF4Roots) (-1 : Fˣ) := by
    apply Units.ext
    rw [← titsEvaluation_val_rootCurve F [j, j]]
    exact cancellation_torus_unit F j
  have he : titsEvaluation F [i] * titsEvaluation F [j, j] *
        (titsEvaluation F [i])⁻¹ = titsEvaluation F (squareWord d) := by
    apply Subtype.ext
    change (titsEvaluation F [i]).val * (titsEvaluation F [j, j]).val *
      ((titsEvaluation F [i]).val)⁻¹ =
      (titsEvaluation F (squareWord d)).val
    change (coverEvaluation F (transportTitsWord F [i])).val *
      (coverEvaluation F (transportTitsWord F [j, j])).val *
      ((coverEvaluation F (transportTitsWord F [i])).val)⁻¹ =
      (coverEvaluation F (transportTitsWord F (squareWord d))).val
    rw [coverEvaluation_transportTitsWord,
      coverEvaluation_transportTitsWord,
      coverEvaluation_transportTitsWord]
    rw [hs, corootDiagonal_word]
    rw [show reflectionWord (P := P) [i] r = rr by simp [reflectionWord, rr]]
    apply Units.ext
    rw [← titsEvaluation_val_rootCurve F (squareWord d)]
    exact hd.symm
  rw [he]
  exact cover_square_word_mem F d

private theorem squareSubgroup_le_normalizer (F : Type*) [Field F] :
    squareSubgroup F ≤ coverTransportNormalizer F := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact coverEvaluation_transportTitsWord_mem_normalizer F [i, i]

private theorem eval_eq_of_integral (F : Type*) [Field F]
    (w v : List Node) (h : titsWord (P := P) w = titsWord v) :
    titsEvaluation F w = titsEvaluation F v := by
  apply Subtype.ext
  change (coverEvaluation F (transportTitsWord F w)).val =
    (coverEvaluation F (transportTitsWord F v)).val
  rw [coverEvaluation_transportTitsWord, coverEvaluation_transportTitsWord]
  apply Units.ext
  change specializeMatrix (S := F) (titsWord w) = specializeMatrix (S := F) (titsWord v)
  rw [h]

private theorem eval_cons (F : Type*) [Field F] (i : Node) (w : List Node) :
    titsEvaluation F (i :: w) = titsEvaluation F [i] * titsEvaluation F w :=
  titsEvaluation_append F [i] w

private theorem generator_pow_four (F : Type*) [Field F] (i : Node) :
    titsEvaluation F [i] ^ 4 = 1 := by
  have hc : titsLift i * titsLift i = titsCancellation i := by
    simpa only [List.nil_append, titsWord, Matrix.one_mul, Matrix.mul_one] using
      titsWord_insert_cancellation [] [] i
  have hm : titsWord (P := P) [i, i, i, i] = titsWord [] := by
    simpa only [← hc, titsWord, Matrix.mul_one, Matrix.mul_assoc] using
      titsCancellation_mul_self i
  have h := eval_eq_of_integral F _ _ hm
  have h' : titsEvaluation F [i, i, i, i] =
      titsEvaluation F [i] * titsEvaluation F [i] *
        titsEvaluation F [i] * titsEvaluation F [i] := by
    rw [show [i, i, i, i] = [i] ++ [i] ++ [i] ++ [i] from rfl,
      titsEvaluation_append, titsEvaluation_append, titsEvaluation_append]
  calc
    titsEvaluation F [i] ^ 4 =
        titsEvaluation F [i] * titsEvaluation F [i] *
          titsEvaluation F [i] * titsEvaluation F [i] := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = titsEvaluation F [i, i, i, i] := h'.symm
    _ = titsEvaluation F [] := h
    _ = 1 := titsEvaluation_nil F

private theorem squareSubgroup_normalized (F : Type*) [Field F] [Finite F] :
    coverTransportNormalizer F ≤ Subgroup.normalizer (squareSubgroup F : Set (Cover F)) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change titsEvaluation F [i] ∈ Subgroup.normalizer (squareSubgroup F : Set (Cover F))
  have hforward : ∀ x ∈ squareSubgroup F,
      titsEvaluation F [i] * x * (titsEvaluation F [i])⁻¹ ∈ squareSubgroup F := by
    intro x hx
    have hle : squareSubgroup F ≤ (squareSubgroup F).comap
        (MulAut.conj (titsEvaluation F [i])).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact square_conjugate_mem F i j
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h := hforward _ (hforward _ (hforward _ hx))
    have he : titsEvaluation F [i] *
        (titsEvaluation F [i] *
          (titsEvaluation F [i] * (titsEvaluation F [i] * x * (titsEvaluation F [i])⁻¹) *
            (titsEvaluation F [i])⁻¹) * (titsEvaluation F [i])⁻¹) *
              (titsEvaluation F [i])⁻¹ = x := by
      calc
        _ = (titsEvaluation F [i] ^ 4) * x * (titsEvaluation F [i] ^ 4)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        _ = x := by rw [generator_pow_four]; simp
    exact he ▸ h

set_option maxHeartbeats 800000 in
private theorem quotient_eval_eq (F : Type*) [Field F] [Finite F]
    (w v : List Node) (hwv : b.wordProd w = b.wordProd v) :
    titsEvaluation F w * (titsEvaluation F v)⁻¹ ∈ squareSubgroup F := by
  let N := coverTransportNormalizer F
  let H := (squareSubgroup F).subgroupOf N
  let : H.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (squareSubgroup_le_normalizer F)).mpr (squareSubgroup_normalized F)
  let q := QuotientGroup.mk' H
  let l : List Node → N := fun z =>
    ⟨titsEvaluation F z, coverEvaluation_transportTitsWord_mem_normalizer F z⟩
  have happ (a c) : l (a ++ c) = l a * l c :=
    Subtype.ext (titsEvaluation_append F a c)
  have qapp (a c) : q (l (a ++ c)) = q (l a) * q (l c) := by
    rw [happ, map_mul]
  have hnil : l [] = 1 := Subtype.ext (titsEvaluation_nil F)
  have hsq (i) : q (l [i, i]) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨C, cs, hC, hs⟩ := b.weylGroup_coxeterPresentation
  have hstep {a c} (hm : Theory.AlgebraicGroup.CoxeterMove C a c) :
      q (l a) = q (l c) := by
    rcases hm with ⟨a, c, i, rfl, rfl⟩ | ⟨a, c, i, j, rfl, rfl⟩
    · simp only [happ, map_mul, hsq, mul_one]
    · have he : l (CoxeterSystem.braidWord C i j) =
          l (CoxeterSystem.braidWord C j i) :=
        Subtype.ext (eval_eq_of_integral F _ _ (titsWord_braidWord_eq_of_orders C hC i j))
      simp only [happ, map_mul, he]
  have hpath {a c} (hp : Relation.ReflTransGen (Theory.AlgebraicGroup.CoxeterMove C) a c) :
      q (l a) = q (l c) := by
    induction hp with
    | refl => rfl
    | tail hp hm ih => exact ih.trans (hstep hm)
  have hrev (z : List Node) : q (l z.reverse) = (q (l z))⁻¹ := by
    have hgi (i : Node) : q (l [i]) = (q (l [i]))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa only [show [i, i] = [i] ++ [i] from rfl, qapp] using hsq i
    induction z with
    | nil => simp only [List.reverse_nil, hnil, map_one, inv_one]
    | cons i z ih =>
      calc
        q (l (List.reverse (i :: z))) = q (l z.reverse) * q (l [i]) := by
          rw [List.reverse_cons, qapp]
        _ = (q (l z))⁻¹ * q (l [i]) :=
          congrArg (fun x => x * q (l [i])) ih
        _ = (q (l z))⁻¹ * (q (l [i]))⁻¹ :=
          congrArg (fun x => (q (l z))⁻¹ * x) (hgi i)
        _ = (q (l [i]) * q (l z))⁻¹ := by
          exact (mul_inv_rev (q (l [i])) (q (l z))).symm
        _ = (q (l (i :: z)))⁻¹ := by
          exact congrArg Inv.inv (qapp [i] z).symm
  have hwp : b.wordProd (w ++ v.reverse) = 1 := by
    rw [b.wordProd_append, b.wordProd_reverse, hwv, mul_inv_cancel]
  have hp := b.wordProd_one_reflTransGen_nil C hC (w ++ v.reverse) hwp
  have hk : q (l w * (l v)⁻¹) = 1 := by
    have he := hpath hp
    have he1 : q (l w) * q (l v.reverse) = 1 := by
      calc
        q (l w) * q (l v.reverse) = q (l (w ++ v.reverse)) :=
          (qapp w v.reverse).symm
        _ = q (l []) := he
        _ = 1 := (congrArg q hnil).trans (map_one q)
    have he2 : q (l w) * (q (l v))⁻¹ = 1 := by
      calc
        q (l w) * (q (l v))⁻¹ = q (l w) * q (l v.reverse) :=
          congrArg (fun x => q (l w) * x) (hrev v).symm
        _ = 1 := he1
    calc
      q (l w * (l v)⁻¹) = q (l w) * (q (l v))⁻¹ := by
        exact map_mul q _ _ |>.trans (congrArg (fun x => q (l w) * x) (map_inv q (l v)))
      _ = 1 := he2
  exact (QuotientGroup.eq_one_iff (l w * (l v)⁻¹)).mp hk

private theorem squareSubgroup_exists_word (F : Type*) [Field F] [Finite F]
    {x : Cover F} (hx : x ∈ squareSubgroup F) :
    ∃ d : List Node, titsEvaluation F (squareWord d) = x := by
  have hm : x ∈ Submonoid.closure (Set.range fun i : Node => titsEvaluation F [i, i]) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  clear hx
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], rfl⟩
  | one => exact ⟨[], titsEvaluation_nil F⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := ihx
    obtain ⟨c, rfl⟩ := ihy
    exact ⟨a ++ c, by rw [squareWord, List.flatMap_append, titsEvaluation_append]; rfl⟩

private theorem hasSquareCorrections_core (F : Type*) [Field F] [Finite F] : HasSquareCorrections F := by
  intro w v hwv
  obtain ⟨d, hd⟩ := squareSubgroup_exists_word F (quotient_eval_eq F w v hwv)
  refine ⟨d, ?_⟩
  rw [hd, inv_mul_cancel_right]

theorem hasSquareCorrections (F : Type*) [Field F] [Finite F]
    (_h2 : (2 : F) ≠ 0) : HasSquareCorrections F :=
  hasSquareCorrections_core F

theorem hasSquareCorrections_of_two_ne_zero (F : Type*) [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) : HasSquareCorrections F :=
  hasSquareCorrections F h2

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths
