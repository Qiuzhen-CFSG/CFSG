module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRankOneExchange

/-!
# The finite `G2` Tits normalizer

This module gives the twelve alternating simple-reflection words and their
finite signed multiplication table.  The table and the length-six braid are
checked on the explicit integral fourteen-dimensional representation and are
then specialized to an arbitrary field.  Closed-carrier inclusion injectivity
transfers those matrix identities to the Chevalley carrier.  Signed words are
collected inductively, and the final interface records the corresponding
split-torus conjugation action.  No root exhaustiveness, Bruhat cover,
semisimplicity, or center theorem is used.
-/

open scoped Matrix
open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public section

/-- The canonical alternating words for the twelve elements of the `G2` Weyl group. -/
public def canonicalWeylWord : Fin 12 → List (Fin 2)
  | 0 => [] | 1 => [0] | 2 => [1] | 3 => [0, 1] | 4 => [1, 0]
  | 5 => [0, 1, 0] | 6 => [1, 0, 1] | 7 => [0, 1, 0, 1]
  | 8 => [1, 0, 1, 0] | 9 => [0, 1, 0, 1, 0]
  | 10 => [1, 0, 1, 0, 1] | 11 => [0, 1, 0, 1, 0, 1]

/-- The four split-torus sign parameters used by the multiplication table. -/
public def titsSignParameter {R : Type*} [CommRing R] : Fin 4 → TorusParameter R
  | 0 => ![(-1 : Rˣ), (-1 : Rˣ)]
  | 1 => ![(-1 : Rˣ), 1]
  | 2 => ![1, (-1 : Rˣ)]
  | 3 => ![1, 1]

/-- Target index for left multiplication by a signed simple lift. -/
public def titsLeftTarget : Fin 2 → Bool → Fin 12 → Fin 12
  | 0, _, 0 => 1 | 0, _, 1 => 0 | 0, _, 2 => 3 | 0, _, 3 => 2
  | 0, _, 4 => 5 | 0, _, 5 => 4 | 0, _, 6 => 7 | 0, _, 7 => 6
  | 0, _, 8 => 9 | 0, _, 9 => 8 | 0, _, 10 => 11 | 0, _, 11 => 10
  | 1, _, 0 => 2 | 1, _, 1 => 4 | 1, _, 2 => 0 | 1, _, 3 => 6
  | 1, _, 4 => 1 | 1, _, 5 => 8 | 1, _, 6 => 3 | 1, _, 7 => 10
  | 1, _, 8 => 5 | 1, _, 9 => 11 | 1, _, 10 => 7 | 1, _, 11 => 9

/-- Torus-sign index in the finite signed multiplication table. -/
public def titsLeftSign : Fin 2 → Bool → Fin 12 → Fin 4
  | 0, false, 0 => 3 | 0, false, 1 => 1 | 0, false, 2 => 3 | 0, false, 3 => 0
  | 0, false, 4 => 3 | 0, false, 5 => 2 | 0, false, 6 => 3 | 0, false, 7 => 2
  | 0, false, 8 => 3 | 0, false, 9 => 0 | 0, false, 10 => 3 | 0, false, 11 => 1
  | 0, true, 0 => 1 | 0, true, 1 => 3 | 0, true, 2 => 0 | 0, true, 3 => 3
  | 0, true, 4 => 2 | 0, true, 5 => 3 | 0, true, 6 => 2 | 0, true, 7 => 3
  | 0, true, 8 => 0 | 0, true, 9 => 3 | 0, true, 10 => 1 | 0, true, 11 => 3
  | 1, false, 0 => 3 | 1, false, 1 => 3 | 1, false, 2 => 2 | 1, false, 3 => 3
  | 1, false, 4 => 0 | 1, false, 5 => 3 | 1, false, 6 => 1 | 1, false, 7 => 3
  | 1, false, 8 => 1 | 1, false, 9 => 3 | 1, false, 10 => 0 | 1, false, 11 => 2
  | 1, true, 0 => 2 | 1, true, 1 => 0 | 1, true, 2 => 3 | 1, true, 3 => 1
  | 1, true, 4 => 3 | 1, true, 5 => 1 | 1, true, 6 => 3 | 1, true, 7 => 0
  | 1, true, 8 => 3 | 1, true, 9 => 2 | 1, true, 10 => 3 | 1, true, 11 => 3

private def wordMatrix {R : Type*} [CommRing R] : List (Fin 2) → (Matrix Basis Basis R)ˣ
  | [] => 1
  | i :: w => weylMatrixUnit i * wordMatrix w

private def wordVal {R : Type*} [CommRing R] : List (Fin 2) → Matrix Basis Basis R
  | [] => 1
  | i :: w => specialize (R := R) (weyl i) * wordVal w

private def simpleSign : Fin 2 → Fin 4
  | 0 => 1 | 1 => 2

private def titsSignMul : Fin 4 → Fin 4 → Fin 4
  | 0, 0 => 3 | 0, 1 => 2 | 0, 2 => 1 | 0, 3 => 0
  | 1, 0 => 2 | 1, 1 => 3 | 1, 2 => 0 | 1, 3 => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 2
  | 3, b => b

private def titsSignReflect : Fin 2 → Fin 4 → Fin 4
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0 | 0, 3 => 3
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2 | 1, 3 => 3

private noncomputable def signPoint (s : Fin 4) : CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints
    ((dPointEquiv 2).symm (titsSignParameter (R := k) s))

private lemma signPoint_mul (a b : Fin 4) :
    signPoint (k := k) a * signPoint (k := k) b =
      signPoint (k := k) (titsSignMul a b) := by
  change (splitTorusMorphism (k := k)).onPoints _ *
      (splitTorusMorphism (k := k)).onPoints _ =
    (splitTorusMorphism (k := k)).onPoints _
  calc
    _ = (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm (titsSignParameter (R := k) a) *
          (dPointEquiv 2).symm (titsSignParameter (R := k) b)) :=
      ((splitTorusMorphism (k := k)).map_mul _ _).symm
    _ = _ := by
      congr 1
      apply (dPointEquiv 2).injective
      fin_cases a <;> fin_cases b <;>
        simp only [dPointEquiv_mul, Equiv.apply_symm_apply]
      all_goals funext q
      all_goals fin_cases q <;>
        simp [titsSignParameter, titsSignMul]

private lemma signPoint_one : signPoint (k := k) 3 = 1 := by
  have h : (dPointEquiv 2).symm
      (titsSignParameter (R := k) 3) =
      (1 : Variety.Point (dVariety k 2)) := by
    apply (dPointEquiv 2).symm_apply_eq.mpr
    have hv : ![(1 : kˣ), 1] = (1 : TorusParameter k) := by
      funext q
      fin_cases q <;> rfl
    exact hv.trans (dPointEquiv_one (k := k) 2).symm
  rw [signPoint, h]
  exact (splitTorusMorphism (k := k)).map_one

private lemma signParameter_reflect {R : Type*} [CommRing R] (i : Fin 2) (s : Fin 4) :
    simpleReflectionTorusParameter i (titsSignParameter (R := R) s) =
      titsSignParameter (R := R) (titsSignReflect i s) := by
  funext j
  fin_cases i <;> fin_cases s <;> fin_cases j <;>
    simp [titsSignParameter, titsSignReflect, simpleReflectionTorusParameter,
      pow_succ]

private def simpleWeylVec {R : Type*} [CommRing R]
    (i : Fin 2) (v : Basis → R) : Basis → R := fun b =>
  match i, b with
  | 0, 0 => -v 0 - v 1
  | 0, 1 => v 1
  | 0, 2 => v 8
  | 0, 3 => -v 6
  | 0, 4 => v 5
  | 0, 5 => -v 4
  | 0, 6 => v 3
  | 0, 7 => v 7
  | 0, 8 => v 2
  | 0, 9 => v 12
  | 0, 10 => -v 11
  | 0, 11 => v 10
  | 0, 12 => -v 9
  | 0, 13 => v 13
  | 1, 0 => v 0
  | 1, 1 => -3 * v 0 - v 1
  | 1, 2 => -v 4
  | 1, 3 => v 9
  | 1, 4 => v 2
  | 1, 5 => v 5
  | 1, 6 => -v 7
  | 1, 7 => v 6
  | 1, 8 => v 10
  | 1, 9 => v 3
  | 1, 10 => -v 8
  | 1, 11 => v 11
  | 1, 12 => v 13
  | 1, 13 => -v 12

private lemma weyl_mulVec {R : Type*} [CommRing R]
    (i : Fin 2) (v : Basis → R) :
    specialize (R := R) (weyl i) *ᵥ v = simpleWeylVec i v := by
  funext b
  fin_cases i <;> fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, weyl, weylEntries, matrixOfEntries, specialize,
      simpleWeylVec, Fin.sum_univ_succ] <;> ring

private def matrixWord {R : Type*} [CommRing R] :
    List (Fin 2) → Matrix Basis Basis R
  | [] => 1
  | i :: w => specialize (R := R) (weyl i) * matrixWord w

private def wordVec {R : Type*} [CommRing R] :
    List (Fin 2) → (Basis → R) → Basis → R
  | [], v => v
  | i :: w, v => simpleWeylVec i (wordVec w v)

private lemma matrixWord_wordVal {R : Type*} [CommRing R] (w : List (Fin 2)) :
    matrixWord (R := R) w = wordVal (R := R) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [matrixWord, wordVal, ih]

private lemma word_mulVec {R : Type*} [CommRing R]
    (w : List (Fin 2)) (v : Basis → R) :
    matrixWord (R := R) w *ᵥ v = wordVec w v := by
  induction w with
  | nil => simp [matrixWord, wordVec]
  | cons i w ih =>
      simp only [matrixWord, wordVec]
      rw [← Matrix.mulVec_mulVec, ih, weyl_mulVec]

private lemma wordVec_braid {R : Type*} [CommRing R] (v : Basis → R) :
    wordVec [0, 1, 0, 1, 0, 1] v = wordVec [1, 0, 1, 0, 1, 0] v := by
  funext b
  fin_cases b <;> simp [wordVec, simpleWeylVec] <;> ring

private lemma torusSign_mulVec {R : Type*} [CommRing R]
    (i : Fin 2) (v : Basis → R) :
    (torusElement (titsSignParameter (R := R) (simpleSign i))).val *ᵥ v =
      simpleWeylVec i (simpleWeylVec i v) := by
  funext b
  fin_cases i <;> fin_cases b <;>
    simp [simpleWeylVec, torusElement, titsSignParameter, simpleSign, basisTorusUnit,
      basisWeight, basisRoot, Root.pairingSimple, Root.coord, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, pow_succ]

private lemma generic_simple_square {R : Type*} [CommRing R] (i : Fin 2) :
    specialize (R := R) (weyl i) * specialize (R := R) (weyl i) =
      (torusElement (titsSignParameter (R := R) (simpleSign i))).val := by
  ext r c
  have hm :
      (specialize (R := R) (weyl i) * specialize (R := R) (weyl i)) *ᵥ
          Pi.single c 1 =
        (torusElement (titsSignParameter (R := R) (simpleSign i))).val *ᵥ
          Pi.single c 1 := by
    rw [← Matrix.mulVec_mulVec, weyl_mulVec, weyl_mulVec, torusSign_mulVec]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hm r

private theorem generic_braid {R : Type*} [CommRing R] :
    wordVal (R := R) [0, 1, 0, 1, 0, 1] =
      wordVal (R := R) [1, 0, 1, 0, 1, 0] := by
  rw [← matrixWord_wordVal, ← matrixWord_wordVal]
  ext r c
  have hm : matrixWord (R := R) [0, 1, 0, 1, 0, 1] *ᵥ Pi.single c 1 =
      matrixWord (R := R) [1, 0, 1, 0, 1, 0] *ᵥ Pi.single c 1 := by
    rw [word_mulVec, word_mulVec]
    exact wordVec_braid _
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hm r

private noncomputable def ambientPointHom :
    LinearMap.GeneralLinearGroup k (Basis → k) →* Variety.Point (Ambient k) where
  toFun g := generalLinearRepresentationPoint (carrierBasis (k := k)) g
  map_one' := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_one (carrierBasis (k := k))
  map_mul' g h := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_mul (carrierBasis (k := k)) g h

private lemma carrierWeylWord_ambient_matrix (w : List (Fin 2)) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        (carrierWeylWord (k := k) w) =
      ambientPointHom (k := k)
        (Matrix.GeneralLinearGroup.toLin (wordMatrix (R := k) w)) := by
  induction w with
  | nil => simp only [carrierWeylWord, wordMatrix, map_one]
  | cons i w ih =>
      rw [carrierWeylWord, map_mul, carrierWeylRepresentative_ambient_matrix, ih]
      change ambientPointHom _ * ambientPointHom _ = ambientPointHom _
      rw [← (ambientPointHom (k := k)).map_mul]
      congr 1
      simp [wordMatrix, map_mul]

private theorem preSimpleTorusConjugation (i : Fin 2)
    (x : Variety.Point (dVariety k 2)) :
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x *
          carrierWeylRepresentative (k := k) i =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := carrierWeylRepresentative_splitTorus_conjugation (k := k) i
    ((splitTorusIso (k := k)).hom.onPoints x)
  simp only [simpleReflectionTorusPoint] at h
  rw [(splitTorusIso (k := k)).hom_inv_id] at h
  change (carrierWeylRepresentative (k := k) i)⁻¹ *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x) *
          carrierWeylRepresentative (k := k) i =
    (splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x)))) at h
  rw [splitTorusIso_inclusion_apply, splitTorusIso_inclusion_apply] at h
  exact h

private def preReflect : List (Fin 2) → Fin 4 → Fin 4
  | [], s => s
  | i :: w, s => preReflect w (titsSignReflect i s)

private lemma preMove (i : Fin 2) (s : Fin 4) :
    signPoint (k := k) s * carrierWeylRepresentative (k := k) i =
      carrierWeylRepresentative (k := k) i *
        signPoint (k := k) (titsSignReflect i s) := by
  have h := preSimpleTorusConjugation (k := k) i
    ((dPointEquiv 2).symm (titsSignParameter (R := k) s))
  have h' : (carrierWeylRepresentative (k := k) i)⁻¹ *
      signPoint (k := k) s * carrierWeylRepresentative (k := k) i =
      signPoint (k := k) (titsSignReflect i s) := by
    simpa [signPoint, signParameter_reflect (R := k) i s] using h
  calc
    signPoint (k := k) s * carrierWeylRepresentative (k := k) i =
        carrierWeylRepresentative (k := k) i *
          ((carrierWeylRepresentative (k := k) i)⁻¹ *
            signPoint (k := k) s * carrierWeylRepresentative (k := k) i) := by group
    _ = _ := by rw [h']

private lemma preMoveWord : ∀ (w : List (Fin 2)) (s : Fin 4),
    signPoint (k := k) s * carrierWeylWord (k := k) w =
      carrierWeylWord (k := k) w * signPoint (k := k) (preReflect w s) := by
  intro w
  induction w with
  | nil => intro s; simp [carrierWeylWord, preReflect]
  | cons i w ih =>
      intro s
      fin_cases i
      · rw [Fin.zero_eta]
        simp only [carrierWeylWord, preReflect]
        rw [← mul_assoc, preMove (k := k) 0 s, mul_assoc, ih]
        simp only [mul_assoc]
      · rw [show (⟨1, by decide⟩ : Fin 2) = 1 by rfl]
        simp only [carrierWeylWord, preReflect]
        rw [← mul_assoc, preMove (k := k) 1 s, mul_assoc, ih]
        simp only [mul_assoc]

private lemma preConjugateWord (w : List (Fin 2)) (s : Fin 4) :
    (carrierWeylWord (k := k) w)⁻¹ * signPoint (k := k) s *
        carrierWeylWord (k := k) w = signPoint (k := k) (preReflect w s) := by
  have h := preMoveWord (k := k) w s
  calc
    (carrierWeylWord (k := k) w)⁻¹ * signPoint (k := k) s *
        carrierWeylWord (k := k) w =
      (carrierWeylWord (k := k) w)⁻¹ *
        (carrierWeylWord (k := k) w * signPoint (k := k) (preReflect w s)) := by
          rw [← h]
          group
    _ = _ := by group

private theorem pre_braid :
    carrierWeylWord (k := k) [0, 1, 0, 1, 0, 1] =
      carrierWeylWord (k := k) [1, 0, 1, 0, 1, 0] := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  rw [carrierWeylWord_ambient_matrix, carrierWeylWord_ambient_matrix]
  have hu : wordMatrix (R := k) [0, 1, 0, 1, 0, 1] =
      wordMatrix (R := k) [1, 0, 1, 0, 1, 0] := Units.ext generic_braid
  exact congrArg (ambientPointHom (k := k))
    (congrArg Matrix.GeneralLinearGroup.toLin hu)

private def abstractWord {G : Type*} [Group G] (W : Fin 2 → G) :
    List (Fin 2) → G
  | [] => 1
  | i :: w => W i * abstractWord W w

private lemma abstractWord_carrier (w : List (Fin 2)) :
    abstractWord (carrierWeylRepresentative (k := k)) w =
      carrierWeylWord (k := k) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [abstractWord, carrierWeylWord, ih]

private def abstractAct : List (Fin 2) → Fin 4 → Fin 4
  | [], s => s
  | i :: w, s => abstractAct w (titsSignReflect i s)

private lemma abstractMoveWord {G : Type*} [Group G]
    (W : Fin 2 → G) (P : Fin 4 → G)
    (hm0 : ∀ s, P s * W 0 = W 0 * P (titsSignReflect 0 s))
    (hm1 : ∀ s, P s * W 1 = W 1 * P (titsSignReflect 1 s)) :
    ∀ (w : List (Fin 2)) (s : Fin 4),
      P s * abstractWord W w =
        abstractWord W w * P (abstractAct w s) := by
  intro w
  induction w with
  | nil => intro s; simp [abstractWord, abstractAct]
  | cons i w ih =>
      intro s
      fin_cases i
      · rw [Fin.zero_eta]
        simp only [abstractWord, abstractAct]
        rw [← mul_assoc, hm0 s, mul_assoc, ih]
        simp only [mul_assoc]
      · rw [show (⟨1, by decide⟩ : Fin 2) = 1 by rfl]
        simp only [abstractWord, abstractAct]
        rw [← mul_assoc, hm1 s, mul_assoc, ih]
        simp only [mul_assoc]

set_option linter.unusedSimpArgs false in
private theorem abstractPositive {G : Type*} [Group G]
    (W : Fin 2 → G) (P : Fin 4 → G)
    (h0 : W 0 * W 0 = P 1) (h1 : W 1 * W 1 = P 2)
    (h3 : P 3 = 1)
    (hm0 : ∀ s, P s * W 0 = W 0 * P (titsSignReflect 0 s))
    (hm1 : ∀ s, P s * W 1 = W 1 * P (titsSignReflect 1 s))
    (hb : W 0 * W 1 * W 0 * W 1 * W 0 * W 1 =
      W 1 * W 0 * W 1 * W 0 * W 1 * W 0)
    (i : Fin 2) (j : Fin 12) :
    W i * abstractWord W (canonicalWeylWord j) =
      abstractWord W (canonicalWeylWord (titsLeftTarget i false j)) *
        P (titsLeftSign i false j) := by
  have hm00 := hm0 0; have hm01 := hm0 1; have hm02 := hm0 2; have hm03 := hm0 3
  have hm10 := hm1 0; have hm11 := hm1 1; have hm12 := hm1 2; have hm13 := hm1 3
  have hmv := abstractMoveWord W P hm0 hm1
  fin_cases i <;> fin_cases j <;>
    simp [abstractWord, canonicalWeylWord, titsLeftTarget, titsLeftSign,
      titsSignReflect, abstractAct, h0, h1, h3, hm00, hm01, hm02, hm03,
      hm10, hm11, hm12, hm13, hb]
  all_goals try simp only [← mul_assoc]
  all_goals try simp [titsSignReflect, abstractAct, h0, h1, h3, hm00, hm01, hm02, hm03,
    hm10, hm11, hm12, hm13, hmv, hb]
  all_goals try simp only [mul_assoc]
  all_goals try simp [titsSignReflect, abstractAct, hmv, h0, h1, h3, hm00, hm10, hb]
  case «0».«7» =>
    simpa [abstractWord, abstractAct, titsSignReflect, mul_assoc] using
      hmv [0, 1] 0
  case «0».«9» =>
    simpa [abstractWord, abstractAct, titsSignReflect, mul_assoc] using
      hmv [0, 1, 0] 0
  case «0».«11» =>
    simpa [abstractWord, abstractAct, titsSignReflect, mul_assoc] using
      hmv [0, 1, 0, 1] 0
  case «1».«8» =>
    simpa [abstractWord, abstractAct, titsSignReflect, mul_assoc] using
      hmv [1, 0] 0
  case «1».«10» =>
    simpa [abstractWord, abstractAct, titsSignReflect, mul_assoc] using
      hmv [1, 0, 1] 0
  case «1».«11» =>
    have hb' := hb.symm
    calc
      W 1 * (W 0 * (W 1 * (W 0 * (W 1 * (W 0 * W 1))))) =
          (W 1 * W 0 * W 1 * W 0 * W 1 * W 0) * W 1 := by group
      _ = (W 0 * W 1 * W 0 * W 1 * W 0 * W 1) * W 1 := by rw [hb']
      _ = W 0 * (W 1 * (W 0 * (W 1 * (W 0 * P 2)))) := by
        simp only [mul_assoc]
        rw [h1]

set_option maxHeartbeats 0 in
private theorem carrier_simple_square (i : Fin 2) :
    carrierWeylRepresentative (k := k) i * carrierWeylRepresentative (k := k) i =
      signPoint (k := k) (simpleSign i) := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul, signPoint, splitTorusMorphism_inclusion_apply,
    carrierWeylRepresentative_ambient_matrix]
  rw [torusAmbientMorphism_apply]
  simp only [torusPointRepresentation]
  let rho := ambientPointHom (k := k)
  change rho (Matrix.GeneralLinearGroup.toLin (weylMatrixUnit (R := k) i)) *
      rho (Matrix.GeneralLinearGroup.toLin (weylMatrixUnit (R := k) i)) =
    rho (Matrix.GeneralLinearGroup.toLin
      (torusElement (titsSignParameter (R := k) (simpleSign i))))
  rw [← rho.map_mul]
  have h : specialize (R := k) (weyl i) * specialize (R := k) (weyl i) =
      (torusElement (titsSignParameter (R := k) (simpleSign i))).val := by
    exact generic_simple_square i
  have hu : weylMatrixUnit (R := k) i * weylMatrixUnit (R := k) i =
      torusElement (titsSignParameter (R := k) (simpleSign i)) := Units.ext h
  simpa only [(Matrix.GeneralLinearGroup.toLin).map_mul] using
    congrArg rho (congrArg Matrix.GeneralLinearGroup.toLin hu)

private theorem carrier_left_positive
    (i : Fin 2) (j : Fin 12) :
    carrierWeylRepresentative (k := k) i *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      carrierWeylWord (k := k)
          (canonicalWeylWord (titsLeftTarget i false j)) *
        signPoint (k := k) (titsLeftSign i false j) := by
  have h0 : carrierWeylRepresentative (k := k) 0 *
      carrierWeylRepresentative (k := k) 0 = signPoint (k := k) 1 := by
    simpa only [simpleSign] using carrier_simple_square (k := k) 0
  have h1 : carrierWeylRepresentative (k := k) 1 *
      carrierWeylRepresentative (k := k) 1 = signPoint (k := k) 2 := by
    simpa only [simpleSign] using carrier_simple_square (k := k) 1
  have hm0 : ∀ s, signPoint (k := k) s * carrierWeylRepresentative (k := k) 0 =
      carrierWeylRepresentative (k := k) 0 * signPoint (k := k)
        (titsSignReflect 0 s) := preMove (k := k) 0
  have hm1 : ∀ s, signPoint (k := k) s * carrierWeylRepresentative (k := k) 1 =
      carrierWeylRepresentative (k := k) 1 * signPoint (k := k)
        (titsSignReflect 1 s) := preMove (k := k) 1
  have hb : carrierWeylRepresentative (k := k) 0 *
      carrierWeylRepresentative (k := k) 1 * carrierWeylRepresentative (k := k) 0 *
      carrierWeylRepresentative (k := k) 1 * carrierWeylRepresentative (k := k) 0 *
      carrierWeylRepresentative (k := k) 1 =
        carrierWeylRepresentative (k := k) 1 * carrierWeylRepresentative (k := k) 0 *
        carrierWeylRepresentative (k := k) 1 * carrierWeylRepresentative (k := k) 0 *
        carrierWeylRepresentative (k := k) 1 * carrierWeylRepresentative (k := k) 0 := by
    have hbr := pre_braid (k := k)
    simp only [carrierWeylWord, mul_one] at hbr
    calc
      _ = carrierWeylRepresentative (k := k) 0 *
          (carrierWeylRepresentative (k := k) 1 *
            (carrierWeylRepresentative (k := k) 0 *
              (carrierWeylRepresentative (k := k) 1 *
                (carrierWeylRepresentative (k := k) 0 *
                  carrierWeylRepresentative (k := k) 1)))) := by group
      _ = carrierWeylRepresentative (k := k) 1 *
          (carrierWeylRepresentative (k := k) 0 *
            (carrierWeylRepresentative (k := k) 1 *
              (carrierWeylRepresentative (k := k) 0 *
                (carrierWeylRepresentative (k := k) 1 *
                  carrierWeylRepresentative (k := k) 0)))) := hbr
      _ = _ := by group
  rw [← abstractWord_carrier, ← abstractWord_carrier]
  exact abstractPositive (carrierWeylRepresentative (k := k)) (signPoint (k := k))
    h0 h1 (signPoint_one (k := k)) hm0 hm1 hb i j

private theorem inverseTable (i : Fin 2) (j : Fin 12) :
    titsLeftTarget i false j = titsLeftTarget i true j ∧
      titsSignMul
          (preReflect (canonicalWeylWord (titsLeftTarget i false j)) (simpleSign i))
          (titsLeftSign i false j) = titsLeftSign i true j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem carrier_left_inverse (i : Fin 2) (j : Fin 12) :
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      carrierWeylWord (k := k)
          (canonicalWeylWord (titsLeftTarget i true j)) *
        signPoint (k := k) (titsLeftSign i true j) := by
  have hs : signPoint (k := k) (simpleSign i) *
      signPoint (k := k) (simpleSign i) = 1 := by
    fin_cases i
    · change signPoint (k := k) 1 * signPoint (k := k) 1 = 1
      rw [signPoint_mul]
      exact signPoint_one (k := k)
    · change signPoint (k := k) 2 * signPoint (k := k) 2 = 1
      rw [signPoint_mul]
      exact signPoint_one (k := k)
  have hsq := carrier_simple_square (k := k) i
  have hsignInv : (signPoint (k := k) (simpleSign i))⁻¹ =
      signPoint (k := k) (simpleSign i) := by
    calc
      (signPoint (k := k) (simpleSign i))⁻¹ =
          (signPoint (k := k) (simpleSign i))⁻¹ * 1 := by group
      _ = (signPoint (k := k) (simpleSign i))⁻¹ *
          (signPoint (k := k) (simpleSign i) *
            signPoint (k := k) (simpleSign i)) := by rw [hs]
      _ = signPoint (k := k) (simpleSign i) := by group
  have hinv : (carrierWeylRepresentative (k := k) i)⁻¹ =
      signPoint (k := k) (simpleSign i) * carrierWeylRepresentative (k := k) i := by
    calc
      (carrierWeylRepresentative (k := k) i)⁻¹ =
          (carrierWeylRepresentative (k := k) i *
            carrierWeylRepresentative (k := k) i)⁻¹ *
              carrierWeylRepresentative (k := k) i := by group
      _ = _ := by rw [hsq, hsignInv]
  have hp := carrier_left_positive (k := k) i j
  calc
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      signPoint (k := k) (simpleSign i) *
        (carrierWeylRepresentative (k := k) i *
          carrierWeylWord (k := k) (canonicalWeylWord j)) := by rw [hinv]; group
    _ = signPoint (k := k) (simpleSign i) *
        (carrierWeylWord (k := k) (canonicalWeylWord (titsLeftTarget i false j)) *
          signPoint (k := k) (titsLeftSign i false j)) := by rw [hp]
    _ = (carrierWeylWord (k := k)
          (canonicalWeylWord (titsLeftTarget i false j)) *
        signPoint (k := k)
          (preReflect (canonicalWeylWord (titsLeftTarget i false j)) (simpleSign i))) *
          signPoint (k := k) (titsLeftSign i false j) := by
            rw [← mul_assoc, preMoveWord]
    _ = carrierWeylWord (k := k)
          (canonicalWeylWord (titsLeftTarget i true j)) *
        signPoint (k := k) (titsLeftSign i true j) := by
          rw [mul_assoc, signPoint_mul]
          obtain ⟨htarget, hsign⟩ := inverseTable i j
          rw [hsign, htarget]

private theorem carrier_left_step (i : Fin 2) (inv : Bool) (j : Fin 12) :
    (if inv then carrierWeylRepresentativeInv (k := k) i
      else carrierWeylRepresentative (k := k) i) *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      carrierWeylWord (k := k) (canonicalWeylWord (titsLeftTarget i inv j)) *
      signPoint (k := k) (titsLeftSign i inv j) := by
  cases inv
  · exact carrier_left_positive (k := k) i j
  · simp only [if_true]
    rw [← carrierWeylRepresentative_inv]
    exact carrier_left_inverse (k := k) i j

/-- Left multiplication of a canonical carrier Weyl word by a signed lift. -/
public theorem canonicalWeyl_left_mul (i : Fin 2) (inv : Bool) (j : Fin 12) :
    (if inv then carrierWeylRepresentativeInv (k := k) i
      else carrierWeylRepresentative (k := k) i) *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      carrierWeylWord (k := k) (canonicalWeylWord (titsLeftTarget i inv j)) *
        (splitTorusMorphism (k := k)).onPoints
          ((dPointEquiv 2).symm
            (titsSignParameter (R := k) (titsLeftSign i inv j))) :=
  by simpa [signPoint] using carrier_left_step (k := k) i inv j

/-- Product of simple Weyl representatives, with inverse signs recorded in the word. -/
public noncomputable def signedCarrierWord : List (Fin 2 × Bool) → CarrierPoint (k := k)
  | [] => 1
  | (i, inv) :: w =>
      (if inv then carrierWeylRepresentativeInv (k := k) i
        else carrierWeylRepresentative (k := k) i) * signedCarrierWord w

private lemma signedCarrierWord_append (u v : List (Fin 2 × Bool)) :
    signedCarrierWord (k := k) (u ++ v) =
      signedCarrierWord (k := k) u * signedCarrierWord (k := k) v := by
  induction u with
  | nil => simp [signedCarrierWord]
  | cons a u ih =>
      simp only [List.cons_append, signedCarrierWord]
      rw [ih]
      simp only [mul_assoc]

private lemma signedCarrierWord_unsigned (w : List (Fin 2)) :
    signedCarrierWord (k := k) (w.map (fun i => (i, false))) =
      carrierWeylWord (k := k) w := by
  induction w with
  | nil => simp [signedCarrierWord, carrierWeylWord]
  | cons i w ih =>
      simp [signedCarrierWord, carrierWeylWord, ih]

/-- Every finite signed simple-lift word has a canonical Weyl word and a torus tail. -/
public theorem exists_canonicalWeyl_normalForm (w : List (Fin 2 × Bool)) :
    ∃ j : Fin 12, ∃ t : Variety.Point (dVariety k 2),
      signedCarrierWord (k := k) w =
        carrierWeylWord (k := k) (canonicalWeylWord j) *
          (splitTorusMorphism (k := k)).onPoints t := by
  induction w with
  | nil => exact ⟨0, 1, by simp [signedCarrierWord, canonicalWeylWord, carrierWeylWord]
      ⟩
  | cons a w ih =>
      obtain ⟨j, t, ht⟩ := ih
      rcases a with ⟨i, inv⟩
      let j' := titsLeftTarget i inv j
      let s := (dPointEquiv 2).symm (titsSignParameter (R := k) (titsLeftSign i inv j))
      refine ⟨j', s * t, ?_⟩
      rw [signedCarrierWord, ht, ← mul_assoc, canonicalWeyl_left_mul]
      simp only [j', s]
      rw [mul_assoc]
      exact congrArg
        (fun z : CarrierPoint (k := k) =>
          carrierWeylWord (k := k)
            (canonicalWeylWord (titsLeftTarget i inv j)) * z)
        ((splitTorusMorphism (k := k)).map_mul _ _).symm

/-- Right multiplication by one signed simple lift has a finite canonical normal form. -/
public theorem exists_canonicalWeyl_right_mul (j : Fin 12) (i : Fin 2) (inv : Bool) :
    ∃ j' : Fin 12, ∃ t : Variety.Point (dVariety k 2),
      carrierWeylWord (k := k) (canonicalWeylWord j) *
          (if inv then carrierWeylRepresentativeInv (k := k) i
            else carrierWeylRepresentative (k := k) i) =
        carrierWeylWord (k := k) (canonicalWeylWord j') *
          (splitTorusMorphism (k := k)).onPoints t := by
  let u : List (Fin 2 × Bool) :=
    (canonicalWeylWord j).map (fun a => (a, false))
  obtain ⟨j', t, ht⟩ := exists_canonicalWeyl_normalForm (k := k)
    (u ++ [(i, inv)])
  refine ⟨j', t, ?_⟩
  dsimp only [u] at ht
  rw [signedCarrierWord_append, signedCarrierWord_unsigned] at ht
  simpa only [signedCarrierWord, mul_one] using ht

/-- The square correction for a simple carrier Weyl representative. -/
public theorem carrierWeylRepresentative_square (i : Fin 2) :
    carrierWeylRepresentative (k := k) i * carrierWeylRepresentative (k := k) i =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm (if i = 0 then
          titsSignParameter (R := k) 1 else titsSignParameter (R := k) 2)) := by
  fin_cases i
  · simpa [signPoint, simpleSign] using carrier_simple_square (k := k) 0
  · simpa [signPoint, simpleSign] using carrier_simple_square (k := k) 1

/-- The corresponding inverse-lift square correction. -/
public theorem carrierWeylRepresentativeInv_square (i : Fin 2) :
    carrierWeylRepresentativeInv (k := k) i * carrierWeylRepresentativeInv (k := k) i =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm (if i = 0 then
          titsSignParameter (R := k) 1 else titsSignParameter (R := k) 2)) := by
  have hpp : signPoint (k := k) (simpleSign i) *
      signPoint (k := k) (simpleSign i) = 1 := by
    fin_cases i
    · change signPoint (k := k) 1 * signPoint (k := k) 1 = 1
      rw [signPoint_mul]
      exact signPoint_one (k := k)
    · change signPoint (k := k) 2 * signPoint (k := k) 2 = 1
      rw [signPoint_mul]
      exact signPoint_one (k := k)
  have hsignInv : (signPoint (k := k) (simpleSign i))⁻¹ =
      signPoint (k := k) (simpleSign i) := by
    calc
      (signPoint (k := k) (simpleSign i))⁻¹ =
          (signPoint (k := k) (simpleSign i))⁻¹ * 1 := by group
      _ = (signPoint (k := k) (simpleSign i))⁻¹ *
          (signPoint (k := k) (simpleSign i) *
            signPoint (k := k) (simpleSign i)) := by rw [hpp]
      _ = signPoint (k := k) (simpleSign i) := by group
  rw [← carrierWeylRepresentative_inv]
  calc
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (carrierWeylRepresentative (k := k) i)⁻¹ =
      (carrierWeylRepresentative (k := k) i *
        carrierWeylRepresentative (k := k) i)⁻¹ := by group
    _ = (signPoint (k := k) (simpleSign i))⁻¹ := by
      rw [carrier_simple_square]
    _ = signPoint (k := k) (simpleSign i) := hsignInv
    _ = _ := by fin_cases i <;> simp [signPoint, simpleSign]

/-- The length-six braid relation for the carrier Weyl lifts. -/
public theorem carrierWeylRepresentative_braid_six :
    carrierWeylWord (k := k) [0, 1, 0, 1, 0, 1] =
      carrierWeylWord (k := k) [1, 0, 1, 0, 1, 0] := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  rw [carrierWeylWord_ambient_matrix, carrierWeylWord_ambient_matrix]
  have hu : wordMatrix (R := k) [0, 1, 0, 1, 0, 1] =
      wordMatrix (R := k) [1, 0, 1, 0, 1, 0] := Units.ext generic_braid
  exact congrArg (ambientPointHom (k := k))
    (congrArg Matrix.GeneralLinearGroup.toLin hu)

public def wordTorusParameter {R : Type*} [CommRing R] :
    List (Fin 2) → TorusParameter R → TorusParameter R
  | [], u => u
  | i :: w, u => wordTorusParameter w (simpleReflectionTorusParameter i u)

private theorem carrierSimpleWeyl_dTorus_conjugation (i : Fin 2)
    (x : Variety.Point (dVariety k 2)) :
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x * carrierWeylRepresentative (k := k) i =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := carrierWeylRepresentative_splitTorus_conjugation (k := k) i
    ((splitTorusIso (k := k)).hom.onPoints x)
  simp only [simpleReflectionTorusPoint] at h
  rw [(splitTorusIso (k := k)).hom_inv_id] at h
  change (carrierWeylRepresentative (k := k) i)⁻¹ *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x) * carrierWeylRepresentative (k := k) i =
    (splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints
        ((dPointEquiv 2).symm
          (simpleReflectionTorusParameter i (dPointEquiv 2 x)))) at h
  rw [splitTorusIso_inclusion_apply, splitTorusIso_inclusion_apply] at h
  exact h

private theorem carrierWeylWord_dTorus_conjugation (w : List (Fin 2))
    (x : Variety.Point (dVariety k 2)) :
    (carrierWeylWord (k := k) w)⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x * carrierWeylWord (k := k) w =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (wordTorusParameter w (dPointEquiv 2 x))) := by
  induction w generalizing x with
  | nil => simp [carrierWeylWord, wordTorusParameter]
  | cons i w ih =>
      rw [carrierWeylWord, mul_inv_rev]
      calc
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              ((carrierWeylRepresentative (k := k) i)⁻¹ *
                (splitTorusMorphism (k := k)).onPoints x *
                carrierWeylRepresentative (k := k) i) *
              carrierWeylWord (k := k) w := by group
        _ = (carrierWeylWord (k := k) w)⁻¹ *
              (splitTorusMorphism (k := k)).onPoints
                ((dPointEquiv 2).symm
                  (simpleReflectionTorusParameter i (dPointEquiv 2 x))) *
              carrierWeylWord (k := k) w := by
                rw [carrierSimpleWeyl_dTorus_conjugation]
        _ = _ := by rw [ih]; congr 2

/-- Conjugation of a `dVariety` split-torus point by a canonical Weyl word. -/
public theorem canonicalWeyl_torus_conjugation (j : Fin 12)
    (x : Variety.Point (dVariety k 2)) :
    (carrierWeylWord (k := k) (canonicalWeylWord j))⁻¹ *
        (splitTorusMorphism (k := k)).onPoints x *
        carrierWeylWord (k := k) (canonicalWeylWord j) =
      (splitTorusMorphism (k := k)).onPoints
        ((dPointEquiv 2).symm
          (wordTorusParameter (canonicalWeylWord j) (dPointEquiv 2 x))) :=
  carrierWeylWord_dTorus_conjugation _ _

end

end Theory.AlgebraicGroup.G2Chevalley
