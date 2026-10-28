module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.InputBridge
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.TableChecks

/-!
# The checked table acts by the actual M11 words

Strong induction on the predecessor indices identifies every table action
with its literal marked A/B word. No injectivity or enumeration theorem is used.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

open Sporadic.Mathieu Inputs CertificateData

theorem decode_stable (n c : ℕ) (hc : c < 2 ^ (n+1)) :
    decodeWord (n+1) c = decodeWord n c := by
  induction n generalizing c with
  | zero =>
    have h : c ≤ 1 := by norm_num at hc ⊢; omega
    simp [decodeWord, h]
  | succ n ih =>
    by_cases h : c ≤ 1
    · simp [decodeWord, h]
    · conv_lhs => rw [decodeWord]
      conv_rhs => rw [decodeWord]
      simp only [if_neg h]
      rw [ih]
      rw [pow_succ] at hc
      omega

theorem decode_step (c : ℕ) (h : 1 < c) (hc : c < 2^32) :
    decodeWord 32 c = decodeWord 32 (c/2) ++ [Fin.ofNat 2 c] := by
  rw [decodeWord, if_neg (by omega)]
  rw [decode_stable 31 (c/2) (by omega)]

theorem generator_digit (s : Fin 2) (x : Fin 11) :
    ((generator s).val x).val = digit (genCode s.val) x.val := by
  fin_cases s <;> fin_cases x <;> rfl

theorem word_append (w : List (Fin 2)) (s : Fin 2) :
    CertificateData.evalWord (w ++ [s]) = CertificateData.evalWord w * generator s := by
  simp [CertificateData.evalWord, List.prod_append]

theorem word_step_spec (i : ℕ) (h : wordStep i = true) :
    parentCode i < i ∧ 1 < wordCode i ∧ wordCode i < 2^32 ∧
      wordCode i / 2 = wordCode (parentCode i) ∧
      ∀ x < 11, digit (permCode i) x =
        digit (permCode (parentCode i)) (digit (genCode (wordCode i % 2)) x) := by
  simpa only [wordStep, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    allBelow_spec, and_assoc] using h

theorem index_point_of_checks
    (hw : ∀ i : Index, wordCode i.val = tableEntry wordCodes i.val)
    (hs : ∀ i : Index, i.val ≠ 0 → wordStep i.val = true)
    (i : Index) (x : Fin 11) :
    ((indexElement i).val x).val = digit (permCode i.val) x.val := by
  induction i using Fin.strong_induction_on generalizing x with
  | h i ih =>
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i
      have hzero : indexWord 0 = [] := by decide +kernel
      have hpoint : ∀ y : Fin 11, y.val = digit (permCode 0) y.val := by decide +kernel
      simp only [indexElement, hzero, CertificateData.evalWord, List.map_nil, List.prod_nil]
      exact hpoint x
    · obtain ⟨hp, hc, hbound, heq, hpoints⟩ := word_step_spec i.val (hs i hi)
      let p : Index := ⟨parentCode i.val, by omega⟩
      have hwrd : indexWord i = indexWord p ++ [Fin.ofNat 2 (wordCode i.val)] := by
        change decodeWord 32 (tableEntry wordCodes i.val) =
          decodeWord 32 (tableEntry wordCodes p.val) ++ _
        rw [← hw i, ← hw p, decode_step _ hc hbound, heq]
      change ((CertificateData.evalWord (indexWord i)).val x).val = _
      rw [hwrd, word_append]
      change ((indexElement p).val ((generator (Fin.ofNat 2 (wordCode i.val))).val x)).val = _
      rw [ih p hp, generator_digit]
      exact (hpoints x.val x.isLt).symm

theorem sylow_point (t : Fin 11) (x : Fin 11) :
    ((m11Sylow11Generator ^ t.val).val x).val = digit (powerCodes[t.val]!) x.val := by
  fin_cases t <;> fin_cases x <;> rfl

/-- Each packed point action is the action of the actual indexed group word. -/
theorem index_point (i : Index) (x : Fin 11) :
    ((indexElement i).val x).val = digit (permCode i.val) x.val :=
  index_point_of_checks wordCode_eq (fun i hi => word_checked i.val i.isLt hi) i x

/-- The seed action checks, expressed with the literal shared indices. -/
theorem seed_point (k : Seed) (t x : Fin 11) :
    digit (permCode (seedEntry k t).val) x.val =
      digit (permCode (translateLeft k).val)
        (digit (powerCodes[t.val]!) (digit (permCode (translateRight k).val) x.val)) := by
  have h := (allBelow_spec _ _).mp (seed_checked k.val k.isLt) t.val t.isLt
  have h' := (allBelow_spec _ _).mp h x.val x.isLt
  simp only [beq_iff_eq] at h'
  simpa only [seedEntry, translateLeft, translateRight, Fin.val_ofNat,
    ← seedCode_eq k, ← translateCode_eq k] using h'

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
