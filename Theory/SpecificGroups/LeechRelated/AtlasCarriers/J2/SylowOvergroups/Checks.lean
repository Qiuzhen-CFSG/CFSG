module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Data
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.SylowOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.OrbitChecks

/-!
# Kernel checks for the Hall--Janko Sylow-overgroup witnesses

Packed permutation lookups verify the word tables, centralizer-coset
separation, the double-coset factors and the generation witnesses. Group
identities in the large factor table are tested on the four-point base;
the reconstruction theorem in `Coverage` justifies this reduction.
Source: ATLAS J2G1-p100B0; Aschbacher--Smith A.3.12(16), pp.47--48.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.SylowOvergroups
open Theory.GroupTheory GeneratorPair GeneratorPair.SecondOrbitCertificate
open ExceptionalParabolics.PairNormalizer Data
set_option Elab.async false


private theorem checkFin_true {n : ℕ} (f : Fin n → Bool)
    (h : FirstFusion.checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

/-- Function evaluation avoids rebuilding permutation structures in the checks. -/
def evalFun {n : ℕ} (g : Fin n → Fin 100 → Fin 100) : List (Fin n) → Fin 100 → Fin 100
  | [], p => p
  | i :: w, p => g i (evalFun g w p)

def pValue (i : Fin 9) : Fin 100 → Fin 100 :=
  if h : i.val < 7 then sVal (SylowData.sGenIndex ⟨i.val,h⟩)
  else packedMap (QuotientData.oddCode ⟨i.val - 7, by omega⟩)

def gValue (j : Fin 72) (i : Fin 16) : Fin 100 → Fin 100 :=
  if h : i.val < 7 then sVal (SylowData.sGenIndex ⟨i.val,h⟩)
  else if i.val = 7 then dVal j
  else if h : i.val < 15 then sGenInvVal ⟨i.val - 8, by omega⟩
  else dInvVal j

set_option maxRecDepth 100000 in
private theorem cWord_check : FirstFusion.checkFin (fun i : Fin 15 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide
      (cVal i p = evalFun FirstFusion.letterValue (cWord i) p))) = true := by
  decide +kernel

theorem cWord_spec (i : Fin 15) (p : Fin 100) :
    cVal i p = evalFun FirstFusion.letterValue (cWord i) p :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ cWord_check i) p)

set_option maxRecDepth 100000 in
private theorem fBase_check : FirstFusion.checkFin (fun p : Fin 100 => decide
    (fVal 0 p = p)) = true := by decide +kernel

theorem fBase_spec (p : Fin 100) : fVal 0 p = p :=
  of_decide_eq_true (checkFin_true _ fBase_check p)

set_option maxRecDepth 100000 in
private theorem fStep_check : FirstFusion.checkFin (fun i : Fin 315 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide (i ≠ 0 →
      fVal i p = fVal (FirstFusion.OrbitData.parent i)
        (FirstFusion.letterValue (FirstFusion.OrbitData.parentLetter i) p)))) = true := by
  decide +kernel

theorem fStep_spec (i : Fin 315) (p : Fin 100) (hi : i ≠ 0) :
    fVal i p = fVal (FirstFusion.OrbitData.parent i)
      (FirstFusion.letterValue (FirstFusion.OrbitData.parentLetter i) p) :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ fStep_check i) p) hi

set_option maxRecDepth 100000 in
private theorem sTable_check : FirstFusion.checkFin (fun i : Fin 128 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide (sVal i p = SylowData.sTable i p))) = true := by
  decide +kernel

theorem sTable_spec (i : Fin 128) (p : Fin 100) : sVal i p = SylowData.sTable i p :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ sTable_check i) p)

set_option maxRecDepth 100000 in
private theorem sInv_check : FirstFusion.checkFin (fun i : Fin 7 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide
      (sGenInvVal i p = (SylowData.sGenTable i)⁻¹ p))) = true := by decide +kernel

theorem sInv_spec (i : Fin 7) (p : Fin 100) :
    sGenInvVal i p = (SylowData.sGenTable i)⁻¹ p :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ sInv_check i) p)

set_option maxRecDepth 100000 in
private theorem cCentral_check : FirstFusion.checkFin (fun i : Fin 15 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide
      (cVal i (FirstFusion.tPerm p) = FirstFusion.tPerm (cVal i p)))) = true := by
  decide +kernel

theorem cCentral_spec (i : Fin 15) (p : Fin 100) :
    cVal i (FirstFusion.tPerm p) = FirstFusion.tPerm (cVal i p) :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ cCentral_check i) p)

set_option maxRecDepth 100000 in
private theorem cSeparate_check : FirstFusion.checkFin (fun i : Fin 15 =>
    FirstFusion.checkFin (fun j : Fin 15 => FirstFusion.checkFin (fun k : Fin 128 => decide
      ((cVal i 0 = sVal k (cVal j 0) ∧ cVal i 1 = sVal k (cVal j 1) ∧
        cVal i 2 = sVal k (cVal j 2)) → i = j)))) = true := by decide +kernel

theorem cSeparate_spec (i j : Fin 15) (k : Fin 128)
    (h : cVal i 0 = sVal k (cVal j 0) ∧ cVal i 1 = sVal k (cVal j 1) ∧
      cVal i 2 = sVal k (cVal j 2)) : i = j :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ (checkFin_true _ cSeparate_check i) j) k) h

set_option maxRecDepth 100000 in
private theorem factor_check : FirstFusion.checkFin (fun i : Fin 15 =>
    FirstFusion.checkFin (fun j : Fin 315 => FirstFusion.checkFin (fun p : Fin 4 => decide
      (cVal i (fVal j (p.castLE (by decide))) =
        sVal (factor i j).2.1 (dVal (factor i j).1
          (sVal (factor i j).2.2 (p.castLE (by decide)))))))) = true := by decide +kernel

theorem factor_spec (i : Fin 15) (j : Fin 315) (p : Fin 4) :
    cVal i (fVal j (p.castLE (by decide))) =
      sVal (factor i j).2.1 (dVal (factor i j).1
        (sVal (factor i j).2.2 (p.castLE (by decide)))) :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ (checkFin_true _ factor_check i) j) p)

set_option maxRecDepth 100000 in
private theorem dInv_check : FirstFusion.checkFin (fun i : Fin 72 =>
    FirstFusion.checkFin (fun p : Fin 100 => decide (dVal i (dInvVal i p) = p))) = true := by
  decide +kernel

theorem dInv_spec (i : Fin 72) (p : Fin 100) : dVal i (dInvVal i p) = p :=
  of_decide_eq_true (checkFin_true _ (checkFin_true _ dInv_check i) p)

set_option maxRecDepth 100000 in
private theorem row_check : FirstFusion.checkFin (fun j : Fin 72 => decide
    (if rowKind j = 0 then
      FirstFusion.checkFin (fun p : Fin 100 => decide
        (dVal j (FirstFusion.tPerm p) = FirstFusion.tPerm (dVal j p))) = true
    else if rowKind j = 1 then
      FirstFusion.checkFin (fun p : Fin 4 => decide
        (dVal j (p.castLE (by decide)) = evalFun pValue (pWord j) (p.castLE (by decide)))) = true
    else
      FirstFusion.checkFin (fun p : Fin 4 => decide
        (evalFun (gValue j) (gWord j) (p.castLE (by decide)) = tableB (p.castLE (by decide)))) = true)) = true := by
  decide +kernel

theorem row_spec (j : Fin 72) :
    (∀ p, dVal j (FirstFusion.tPerm p) = FirstFusion.tPerm (dVal j p)) ∨
    (∀ p : Fin 4, dVal j (p.castLE (by decide)) = evalFun pValue (pWord j) (p.castLE (by decide))) ∨
    (∀ p : Fin 4, evalFun (gValue j) (gWord j) (p.castLE (by decide)) = tableB (p.castLE (by decide))) := by
  have h := of_decide_eq_true (checkFin_true _ row_check j)
  split at h
  · exact Or.inl (fun p => of_decide_eq_true (checkFin_true _ h p))
  · split at h
    · exact Or.inr (Or.inl (fun p => of_decide_eq_true (checkFin_true _ h p)))
    · exact Or.inr (Or.inr (fun p => of_decide_eq_true (checkFin_true _ h p)))

end Sporadic.LeechRelated.J2.SylowOvergroups
