module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CertificateData
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.MaskMatrices

/-!
# Finite row certificates for natural-six self-extensions

The selected Coxeter relations have 216 independent rows. Their explicit
binary masks are checked against symbolic matrix multiplication. Each input
coordinate is then the sum of its coboundary-plus-parity correction and an
explicit combination of those relation rows. All finite checks use Lean's
kernel.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
namespace CertificateMasks
open CertificateData
open MaskMatrices

def index (i : Fin 7) (r c : Fin 6) : Fin 252 := ⟨i.val*36+r.val*6+c.val,by omega⟩
def input (i : Fin 7) : MatrixMask 6 6 252 := fun r c => Mask.unit (index i r c)

def relation (typ : Fin 3) (i j : Fin 7) : MatrixMask 6 6 252 :=
  if typ = 0 then add (left (rows i) (input i)) (right (input i) (rows i))
  else if typ = 1 then add
    (add (left (rows i) (input j)) (right (input i) (rows j)))
    (add (left (rows j) (input i)) (right (input j) (rows i)))
  else add
    (add (add (left (rows i) (left (rows j) (input i)))
      (right (left (rows i) (input j)) (rows i)))
      (right (right (input i) (rows j)) (rows i)))
    (add (add (left (rows j) (left (rows i) (input j)))
      (right (left (rows j) (input i)) (rows j)))
      (right (right (input j) (rows i)) (rows j)))

def correction : MatrixMask 6 6 252 :=
  fun r c => correctionMasks ⟨r.val*6+c.val,by omega⟩

def parity : BitVec 252 := correctionMasks 36

def correctionOutput (i : Fin 7) : MatrixMask 6 6 252 :=
  add (add (left (rows i) correction) (right correction (rows i)))
    (fun r c => if (rows i r).getLsbD c.val then parity else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem constraintMasks_spec : ∀ k : Fin 216,
    let p := constraintPlaces k
    relation p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 = constraintMasks k := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem constraintPlaces_valid : ∀ k : Fin 216,
    let p := constraintPlaces k
    (p.1 = 1 → p.2.1.val + 1 < p.2.2.1.val) ∧
    (p.1 = 2 → p.2.2.1.val = p.2.1.val + 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem correction_certificate : ∀ (i : Fin 7) (r c : Fin 6),
    input i r c = correctionOutput i r c ^^^
      Mask.substitute constraintMasks (certificates (index i r c)) := by
  decide +kernel
end CertificateMasks
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
