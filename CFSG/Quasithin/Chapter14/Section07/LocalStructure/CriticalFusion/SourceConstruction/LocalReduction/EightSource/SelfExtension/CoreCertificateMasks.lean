module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CoreCertificateData
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.MaskMatrices

/-!
# Finite row certificates for core-by-natural extensions

The selected Coxeter relations have 252 independent rows. Their explicit
binary masks are checked against symbolic matrix multiplication. Each input
coordinate is then the sum of its coboundary correction and an
explicit combination of those relation rows. All finite checks use Lean's
kernel.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
namespace CoreCertificateMasks
open CoreCertificateData
open MaskMatrices

def index (i : Fin 7) (r : Fin 7) (c : Fin 6) : Fin 294 := ⟨i.val*42+r.val*6+c.val,by omega⟩
def input (i : Fin 7) : MatrixMask 7 6 294 := fun r c => Mask.unit (index i r c)

def relation (typ : Fin 3) (i j : Fin 7) : MatrixMask 7 6 294 :=
  if typ = 0 then add (left (coreRows i) (input i)) (right (input i) (rows i))
  else if typ = 1 then add
    (add (left (coreRows i) (input j)) (right (input i) (rows j)))
    (add (left (coreRows j) (input i)) (right (input j) (rows i)))
  else add
    (add (add (left (coreRows i) (left (coreRows j) (input i)))
      (right (left (coreRows i) (input j)) (rows i)))
      (right (right (input i) (rows j)) (rows i)))
    (add (add (left (coreRows j) (left (coreRows i) (input j)))
      (right (left (coreRows j) (input i)) (rows j)))
      (right (right (input j) (rows i)) (rows j)))

def correction : MatrixMask 7 6 294 :=
  fun r c => correctionMasks ⟨r.val*6+c.val,by omega⟩

def correctionOutput (i : Fin 7) : MatrixMask 7 6 294 :=
  add (left (coreRows i) correction) (right correction (rows i))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem constraintMasks_spec : ∀ k : Fin 252,
    let p := constraintPlaces k
    relation p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 = constraintMasks k := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem constraintPlaces_valid : ∀ k : Fin 252,
    let p := constraintPlaces k
    (p.1 = 1 → p.2.1.val + 1 < p.2.2.1.val) ∧
    (p.1 = 2 → p.2.2.1.val = p.2.1.val + 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem correction_certificate : ∀ (i : Fin 7) (r : Fin 7) (c : Fin 6),
    input i r c = correctionOutput i r c ^^^
      Mask.substitute constraintMasks (certificates (index i r c)) := by
  decide +kernel
end CoreCertificateMasks
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
