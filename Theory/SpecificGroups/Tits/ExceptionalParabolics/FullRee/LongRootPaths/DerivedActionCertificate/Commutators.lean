module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate.Normality
-- Internal certificate split keeps the faithful point calculations bounded.
import all Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate.Normality

/-!
# Commutator membership in the collected root subgroup

The faithful root multiplication equations place every core-generator
commutator in the collected subgroup. This is the abelian quotient half
of the intrinsic derived-core identification in J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
open DerivedCoreCertificate DerivedCorePacked DerivedOuterAction
open OuterOddSubgroups.OverlapCentralizers
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck0 (j:Fin 7) (hij:(0:Fin 7)<j) :
    root 0*root j=word (commutatorIndex 0 j)*root j*root 0 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (0:Fin 7)<j→
      (packedRoot 0*packedRoot j) k=
        (packedWord (commutatorIndex 0 j)*packedRoot j*packedRoot 0) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck1 (j:Fin 7) (hij:(1:Fin 7)<j) :
    root 1*root j=word (commutatorIndex 1 j)*root j*root 1 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (1:Fin 7)<j→
      (packedRoot 1*packedRoot j) k=
        (packedWord (commutatorIndex 1 j)*packedRoot j*packedRoot 1) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck2 (j:Fin 7) (hij:(2:Fin 7)<j) :
    root 2*root j=word (commutatorIndex 2 j)*root j*root 2 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (2:Fin 7)<j→
      (packedRoot 2*packedRoot j) k=
        (packedWord (commutatorIndex 2 j)*packedRoot j*packedRoot 2) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck3 (j:Fin 7) (hij:(3:Fin 7)<j) :
    root 3*root j=word (commutatorIndex 3 j)*root j*root 3 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (3:Fin 7)<j→
      (packedRoot 3*packedRoot j) k=
        (packedWord (commutatorIndex 3 j)*packedRoot j*packedRoot 3) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck4 (j:Fin 7) (hij:(4:Fin 7)<j) :
    root 4*root j=word (commutatorIndex 4 j)*root j*root 4 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (4:Fin 7)<j→
      (packedRoot 4*packedRoot j) k=
        (packedWord (commutatorIndex 4 j)*packedRoot j*packedRoot 4) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem commutatorCheck5 (j:Fin 7) (hij:(5:Fin 7)<j) :
    root 5*root j=word (commutatorIndex 5 j)*root j*root 5 := by
  apply Subtype.ext
  simp only [val_mul,root_val,word_val]
  have h:∀(j:Fin 7)(k:Fin 1600), (5:Fin 7)<j→
      (packedRoot 5*packedRoot j) k=
        (packedWord (commutatorIndex 5 j)*packedRoot j*packedRoot 5) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (fun k=>h j k hij)

theorem root_commutator (i j:Fin 7) (hij:i<j) :
    root i*root j*(root i)^3*(root j)^3=word (commutatorIndex i j) := by
  have hm:root i*root j=word (commutatorIndex i j)*root j*root i := by
    fin_cases i
    · exact commutatorCheck0 j hij
    · exact commutatorCheck1 j hij
    · exact commutatorCheck2 j hij
    · exact commutatorCheck3 j hij
    · exact commutatorCheck4 j hij
    · exact commutatorCheck5 j hij
    · change 6<j.val at hij
      omega
  rw [← root_inv,← root_inv,hm,mul_inv_cancel_right,mul_inv_cancel_right]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck0 : actionWord 0=word (outerIndex 0)*root 0 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 0 k=(packedWord (outerIndex 0)*packedRoot 0) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck1 : actionWord 1=word (outerIndex 1)*root 1 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 1 k=(packedWord (outerIndex 1)*packedRoot 1) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck2 : actionWord 2=word (outerIndex 2)*root 2 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 2 k=(packedWord (outerIndex 2)*packedRoot 2) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck3 : actionWord 3=word (outerIndex 3)*root 3 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 3 k=(packedWord (outerIndex 3)*packedRoot 3) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck4 : actionWord 4=word (outerIndex 4)*root 4 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 4 k=(packedWord (outerIndex 4)*packedRoot 4) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck5 : actionWord 5=word (outerIndex 5)*root 5 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 5 k=(packedWord (outerIndex 5)*packedRoot 5) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem outerCheck6 : actionWord 6=word (outerIndex 6)*root 6 := by
  apply Subtype.ext
  simp only [val_mul,root_val,action_val,word_val]
  have h:∀k:Fin 1600,
      packedAction 6 k=(packedWord (outerIndex 6)*packedRoot 6) k := by
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact Equiv.ext h

theorem outer_commutator (i:Fin 7) :
    actionWord i*(root i)^3=word (outerIndex i) := by
  have hm:actionWord i=word (outerIndex i)*root i := by
    fin_cases i
    · exact outerCheck0
    · exact outerCheck1
    · exact outerCheck2
    · exact outerCheck3
    · exact outerCheck4
    · exact outerCheck5
    · exact outerCheck6
  rw [← root_inv,hm,mul_inv_cancel_right]


end Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
