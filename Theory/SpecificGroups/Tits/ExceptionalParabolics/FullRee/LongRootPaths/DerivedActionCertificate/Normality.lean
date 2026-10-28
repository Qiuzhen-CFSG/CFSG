module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedCoreCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedOuterAction

/-!
# The collected subgroup is the radical commutator subgroup

Small faithful word checks record the seven derived-root actions, their
pairwise commutators, and the specified outer-root action. The outer action
itself is proved by the separate binary matrix calculation. These tables
supply normality and both inclusions for the intrinsic derived subgroup;
they do not enumerate a subgroup lattice. Source: J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
open DerivedCoreCertificate DerivedCorePacked DerivedOuterAction
open OuterOddSubgroups.OverlapCentralizers

private def packedRoot (i:Fin 7) : Equiv.Perm (Fin 1600) :=
  ![Packed.perm 2,Packed.perm 3,Packed.perm 4,Packed.perm 5,
    Packed.perm 6,Packed.perm 7,Packed.perm 8] i
private def packedAction (i:Fin 7) : Equiv.Perm (Fin 1600) :=
  ![packedRoot 0,packedRoot 1,packedRoot 1*packedRoot 2,
    packedRoot 0*packedRoot 1*(packedRoot 2)^2*packedRoot 3,packedRoot 4,
    packedRoot 0*packedRoot 3*(packedRoot 4)^2*packedRoot 5,
    packedRoot 0*(packedRoot 2)^3*packedRoot 3*(packedRoot 4)^3*packedRoot 6] i

private theorem val_mul (a b:Atlas1600Group) : (a*b).val=a.val*b.val := rfl
private theorem val_pow (a:Atlas1600Group) (n:Nat) : (a^n).val=a.val^n := rfl
private theorem val_inv (a:Atlas1600Group) : a⁻¹.val=a.val⁻¹ := rfl
private theorem root_val (i:Fin 7) : (root i).val=packedRoot i := by
  fin_cases i <;> simp [root,packedRoot,Atlas.a,Packed.perm_eq,Packed.generator,
    atlas1600ParrottAssignment_val,Atlas1600ParrottData.permutation]
private theorem action_val (i:Fin 7) : (actionWord i).val=packedAction i := by
  fin_cases i <;> simp [actionWord,packedAction,packedRoot,val_mul,pow_succ,mul_assoc,
    Atlas.a,Packed.perm_eq,Packed.generator,atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation]

def normalIndex:Fin 7→Fin 6→Fin 64 :=
  ![![1,2,4,8,17,32],
    ![1,2,4,8,16,33],
    ![1,3,4,8,18,43],
    ![1,2,4,8,16,32],
    ![1,3,4,9,22,43],
    ![1,2,4,8,16,36],
    ![1,7,4,11,19,63]]

def commutatorIndex:Fin 7→Fin 7→Fin 64 :=
  ![![0,0,0,0,0,1,14],
    ![0,0,0,0,1,0,3],
    ![0,0,0,1,10,2,45],
    ![0,0,1,0,1,0,5],
    ![0,1,10,1,0,6,49],
    ![1,0,2,0,6,0,3],
    ![14,3,43,5,50,3,0]]

def outerIndex:Fin 7→Fin 64 := ![0,0,8,1,0,6,39]

def outerGenIndex:Fin 6→Fin 64 := ![1,3,4,8,22,40]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem root_four (i:Fin 7) : (root i)^4=1 := by
  apply Subtype.ext
  change (root i).val^4=1
  rw [root_val]
  have h:∀(i:Fin 7)(k:Fin 1600),(packedRoot i^4) k=k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h i)

private theorem root_inv (i:Fin 7) : (root i)⁻¹=(root i)^3 := by
  calc
    (root i)⁻¹=(root i)⁻¹*1 := (mul_one _).symm
    _ = (root i)⁻¹*(root i)^4 := congrArg _ (root_four i).symm
    _ = (root i)^3 := by group

-- Fixed-root multiplication checks keep each kernel certificate bounded.
-- Multiplying on the right avoids evaluating cubic inverse words.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck0 (j:Fin 6) :
    root 0*gen j=word (normalIndex 0 j)*root 0 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 0*packedGen j) k=(packedWord (normalIndex 0 j)*packedRoot 0) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck1 (j:Fin 6) :
    root 1*gen j=word (normalIndex 1 j)*root 1 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 1*packedGen j) k=(packedWord (normalIndex 1 j)*packedRoot 1) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck2 (j:Fin 6) :
    root 2*gen j=word (normalIndex 2 j)*root 2 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 2*packedGen j) k=(packedWord (normalIndex 2 j)*packedRoot 2) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck3 (j:Fin 6) :
    root 3*gen j=word (normalIndex 3 j)*root 3 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 3*packedGen j) k=(packedWord (normalIndex 3 j)*packedRoot 3) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck4 (j:Fin 6) :
    root 4*gen j=word (normalIndex 4 j)*root 4 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 4*packedGen j) k=(packedWord (normalIndex 4 j)*packedRoot 4) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck5 (j:Fin 6) :
    root 5*gen j=word (normalIndex 5 j)*root 5 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 5*packedGen j) k=(packedWord (normalIndex 5 j)*packedRoot 5) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem conjugateCheck6 (j:Fin 6) :
    root 6*gen j=word (normalIndex 6 j)*root 6 := by
  apply Subtype.ext
  simp only [val_mul,root_val,gen_val,word_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedRoot 6*packedGen j) k=(packedWord (normalIndex 6 j)*packedRoot 6) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

theorem root_conjugates_collected (i:Fin 7)(j:Fin 6) :
    root i*gen j*(root i)^3=word (normalIndex i j) := by
  have hm:root i*gen j=word (normalIndex i j)*root i := by
    fin_cases i
    · exact conjugateCheck0 j
    · exact conjugateCheck1 j
    · exact conjugateCheck2 j
    · exact conjugateCheck3 j
    · exact conjugateCheck4 j
    · exact conjugateCheck5 j
    · exact conjugateCheck6 j
  rw [← root_inv,hm,mul_inv_cancel_right]


end Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
