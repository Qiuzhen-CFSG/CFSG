module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCoreCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedCorePacked

/-!
# A small collected subgroup in the binary linear radical

Six specified Parrott words form a collected sequence for a group of order
64. Five are involutions; the last has square in the first three. Point zero
separates the 64 binary words, and a two-generator point test bounds their
center by the first eight words. All checks are faithful word certificates,
without subgroup-lattice enumeration. Source: the local root calculation in
J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedCoreCertificate
open OuterOddSubgroups.OverlapCentralizers
open Subgroup

/-- The collected sequence, with central generators first. -/
def gen (i:Fin 6) : Atlas1600Group :=
  ![Atlas.a .s1*Atlas.a .s2*(Atlas.a .s3)^2,Atlas.a .s4,
    Atlas.a .s1*(Atlas.a .s5)^2,Atlas.a .s2,Atlas.a .s6,
    (Atlas.a .s3)^3*Atlas.a .s5] i

/-- The 64 binary collected words. -/
def word (n:Fin 64) : Atlas1600Group :=
  gen 0^(n.val%2)*gen 1^(n.val/2%2)*gen 2^(n.val/4%2)*
    gen 3^(n.val/8%2)*gen 4^(n.val/16%2)*gen 5^(n.val/32%2)

open DerivedCorePacked

def packedWord (n:Fin 64) : Equiv.Perm (Fin 1600) :=
  packedGen 0^(n.val%2)*packedGen 1^(n.val/2%2)*packedGen 2^(n.val/4%2)*
    packedGen 3^(n.val/8%2)*packedGen 4^(n.val/16%2)*packedGen 5^(n.val/32%2)

private theorem val_mul (a b:Atlas1600Group) : (a*b).val=a.val*b.val := rfl
private theorem val_pow (a:Atlas1600Group) (n:Nat) : (a^n).val=a.val^n := rfl

theorem gen_val (i:Fin 6) : (gen i).val=packedGen i := by
  fin_cases i <;>
    simp [gen,val_mul,val_pow,packedGen_eq,original,Atlas.a,Packed.perm_eq,Packed.generator,atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation]
theorem word_val (n:Fin 64) : (word n).val=packedWord n := by
  simp only [word,packedWord,val_mul,val_pow,gen_val]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem generator_power (i:Fin 6) : gen i^(if i=5 then 4 else 2)=1 := by
  apply Subtype.ext
  change (gen i).val^(if i=5 then 4 else 2)=1
  rw [gen_val]
  have h : ∀ (i:Fin 6) (k:Fin 1600), (packedGen i^(if i=5 then 4 else 2)) k=k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h i)

/-- Collected conjugation indices. -/
def conjugateIndex : Fin 6→Fin 6→Fin 64 :=
  ![![1,2,4,8,16,32],
    ![1,2,4,8,16,32],
    ![1,2,4,8,16,32],
    ![1,2,4,8,16,33],
    ![1,2,4,8,16,36],
    ![1,2,4,9,20,32]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem conjugate_eq (i j:Fin 6) : gen i*gen j*(gen i)^3=word (conjugateIndex i j) := by
  apply Subtype.ext
  change (gen i).val*(gen j).val*((gen i).val)^3=(word (conjugateIndex i j)).val
  rw [gen_val,gen_val,word_val]
  have h : ∀ (i j:Fin 6) (k:Fin 1600),
      (packedGen i*packedGen j*(packedGen i)^3) k=packedWord (conjugateIndex i j) k := by
    apply Atlas1600OrderCertificate.allFin₃
    decide +kernel
  exact Equiv.ext (h i j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem last_square : (gen 5)^2=gen 0*gen 1*gen 2 := by
  apply Subtype.ext
  change ((gen 5).val)^2=(gen 0).val*(gen 1).val*(gen 2).val
  rw [gen_val,gen_val,gen_val,gen_val]
  have h : (packedGen 5)^2=packedGen 0*packedGen 1*packedGen 2 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem word_injective : Function.Injective word := by
  have h : ∀ n m:Fin 64,packedWord n 0=packedWord m 0→n=m := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  intro n m he
  apply h
  simpa only [word_val] using congrArg (fun a:Atlas1600Group=>a.val 0) he

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem center_candidate (n:Fin 64)
    (h3:Commute (word n) (gen 3)) (h5:Commute (word n) (gen 5)) : n.val<8 := by
  have h : ∀ n:Fin 64,
      (packedWord n*packedGen 3) 0=(packedGen 3*packedWord n) 0 →
      (packedWord n*packedGen 5) 0=(packedGen 5*packedWord n) 0 → n.val<8 := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  apply h n
  · simpa only [val_mul,word_val,gen_val] using congrArg (fun a:Atlas1600Group=>a.val 0) h3.eq
  · simpa only [val_mul,word_val,gen_val] using congrArg (fun a:Atlas1600Group=>a.val 0) h5.eq

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedCoreCertificate
