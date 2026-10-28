module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate.Commutators
-- The packed maps are an internal boundary of this certificate family.
import all Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate.Normality

/-!
# Derived generators and the marked central short root

The outer action preserves the collected subgroup. Its generators are
products of the certified root commutators, and the marked short root
commutes with them all. Together with the preceding normality and
commutator files this identifies the intrinsic derived core.
Source: J.4.7, printed p.444.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
open DerivedCoreCertificate DerivedCorePacked DerivedOuterAction
open OuterOddSubgroups.OverlapCentralizers
/-- The six collected words evaluated in any group. -/
def collectedWords {H:Type*} [Group H] (r:Fin 7→H) (i:Fin 6) : H :=
  ![r 0*r 1*(r 2)^2,r 3,r 0*(r 4)^2,r 1,r 5,(r 2)^3*r 4] i

private theorem map_collectedWords {H K:Type*} [Group H] [Group K]
    (f:H→*K) (r:Fin 7→H) (i:Fin 6) :
    f (collectedWords r i)=collectedWords (fun j=>f (r j)) i := by
  fin_cases i <;> simp [collectedWords,map_mul,map_pow]

/-- q applied to each collected generator, before collection. -/
def actedGen (i:Fin 6) : Atlas1600Group := collectedWords actionWord i
private def packedActed (i:Fin 6) : Equiv.Perm (Fin 1600) := collectedWords packedAction i

private theorem acted_val (i:Fin 6) : (actedGen i).val=packedActed i := by
  have he : (fun j:Fin 7=>(actionWord j).val)=packedAction := funext action_val
  exact (map_collectedWords (show Atlas1600Group→*Equiv.Perm (Fin 1600) from {toFun:=Subtype.val,map_one' :=rfl,map_mul' :=fun _ _=>rfl})
    actionWord i).trans (congrArg (fun r=>collectedWords r i) he)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem outer_conjugates_collected (i:Fin 6) : actedGen i=word (outerGenIndex i) := by
  apply Subtype.ext
  rw [acted_val,word_val]
  have h:∀(i:Fin 6)(k:Fin 1600),packedActed i k=packedWord (outerGenIndex i) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h i)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem fourth_generator_witness : gen 4=word 1*word 49*word 39 := by
  apply Subtype.ext
  simp only [val_mul,gen_val,word_val]
  have h:packedGen 4=packedWord 1*packedWord 49*packedWord 39 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem last_generator_witness : gen 5=(word 39)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change (gen 5).val*(word 39).val=1
  rw [gen_val,word_val]
  have h:packedGen 5*packedWord 39=1 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem short_word_eq : Atlas.a .s7*Atlas.a .s4*(Atlas.a .s7)⁻¹=word 7 := by
  have hi:(Atlas.a .s7)⁻¹=(Atlas.a .s7)^3 := by
    have h4:(Atlas.a .s7)^4=1 := root_four 6
    calc
      (Atlas.a .s7)⁻¹=(Atlas.a .s7)⁻¹*1 := (mul_one _).symm
      _ = (Atlas.a .s7)⁻¹*(Atlas.a .s7)^4 := congrArg _ h4.symm
      _ = (Atlas.a .s7)^3 := by group
  rw [hi]
  apply Subtype.ext
  simp only [val_mul,val_pow,Atlas.a,atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation,word_val]
  have h:Packed.perm 8*Packed.perm 5*(Packed.perm 8)^3=packedWord 7 := by
    apply Equiv.ext
    apply Atlas1600ParrottData.allFin
    decide +kernel
  simpa [Packed.perm_eq,Packed.generator] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem short_center_generator (j:Fin 6) : Commute (word 7) (gen j) := by
  apply Subtype.ext
  simp only [val_mul,word_val,gen_val]
  have h:∀(j:Fin 6)(k:Fin 1600),
      (packedWord 7*packedGen j) k=(packedGen j*packedWord 7) k := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h j)

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate
