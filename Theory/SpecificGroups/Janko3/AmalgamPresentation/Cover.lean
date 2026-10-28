module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Checked
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape

/-!
# A relation-derived cover of the universal rank-three J₃ amalgam

The 18468 representatives come with actual first-local-subgroup witnesses for
both signs of each of the six defining generators. They therefore cover the
abstract relation carrier, independently of any finite model or faithful action.
-/

namespace Sporadic.Janko3.AmalgamPresentation
namespace Cover
open Subgroup.CosetWordCertificate

private theorem transitions (i : Fin 18468) (a : Fin 12) :
    Holds firstLocal generator (definitions.repr generator)
      ⟨i.val, [decode a.val], (destination (12*i.val+a.val)).val⟩ := by
  have hs := all_shapes (12*i.val+a.val) (by omega)
  have hp : Path.refCheck context decode 1479202 (outputCode (12*i.val+a.val)) = true ∧
      factBEq (outputData (12*i.val+a.val))
        ⟨(12*i.val+a.val)/12,[decode ((12*i.val+a.val)%12)],
          (destination (12*i.val+a.val)).val⟩ = true := by
    simpa only [shapeAt, Bool.and_eq_true] using hs
  have he := (factBEq_eq_true_iff _ _).mp hp.2
  have hd : (12*i.val+a.val) / 12 = i.val := by omega
  have hm : (12*i.val+a.val) % 12 = a.val := by omega
  rw [hd,hm] at he
  rw [← he]
  exact Path.refCheck_sound context_valid decode facts 1479202 _ all_hold hp.1

end Cover
open Cover Subgroup.CosetWordCertificate

/-- Every marked generator and its inverse preserve the actual coset cover. -/
public def firstLocalCover :
    Subgroup.GeneratorCosetCover firstLocal generator (Fin 18468) where
  repr i := definitions.repr generator i.val
  initial := 0
  initial_eq := definitions.repr_zero generator
  step i a := by
    obtain ⟨h,hh⟩ := transitions i ⟨2*a.val,by omega⟩
    refine ⟨h,destination (12*i.val+2*a.val),?_⟩
    have hd : decode (2*a.val) = (a,true) := by
      apply Prod.ext
      · apply Fin.ext
        change (2*a.val)/2%6=a.val
        omega
      · simp [decode]
    simpa only [hd,eval_letter,Bool.false_eq_true,↓reduceIte] using hh
  inv_step i a := by
    obtain ⟨h,hh⟩ := transitions i ⟨2*a.val+1,by omega⟩
    refine ⟨h,destination (12*i.val+(2*a.val+1)),?_⟩
    have hd : decode (2*a.val+1) = (a,false) := by
      apply Prod.ext
      · apply Fin.ext
        change (2*a.val+1)/2%6=a.val
        omega
      · simp [decode]
    simpa only [hd,eval_letter,Bool.false_eq_true,↓reduceIte] using hh

/-- This is a genuine finite-index statement for the abstract presentation. -/
public theorem firstLocal_finiteIndex : firstLocal.FiniteIndex :=
  ⟨(firstLocalCover.index_pos generator_generates).ne'⟩

/-- The literal first local subgroup has at most 18468 cosets. -/
public theorem firstLocal_index_le : firstLocal.index ≤ 18468 := by
  simpa using firstLocalCover.index_le_card generator_generates

end Sporadic.Janko3.AmalgamPresentation
