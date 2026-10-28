module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BIntersections

/-!
# Bases in either four-point candidate for the five-orbit

Each of the two source classes Δ3 and Δ5 meets B in a binary basis.
Explicit four-tuples and their sixteen binary words prove generation
for either choice; this avoids making the disputed printed fusion-label
selection in 13.9.9. The actual normalizer five-orbit therefore spans B.

Source: Aschbacher–Smith 13.9.9, printed p.973.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup

def classBasis (b:Bool) (i:Fin 4) : Parameters :=
  if i=0 then (⟨DihedralGroup.sr 0,by decide⟩,if b then ⟨DihedralGroup.r 2,by decide⟩ else 1)
  else if i=1 then (⟨DihedralGroup.sr 2,by decide⟩,if b then ⟨DihedralGroup.r 2,by decide⟩ else 1)
  else if i=2 then (if b then ⟨DihedralGroup.r 2,by decide⟩ else 1,⟨DihedralGroup.sr 0,by decide⟩)
  else (if b then ⟨DihedralGroup.r 2,by decide⟩ else 1,⟨DihedralGroup.sr 2,by decide⟩)

theorem classBasis_index : ∀b:Bool,∀i:Fin 4,classBasis b i≠1 ∧
    parameterIndex (classBasis b i)=(if b then 4 else 2) := by decide +kernel

def classWord (b:Bool) (e:Fin 4→Fin 2) : Parameters :=
  classBasis b 0^(e 0).val*classBasis b 1^(e 1).val*
    classBasis b 2^(e 2).val*classBasis b 3^(e 3).val

theorem classWord_surjective (b:Bool) : Function.Surjective (classWord b) := by
  cases b <;> decide +kernel

theorem B_class_generates (b:Bool) :
    Subgroup.closure {x:W | x∈B ∧ IsConj (representative (if b then 4 else 2)) x}=B := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (fun _ h=>h.1)
  · intro x hx
    rw [←parametersToW_range] at hx
    obtain ⟨a,rfl⟩:=hx
    obtain ⟨e,rfl⟩:=classWord_surjective b a
    let H:=Subgroup.closure {x:W | x∈B ∧ IsConj (representative (if b then 4 else 2)) x}
    have hgen (i:Fin 4):parametersToW (classBasis b i)∈H := by
      apply Subgroup.subset_closure
      refine ⟨?_,(parameters_class_iff _ _).mpr (classBasis_index b i)⟩
      rw [←parametersToW_range]
      exact ⟨classBasis b i,rfl⟩
    change parametersToW (classWord b e)∈H
    simp only [classWord,map_mul,map_pow]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.pow_mem (hgen 0) _) (H.pow_mem (hgen 1) _))
      (H.pow_mem (hgen 2) _)) (H.pow_mem (hgen 3) _)

end SymmetricFourWreath.InvolutionClasses
