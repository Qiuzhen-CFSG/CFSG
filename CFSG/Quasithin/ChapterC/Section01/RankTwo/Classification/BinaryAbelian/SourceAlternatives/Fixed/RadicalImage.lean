module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.RadicalSeed
public import Theory.GroupTheory.PCoreImage
/-!
# The original radical in the actual binary matrix quotient

The ambient action has kernel exactly O₂(J), contained in R. Consequently
the original proper odd-index subgroup remains proper in the action image,
and the two-core maps to its two-core. This supplies MS2(a) for the literal
image of R in SL₃(2); it does not choose a point or a line parabolic.

Source: Aschbacher–Smith C.1.31(MS2)(a), C.1.34(5), printed pp.135–137.
-/

public section

open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]
namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

theorem ambient_radical_image : MSOddIndexRadical (R.map (q.ambientActor h)) := by
  obtain ⟨H,hH,hodd,hcore⟩ := h.radical
  have hk : (q.ambientActor h).ker ≤ H := by
    rw [q.ambientActor_kernel]
    exact h.radical.twoCore_le.trans (hcore ▸ map_subtype_le (pCore 2 H))
  refine ⟨H.map (q.ambientActor h),lt_top_iff_ne_top.mpr ?_,
    hodd.of_dvd_nat (H.index_map_dvd (q.ambientActor_surjective h)),?_⟩
  · intro he
    have hh := congrArg (fun K => K.comap (q.ambientActor h)) he
    rw [comap_map_eq,sup_of_le_left hk,comap_top] at hh
    exact hH.ne hh
  · have hp : IsPGroup 2 (q.ambientActor h).ker := by
      rw [q.ambientActor_kernel]
      exact pCore_isPGroup
    change (H.map (q.ambientActor h)).pCoreIn 2 = _
    rw [← map_pCoreIn_of_ker_isPGroup (q.ambientActor h) hp]
    exact congrArg (map (q.ambientActor h)) hcore

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS
