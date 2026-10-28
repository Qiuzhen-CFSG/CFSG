module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block00
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block01
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block02
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block03
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block04
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block05
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block06
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block07
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block08
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block09
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block10
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Block11
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Lower

/-! Assembly of the projective transfer tables. -/

public section
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4
theorem raw0Step (i:Fin 4)(r:Fin 300) :
    (raw0Gen i).mul (raw0Rep r) =
      (raw0Rep (L0Act i r)).mul (evalRaw raw1Gen (L0Factor i r)) ∨
    (raw0Gen i).mul (raw0Rep r) =
      ((raw0Rep (L0Act i r)).mul (evalRaw raw1Gen (L0Factor i r))).neg := by
  have hh (b:Fin 12)(j:Fin 25) :
      (raw0Gen i).mul (raw0Rep ⟨25*b.val+j.val,by omega⟩) =
        (raw0Rep (L0Act i ⟨25*b.val+j.val,by omega⟩)).mul (evalRaw raw1Gen (L0Factor i ⟨25*b.val+j.val,by omega⟩)) ∨
      (raw0Gen i).mul (raw0Rep ⟨25*b.val+j.val,by omega⟩) =
        ((raw0Rep (L0Act i ⟨25*b.val+j.val,by omega⟩)).mul (evalRaw raw1Gen (L0Factor i ⟨25*b.val+j.val,by omega⟩))).neg := by
    fin_cases b
    · exact raw0Block0 i j
    · exact raw0Block1 i j
    · exact raw0Block2 i j
    · exact raw0Block3 i j
    · exact raw0Block4 i j
    · exact raw0Block5 i j
    · exact raw0Block6 i j
    · exact raw0Block7 i j
    · exact raw0Block8 i j
    · exact raw0Block9 i j
    · exact raw0Block10 i j
    · exact raw0Block11 i j
  let b : Fin 12 := ⟨r.val/25,by omega⟩
  let j : Fin 25 := ⟨r.val%25,Nat.mod_lt _ (by decide)⟩
  have he : (⟨25*b.val+j.val,by omega⟩:Fin 300)=r := by
    apply Fin.ext
    dsimp [b,j]
    omega
  simpa only [he] using hh b j
end Tits.Max4Projective
