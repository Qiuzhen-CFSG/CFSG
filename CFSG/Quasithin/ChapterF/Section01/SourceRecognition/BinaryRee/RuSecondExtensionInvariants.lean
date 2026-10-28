module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCoreMarking
public import Theory.SpecificGroups.ReeTwo.SylowInvolutionCount

/-!
# The actual middle involution count

The source middle is already isomorphic to the verified full binary Ree
Sylow group. Transport of element order gives the literal count of 143
involutions, preserving the original choices. This is an invariant used to
separate the remaining second-endpoint extension variants in F.1.12/J.4.5.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The actual source middle has precisely 143 involutions. -/
theorem SourceChoice.T_F_involution_card (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card {x : p.T_F B5 // orderOf x=2}=143 := by
  obtain ⟨e⟩:=s.T_F_equiv_sylowModel B5 hi
  let f : {x : p.T_F B5 // orderOf x=2}≃{x : ReeTwo.SylowModel // orderOf x=2} :=
    Equiv.subtypeEquiv e.toEquiv (fun x=>by
      change (orderOf x=2)↔(orderOf (e x)=2)
      exact Iff.of_eq ((congrArg (·=2) (orderOf_injective e.toMonoidHom e.injective x)).symm))
  rw [Nat.card_congr f]
  exact ReeTwo.SylowModel.involution_card

end CFSG.Quasithin.ChapterJ.RuSubgroup
