module

public import Theory.GroupTheory.Amalgam.AutomorphismGroup
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finiteness of the compatible amalgam automorphism group

A compatible automorphism is determined by its three component automorphisms.
For finite local groups this embeds the group into a finite product. This
supports the normal-base extension cardinal comparison in Goldschmidt (1980),
(2.8), without enumerating arbitrary functions.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L D R : Type*} [Group L] [Group D] [Group R]
    (α : RankTwoAmalgam L D R)
instance [Finite L] [Finite D] [Finite R] : Finite (Iso α α) :=
  Finite.of_injective (fun e : Iso α α =>
    ((e.left : MulAut L), (e.middle : MulAut D), (e.right : MulAut R)))
    (by intro e f he
        exact Iso.ext (congrArg Prod.fst he)
          (congrArg (fun x => x.2.1) he) (congrArg (fun x => x.2.2) he))

end Theory.GroupTheory.RankTwoAmalgam
