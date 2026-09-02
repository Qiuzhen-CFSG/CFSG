module
import Stellmacher.SectionFiveToSeven.Defs
universe u
namespace Test

def QProp {G : Type u} [Group G] (A B : Subgroup G) (p n : ℕ) : Prop :=
  ∃ X : Type u, ∃ gX : Group X, ∃ fX : Finite X,
    (let _ := gX
     let _ := fX
     IsElementaryAbelian p X ∧ Nat.card X = p ^ n ∧
      ∃ f : A →* X, Function.Surjective f ∧ f.ker = B.subgroupOf A)
#check QProp
end Test
