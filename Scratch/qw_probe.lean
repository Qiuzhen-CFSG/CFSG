module
import Stellmacher.SectionFiveToSeven.Defs
universe u
namespace Test
structure QW {G : Type u} [Group G] (A K : Subgroup G) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  π : A →* X
  surj : Function.Surjective π
  ker_eq : π.ker = K.subgroupOf A

#check QW
#check QW.groupX

def QI {G : Type u} [Group G] (A K : Subgroup G) : Prop := Nonempty (QW A K)

def QElem {G : Type u} [Group G] (A K : Subgroup G) (p n : ℕ) : Prop :=
  ∃ w : QW A K,
    (let _ := w.groupX
     let _ := w.finiteX
     IsElementaryAbelian p w.X ∧ Nat.card w.X = p^n)
end Test
