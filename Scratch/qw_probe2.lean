module
import Stellmacher.SectionFiveToSeven
universe u
namespace Test
structure QW {G : Type u} [Group G] (A K : Subgroup G) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  π : A →* X
  surj : Function.Surjective π
  ker_eq : π.ker = K.subgroupOf A

def qImage {G : Type u} [Group G] {A K : Subgroup G} (w : QW A K) (E : Subgroup G) : Subgroup w.X :=
  (E.subgroupOf A).map w.π
end Test
