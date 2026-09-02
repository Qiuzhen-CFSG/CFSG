module
import Stellmacher.SectionFiveToSeven
universe u
namespace Test

def IsSpecial {G : Type u} [Group G] (A : Subgroup G) : Prop :=
  Subgroup.center ↥A = commutator ↥A ∧
    commutator ↥A = frattini ↥A
#check IsSpecial
end Test
