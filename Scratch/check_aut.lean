module
import Stellmacher.SectionsOneToFourDefs
open scoped Pointwise BigOperators
open Stellmacher
namespace Stellmacher.SectionTwo
universe u
#check MulAut
#check MulEquiv.toMonoidHom
#check MulEquiv.toMonoidHom
example {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (τ : MulAut S) : Subgroup G := by
  exact (((vSubgroup S).comap (S : Subgroup G).subtype).map (τ : S →* S)).map (S : Subgroup G).subtype
example {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (T : Subgroup (MulAut S)) : Prop := Odd (Nat.card T)
end Stellmacher.SectionTwo
