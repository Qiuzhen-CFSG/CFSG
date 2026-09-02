module
import Stellmacher.SectionFiveToSeven.Defs
open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
universe u
variable {G : Type u} [Group G] [Finite G]
example (P Q A : Subgroup G) : Prop :=
  Nonempty (((P ⧸ (P ⊓ Q).subgroupOf P) ≃*
    (DihedralGroup 3 × (A ⧸ (A ⊓ Q).subgroupOf A))))
end Stellmacher.SectionsFiveToSeven
