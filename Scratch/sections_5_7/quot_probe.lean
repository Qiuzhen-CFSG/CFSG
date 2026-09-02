module
import Stellmacher.SectionFiveToSeven.Defs
open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
universe u
variable {G : Type u} [Group G] [Finite G]
example (P : Subgroup G) : Prop :=
  ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n))
end Stellmacher.SectionsFiveToSeven
