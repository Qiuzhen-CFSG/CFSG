module
import Stellmacher.SectionsOneToFourDefs
open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionThree
universe u
variable {G : Type u} [Group G] [Finite G]
variable (P : Subgroup G) (S : Subgroup G) (P0 : Subgroup P)
example : Prop := ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧
  IsPGroup p (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
example : Prop :=
  P0.map (QuotientGroup.mk' (pCore 2 P)) =
    frattiniAmbient (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
example : Prop := IsIrreducibleSection (S.subgroupOf P) P0 (twoResidualSubgroup P)
end Stellmacher.SectionThree
