module
import Stellmacher.SectionsOneToFourDefs
open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionThree
universe u
variable {G : Type u} [Group G] [Finite G]
variable (P A A0 : Subgroup G) (a x : G)
noncomputable example : Prop :=
  ∃ p n : ℕ, Nat.Prime p ∧ Odd p ∧
    ∃ L : Subgroup G, L = A ⊔ A.conjBy x ∧
      ∃ Ebar Abar : Subgroup (L ⧸ pCore 2 L),
        Nonempty (Ebar ≃* DihedralGroup (p ^ n)) ∧
        Abar = (A0.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ∧
        IsInternalDirectProductFamily (⊤ : Subgroup (L ⧸ pCore 2 L))
          (fun i : Bool => if i then Ebar else Abar)
example : Prop :=
  ∀ e : G, e ∈ A → ∀ y : G, y ∈ A0 → e*y=y*e
end Stellmacher.SectionThree
