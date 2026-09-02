module
import Stellmacher.SectionsOneToFourDefs
open scoped Pointwise
example {G : Type*} [Group G] (S H : Subgroup G) : Set G := (S : Set G) * (H : Set G)
example {G : Type*} [Group G] (S H : Subgroup G) : Prop := (S : Set G) * (H : Set G) = (⊤ : Subgroup G)
