module
import Stellmacher.SectionFiveToSeven.Defs
open Stellmacher Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
#check Sylow
#check stabilizer
#check (fun {G : Type} [Group G] [Finite G] {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) (d : Γ.Vertex) => stabilizer Γ d)
#check (fun {G : Type} [Group G] [Finite G] {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex) => (stabilizer Γ d ⊓ stabilizer Γ l))
#check (fun {G : Type} [Group G] [Finite G] {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex) => Sylow 2 (stabilizer Γ d ⊓ stabilizer Γ l))
