module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Subgroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Radical.Defs

/-!
# Exact local conclusions needed in the exterior branch

These are output contracts, not added assumptions in Hypothesis 12.2.3.
The parabolic P is the inverse image of the standard first-node minimal
parabolic under the actual actor on LT. The component alternatives retain
relative normality in Gᵢ, actual quotient models and the original Ξ₇ row.
The exceptional product is written as a join; Ξ₇(K) is characteristic in K.

Source: Aschbacher--Smith, 12.5.3 and its preceding notation, pp.817--819.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace SylowExteriorMarking
/-- The first-node parabolic: all natural flag spaces except Γ₁ are fixed. -/
def P (s : SylowExteriorMarking D) : Subgroup G :=
  ((⨅ (k : Fin 5) (_ : k.val ≠ 1), Representation.SL5ExteriorSquare.parabolic k.val).comap
    s.actor).map (L ⊔ (T : Subgroup G)).subtype

/-- The literal embedded two-residual O²(P), not its two-core. -/
def Y (s : SylowExteriorMarking D) : Subgroup G :=
  (pResidual 2 s.P).map s.P.subtype
end SylowExteriorMarking

/-- The four normalizers in source 12.5.3. -/
def LocalIndex (i : ℕ) : Prop := i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6

/-- The three original alternatives; every model refers to the actual K/O₂(K). -/
inductive LocalComponentAlternative (s : SylowExteriorMarking D) (i : ℕ)
    (K : Subgroup G) : Prop
  | equal (eq : s.marking.Li i = K)
  | large (index : i = 1)
      (model : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
      (residual_le : s.Y ≤ K)
  | radical (index : i = 1)
      (product : K = Chapter1.XiP 7 K ⊔ s.marking.Li 1)
      (model : HasExtension (K ⧸ pCore 2 K) (ElementaryModel 7 2)
        (fun X _ => IsSL X 2 7))

/-- The conclusion of 12.5.3, with all embeddings and normality relative to Gᵢ. -/
structure LocalComponents (s : SylowExteriorMarking D) where
  K : ℕ → Subgroup G
  contains : ∀ i, LocalIndex i → s.marking.Li i ≤ K i
  component : ∀ i, LocalIndex i → K i ∈ Chapter1.cComponentsIn (s.marking.Gi i)
  normal : ∀ i, LocalIndex i → ((K i).subgroupOf (s.marking.Gi i)).Normal
  alternative : ∀ i, LocalIndex i → LocalComponentAlternative s i (K i)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
