module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.OddCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry
/-!
# The odd-core branch for the original symplectic pair

The moving Sylow actor places the original elementary image in the central
root plane and makes its opposite pair irreducible, with trivial two-core.
If that pair contains no root element, its odd core is also trivial by the
three-centralizer argument. The source consumer retains the original
component map and the original elementary image throughout.

This discharges the odd-core step of Aschbacher--Smith E.2.7, printed p.220.
The resulting root/no-root split does not identify the pair: coefficient-field
recognition and the all-c₂ classification are separate source obligations.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual moving-actor pair either contains a root element or has both
its two-core and odd core trivial. -/
theorem source_moving_pair_root_or_trivial_cores {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU : V≤unipotent)
    (hV : V.map a.val.toMonoidHom = V) (hr : 2<Nat.card V) :
    V≤(center (unipotent (F := F))).map (unipotent (F := F)).subtype ∧
    Representation.IsIrreducible (pairAction V) ∧ pCore 2 (oppositePair V)=⊥ ∧
    ((∃ g ∈ oppositePair V, IsRootElement g) ∨ pPrimeCore 2 (oppositePair V)=⊥) := by
  obtain ⟨hc,hi,hcore⟩ := source_moving_pair hF hn a ha V hVU hV hr
  refine ⟨hc,hi,hcore,?_⟩
  by_cases hroot : ∃ g ∈ oppositePair V, IsRootElement g
  · exact Or.inl hroot
  · exact Or.inr (oppositePair_oddCore_eq_bot_of_nonroot_central hF V hr
      (CentralRootGeometry.parameter_range (F := F) ▸ hc)
      (fun g hg hr => hroot ⟨g,hg,hr⟩))

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open ChapterB
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Original aligned source geometry, including the odd-core conclusion in
the no-root branch, for the same component inclusion and elementary image. -/
theorem source_geometry_root_or_trivial_cores {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V) :
    let f := L.subtype.comp e.toMonoidHom
    let W := V.comap f
    V≤L ∧ W.map f=V ∧
    W≤(center (unipotent (F := F))).map (unipotent (F := F)).subtype ∧
    Representation.IsIrreducible (pairAction W) ∧ pCore 2 (oppositePair W)=⊥ ∧
    ((∃ g ∈ oppositePair W, IsRootElement g) ∨ pPrimeCore 2 (oppositePair W)=⊥) := by
  dsimp only
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨hVL,hmap,hc,hi,hcore⟩ := source_geometry hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  let j : W →* V := (f.comp W.subtype).codRestrict V (fun x => x.property)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective j (by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : V => (z : G)) h)))
  refine ⟨hVL,hmap,hc,hi,hcore,?_⟩
  by_cases hroot : ∃ g ∈ oppositePair W, IsRootElement g
  · exact Or.inl hroot
  · exact Or.inr (oppositePair_oddCore_eq_bot_of_nonroot_central hF W
      (hcard.symm ▸ hr) (CentralRootGeometry.parameter_range (F := F) ▸ hc)
      (fun g hg hr => hroot ⟨g,hg,hr⟩))

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
