module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceOddCore

/-!
# The simple-socle branch of the original symplectic source pair

The original moving Sylow actor gives the same elementary image, central
root-plane placement, irreducible opposition pair, and trivial two-core.
If the pair has no root element, its odd core vanishes and all involution
centralizers are two-groups. The generic component argument makes its
actual generalized Fitting subgroup simple.

The aligned source theorem retains the component map and the original
pullback throughout. It discharges the simple-socle reduction in
Aschbacher--Smith E.2.7, printed p.220. Recognition of that simple socle
and its coefficient field remain separate obligations.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The moving-actor opposition pair either contains a root element or has
a simple actual generalized Fitting subgroup. -/
theorem source_moving_pair_root_or_simple_socle {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V] (hVU : V≤unipotent)
    (hV : V.map a.val.toMonoidHom = V) (hr : 2<Nat.card V) :
    V≤(center (unipotent (F := F))).map (unipotent (F := F)).subtype ∧
    Representation.IsIrreducible (pairAction V) ∧ pCore 2 (oppositePair V)=⊥ ∧
    ((∃ g ∈ oppositePair V, IsRootElement g) ∨
      IsSimpleGroup (Theory.GroupTheory.generalizedFitting (oppositePair V))) := by
  obtain ⟨hc,hi,hcore,_⟩ := source_moving_pair_root_or_trivial_cores hF hn a ha V hVU hV hr
  refine ⟨hc,hi,hcore,?_⟩
  by_cases hroot : ∃ g ∈ oppositePair V, IsRootElement g
  · exact Or.inl hroot
  · exact Or.inr (oppositePair_generalizedFitting_simple_of_nonroot_central hF V hr
      (CentralRootGeometry.parameter_range (F := F) ▸ hc) hcore
      (fun g hg h => hroot ⟨g,hg,h⟩))
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open ChapterB
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The literal E.2.7 pullback pair has a root element or a simple socle,
with the original component inclusion and elementary image retained. -/
theorem source_geometry_root_or_simple_socle {n : ℕ}
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
    ((∃ g ∈ oppositePair W, IsRootElement g) ∨
      IsSimpleGroup (Theory.GroupTheory.generalizedFitting (oppositePair W))) := by
  dsimp only
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨hVL,hmap,hc,hi,hcore,_⟩ := source_geometry_root_or_trivial_cores hF hn T hP hJ L e hmark
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
  · exact Or.inr (oppositePair_generalizedFitting_simple_of_nonroot_central hF W
      (hcard.symm ▸ hr) (CentralRootGeometry.parameter_range (F := F) ▸ hc) hcore
      (fun g hg h => hroot ⟨g,hg,h⟩))

/-- In the original source geometry, root avoidance gives a simple F*
without any additional component or centralizer hypothesis. -/
theorem source_geometry_nonroot_simple_socle {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hnr : ∀ g ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      ¬IsRootElement g) :
    IsSimpleGroup (Theory.GroupTheory.generalizedFitting
      (oppositePair (V.comap (L.subtype.comp e.toMonoidHom)))) := by
  obtain ⟨_,_,_,_,_,hc⟩ := source_geometry_root_or_simple_socle hF hn T hP hJ L e hmark
    hgen V hVT hVM hVN hr
  exact hc.resolve_left (by rintro ⟨g,hg,hr⟩; exact hnr g hg hr)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
