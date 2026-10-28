module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import Theory.GroupTheory.WeakBNPair.RegularTree.ActorCover
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRootCover
public import Theory.GroupTheory.PGroup.Omega

/-!
# The prescribed six-path reflection class

The additional choice in DGS (14.2) is conjugacy inside the actual local
actor to an involution of the radical of a genuine long path. For the
binary six-path branch, retain that path and both elements of the actor.
The path need not be the path later constructed from the chosen reflections.
Its radical is literally the two-core of its complete pointwise stabilizer.

The universal-to-reduced cover preserves this radical and is injective on
the marked actor. Hence the involution, its order and its actor conjugator
all transport through the original map. The final consumer carries a proved
normal-subgroup class for this path radical to the selected reflection.
For example, a native alpha-root derived-group calculation can use this
consumer without substituting the full endpoint for its local actor.

This records and transports the source choice; it does not construct that
choice from F.1.11 or infer central cube membership from second-ball fixation.
Source: DGS, Groups and Graphs (1985), (14.1)--(14.2), printed pp.210--211,
and the binary reflection calculation in (14.17), printed pp.222--223.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal local actor pulled back within its marked universal endpoint. -/
abbrev sixPathReflectionActor (h : HypothesisF11 L S) (i : Bool) :=
  coveredActor (F := Universal.cosetFamily (reducedAmalgam L S))
    (f := bOne_tree_map h)
    (graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) i)) i

/-- Restriction of the original cover to the same source local actor. -/
def sixPathReflectionActorEquiv (h : HypothesisF11 L S) (i : Bool) :
    sixPathReflectionActor h i ≃*
      graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) i) :=
  coveredActorEquiv (bOne_tree_cover h) _ i (by
    simpa only [graphLocalGroup,RankTwo.stabilizer,stabilizer_base] using
      Theory.GroupTheory.AmalgamGraph.sylowGenerated_le
        (RankTwo.stabilizer (reducedFamily L S) (RankTwo.base (reducedFamily L S) i)))

/-- The precise root-conjugacy choice in the binary `r=6` branch of (14.2).
This is additional data for a selected reflection, not a consequence of its
fixation, movement, involution and Cartan-normalization properties. -/
structure BinarySixPathReflectionClass (h : HypothesisF11 L S) (i : Bool)
    (t : (reducedAmalgam L S).Universal) where
  start : RankTwo.Vertex (Universal.cosetFamily (reducedAmalgam L S))
  path : (RankTwo.graph (Universal.cosetFamily (reducedAmalgam L S))).Walk start
    (base (Universal.cosetFamily (reducedAmalgam L S)) i)
  isPath : path.IsPath
  length_eq : path.length = 6
  previous : path.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
  root : sixPathReflectionActor h i
  root_mem : (root : (reducedAmalgam L S).Universal) ∈
    pathRoot (X := (reducedAmalgam L S).Universal) path
  root_order : orderOf (root : (reducedAmalgam L S).Universal) = 2
  conjugator : sixPathReflectionActor h i
  conjugates : (conjugator : (reducedAmalgam L S).Universal) * root *
    (conjugator : (reducedAmalgam L S).Universal)⁻¹ = t

namespace BinarySixPathReflectionClass
variable {h : HypothesisF11 L S} {i : Bool} {t : (reducedAmalgam L S).Universal}
  (d : BinarySixPathReflectionClass h i t)

/-- The involution witness lies in exactly the first omega subgroup specified
in (14.2), embedded from the actual path radical. -/
theorem root_mem_omega :
    (d.root : (reducedAmalgam L S).Universal) ∈
      (omega₁ (pathRoot (X := (reducedAmalgam L S).Universal) d.path) (p := 2)).map
        (pathRoot (X := (reducedAmalgam L S).Universal) d.path).subtype := by
  apply mem_map_of_mem _
    (show (⟨d.root,d.root_mem⟩ : pathRoot (X := (reducedAmalgam L S).Universal) d.path) ∈
      omega₁ _ (p := 2) from ?_)
  apply Subgroup.subset_closure
  apply Subtype.ext
  change (d.root : (reducedAmalgam L S).Universal) ^ (2 ^ 1) = 1
  simpa only [pow_one,d.root_order] using
    pow_orderOf_eq_one (d.root : (reducedAmalgam L S).Universal)

include d in
/-- The selected reflection is in the same local actor as its root and
conjugator. No enlargement to the full marked endpoint is used. -/
theorem mem_actor : t ∈ sixPathReflectionActor h i := by
  rw [← d.conjugates]
  exact (sixPathReflectionActor h i).mul_mem
    ((sixPathReflectionActor h i).mul_mem d.conjugator.property d.root.property)
    ((sixPathReflectionActor h i).inv_mem d.conjugator.property)

/-- The literal reduced map preserves the root involution and its conjugacy
inside the original source actor, on the image of the same genuine path. -/
theorem reduced_clauses :
    ∃ y ∈ pathRoot (X := G₀ L S) (d.path.map (bOne_tree_cover h).hom),
      orderOf y = 2 ∧
      y ∈ graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) i) ∧
      ∃ g ∈ graphLocalGroup (reducedFamily L S) (RankTwo.base (reducedFamily L S) i),
        g * y * g⁻¹ = bOne_tree_map h t := by
  let e := sixPathReflectionActorEquiv h i
  have he (a : sixPathReflectionActor h i) :
      (e a : G₀ L S) = bOne_tree_map h a := rfl
  refine ⟨bOne_tree_map h d.root,?_,?_,d.root.property.1,
    bOne_tree_map h d.conjugator,d.conjugator.property.1,?_⟩
  · rw [← (bOne_tree_cover h).pathRoot_map d.path]
    exact mem_map_of_mem _ d.root_mem
  · rw [← he,Subgroup.orderOf_coe,e.orderOf_eq,← Subgroup.orderOf_coe]
    exact d.root_order
  · simpa only [map_mul,map_inv] using congrArg (bOne_tree_map h) d.conjugates

/-- A model calculation on the chosen path radical transfers its
normal-subgroup class to the prescribed reflection. The homomorphism can
be the universal map supplied by a marked native amalgam comparison. -/
theorem image_mem_normal_of_root {Y : Type*} [Group Y]
    (φ : (reducedAmalgam L S).Universal →* Y)
    (N : Subgroup Y) [N.Normal]
    (hy : φ d.root ∈ N) : φ t ∈ N := by
  have hh := (inferInstance : N.Normal).conj_mem
    (φ d.root) hy (φ d.conjugator)
  simpa only [← map_inv,← map_mul,d.conjugates] using hh

/-- A normal-subgroup class for the whole chosen path radical supplies the
witness-level premise for the prescribed reflection. -/
theorem image_mem_normal {Y : Type*} [Group Y]
    (φ : (reducedAmalgam L S).Universal →* Y)
    (N : Subgroup Y) [N.Normal]
    (hroot : (pathRoot (X := (reducedAmalgam L S).Universal) d.path).map
      φ ≤ N) : φ t ∈ N :=
  d.image_mem_normal_of_root φ N (hroot (mem_map_of_mem φ d.root_mem))

/-- Source-facing application on the literal reduced image of the same path.
The separate path-root class premise remains visible for its producer. -/
theorem reduced_image_mem_normal {Y : Type*} [Group Y] (φ : G₀ L S →* Y)
    (N : Subgroup Y) [N.Normal]
    (hroot : (pathRoot (X := G₀ L S) (d.path.map (bOne_tree_cover h).hom)).map φ ≤ N) :
    φ (bOne_tree_map h t) ∈ N := by
  apply d.image_mem_normal (φ.comp (bOne_tree_map h)) N
  rw [← Subgroup.map_map,(bOne_tree_cover h).pathRoot_map]
  exact hroot

end BinarySixPathReflectionClass
end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
