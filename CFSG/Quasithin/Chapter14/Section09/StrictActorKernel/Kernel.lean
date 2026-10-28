module
public import CFSG.Quasithin.Chapter14.Section09.StrictActorKernel.Cartan

/-!
# The exact strict actor kernel under the source covering

Restrict the same midpoint quotient to the literal two-root actor. Its kernel
maps to the intersection of that actor image with the original endpoint core,
not to an independently chosen subgroup. The Cartan calculation further puts
this intersection in the centralizer of the full Cartan neighborhood kernel.
This is a constraint on the actual kernel needed in DGS (14.9)(c); equality
with the source Z_i and its natural action remain to be proved.

Source: DGS, *Groups and Graphs* (1985), (14.5)(b) and (14.9)(c),
printed pp.213,215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
variable (h : HypothesisF11 L S)
variable {a b : SourceVertex (reducedAmalgam L S)} (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (n : ℕ) (hl : p.length=2*n)
    {k : Type*} [Field k]
    (e : (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert n)))) ≃* SL(2,k))

/-- The original covering sends the actual quotient kernel exactly to the
intersection with the source endpoint core, on every even path. -/
theorem halfPath_kernel_image :
    ((halfPathLinearMap h p n hl e).ker.map
      (halfPathActor (X := (A).Universal) p n).subtype).map (bOne_tree_map h) =
    (halfPathActor (X := (A).Universal) p n).map (bOne_tree_map h) ⊓
      Q F ((bOne_tree_cover h).vertex (p.getVert n)) := by
  let D := halfPathActor (X := (A).Universal) p n
  let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert n))
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hJ : (pCore 2 J).map J.subtype =
      Q F ((bOne_tree_cover h).vertex (p.getVert n)) := sylowGenerated_core _
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨mem_map_of_mem _ z.property,?_⟩
    rw [halfPathLinearMap_kernel] at hz
    rw [←hJ]
    change halfPathLocalMap h p n hl z ∈ pCore 2 J at hz
    exact mem_map_of_mem J.subtype hz
  · rintro ⟨⟨y,hy,rfl⟩,hyQ⟩
    refine ⟨y,⟨⟨y,hy⟩,?_,rfl⟩,rfl⟩
    rw [halfPathLinearMap_kernel]
    change halfPathLocalMap h p n hl ⟨y,hy⟩ ∈ pCore 2 J
    rw [←hJ] at hyQ
    exact (mem_map_iff_mem J.subtype_injective).mp hyQ

variable (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection))

include hp hlen hT in
/-- DGS (14.5)(b) constrains the literal smaller actor core, downstairs
under the original covering, by the full Cartan neighborhood kernel. -/
theorem six_actor_core_image_le_centralizer :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h) ≤
      centralizer (((cartan c).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 6)) : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro y ⟨⟨z,hz,rfl⟩,hzU⟩
  have hzC : z∈centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) := by
    have hm : z∈cartan c ⊓
        (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) := ⟨hz,hzU⟩
    rw [←six_cartan_actor_centralizer h c d p hp hlen hT] at hm
    exact hm.2
  have he := mem_centralizer_iff.mp hzC x (pCoreIn_le 2 _ hx)
  simpa only [map_mul] using congrArg (bOne_tree_map h) he.symm

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
