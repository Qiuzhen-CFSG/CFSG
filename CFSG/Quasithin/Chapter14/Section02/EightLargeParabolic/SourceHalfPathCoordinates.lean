module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorRootCoordinates
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCentralizer

/-!
# Opposite roots on the original mixed-field half-path actors

For the same source reflections, root classes and original quotient markings,
every supported twelve-path retains its canonical full two-core kernel,
supplement and representative formula. Both actual half-radicals inject into
that quotient, and a single inner change places them in the full opposite
unipotent groups. The full Cartan centralizer is its intersection with the
complete midpoint permutation kernel. At binary midpoints the whole Cartan
centralizes the half-path actor. No selected geometry or marking is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathCoordinates
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceHalfPathQuotients
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The same actual geometry, quotient markings and intrinsic root classes,
with opposite radical coordinates and the full Cartan centralizer calculation. -/
@[expose] def HasCoordinatizedHalfPathQuotients (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∃ d : SixPathSmallActorGeometry c,
    (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i)=if i then 8 else 2) ∧
      ∃ e : ∀ v : Vertex F,
        (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
      ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=12),
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) →
        Function.Surjective (halfPathLinearMap h p 6 hl
          (e ((bOne_tree_cover h).vertex (p.getVert 6)))) ∧
        (halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))).ker =
          pCore 2 (halfPathActor (X := (A).Universal) p 6) ∧
        (halfPathActor (X := (A).Universal) p 6).map (bOne_tree_map h) ⊔
          Q F ((bOne_tree_cover h).vertex (p.getVert 6)) =
            graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ∧
        (∃ E : (halfPathActor (X := (A).Universal) p 6 ⧸
            pCore 2 (halfPathActor (X := (A).Universal) p 6)) ≃*
              SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
          ∀ x : halfPathActor (X := (A).Universal) p 6,
            E (QuotientGroup.mk' _ x) =
              e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hl x))) ∧
        (let D := halfPathActor (X := (A).Universal) p 6
         let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
         let V := (pathRoot (X := (A).Universal) (p.take 6)).subgroupOf D
         let f := halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))
         R ⊓ f.ker=⊥ ∧ V ⊓ f.ker=⊥ ∧
           ∃ z : SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
             R.map ((MulAut.conj z).toMonoidHom.comp f)=
               Matrix.SpecialLinearGroup.upperUnipotent _ ∧
             ∀ y, y∈V.map ((MulAut.conj z).toMonoidHom.comp f) ↔
               ∃ a, Matrix.SpecialLinearGroup.transvection
                 (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) ∧
        cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
          cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) ∧
        ((p.getVert 6).type=false →
          cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal))

private theorem coordinates_of_canonical_quotients (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hq : HasCanonicalHalfPathQuotients h c) : HasCoordinatizedHalfPathQuotients h c := by
  obtain ⟨d,hclass,K,hfield,hfinite,hchar,hK,e,hpaths⟩ := hq
  let _ := hfield
  let _ := hfinite
  let _ := hchar
  refine ⟨d,hclass,K,hfield,hfinite,hchar,hK,e,?_⟩
  intro a b p hp hl hT
  obtain ⟨hsurj,hker,hsupp,hE⟩ := hpaths p hp hl hT
  have hval' : Nat.card ((sourceGraph A).neighborSet (p.getVert 6)) =
      Nat.card (K ((bOne_tree_cover h).vertex (p.getVert 6)).type)+1 := by
    rw [hval,hK]
    change (if (p.getVert 6).type then 9 else 3)=
      (if (p.getVert 6).type then 8 else 2)+1
    cases (p.getVert 6).type <;> rfl
  exact ⟨hsurj,hker,hsupp,hE,
    source_six_root_coordinates h c d p hp hl hT (e _) hval',
    Assembly.BTwoSource.six_actor_cartan_centralizer h c d p hp hl hT,
    SourceBinaryCartan.binary_halfactor_centralization h c hC hval d p hp hl hT⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]

set_option maxHeartbeats 800000 in
/-- The original source produces opposite root coordinates and the exact
full local-kernel Cartan centralizer on every supported twelve-path, using
one simultaneous choice of reflections, fields and local quotient markings. -/
theorem source_half_path_coordinates
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasCoordinatizedHalfPathQuotients
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact coordinates_of_canonical_quotients _ c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (source_half_path_quotients hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathCoordinates
