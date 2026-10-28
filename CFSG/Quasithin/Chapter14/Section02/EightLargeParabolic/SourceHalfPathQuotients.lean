module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeReflections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathThicknessSource
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePathProfile

/-!
# Actual mixed-field half-path actors and their canonical quotients

The original source constructs the same full-Cartan reflections with their
six-path root classes, and therefore its six-path apartment geometry. Every
supported twelve-path has an actual half-path actor with quotient SL₂(2)
or SL₂(8), according to the midpoint type. The quotient is the original
covering followed by the intrinsic local quotient; its exact kernel is the
half-path actor's full two-core. The actor supplements the original midpoint
core, and the induced quotient equivalence retains every representative.
No nonsolvability of the binary endpoint, selected geometry, root-class,
local marking, or apartment exchange assumption is supplied.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathQuotients
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- Full original mixed-field geometry and canonical half-actor quotients.
The existential markings and geometry are produced, not extra hypotheses. -/
@[expose] def HasCanonicalHalfPathQuotients (h : HypothesisF11 L S)
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
        ∃ E : (halfPathActor (X := (A).Universal) p 6 ⧸
            pCore 2 (halfPathActor (X := (A).Universal) p 6)) ≃*
              SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
          ∀ x : halfPathActor (X := (A).Universal) p 6,
            E (QuotientGroup.mk' _ x) =
              e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hl x))

private theorem half_path_quotients_of_source_geometry (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (hK : ∀ i, Nat.card (K i)=if i then 8 else 2)
    (e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type))
    (hp : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      BasedPathTransitive (X := (A).Universal) (sourceGraph A) 7 ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=7 →
        Odd (Nat.card (pathFixer (X := (A).Universal) p)))
    (ht : ∃ t : Bool → (A).Universal,
      (∀ i, t i • base UP i=base UP i) ∧
      (∀ i, t i • base UP (!i)≠base UP (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i ∈ normalizer (cartan c : Set (A).Universal)) ∧
      (∀ i, Nonempty (BinarySixPathReflectionClass h i (t i)))) :
    HasCanonicalHalfPathQuotients h c := by
  obtain ⟨t,htfix,htmove,htsq,htnorm,htclass⟩ := ht
  let d : SixPathSmallActorGeometry c :=
    { reflection := t, fixes := htfix, moves := htmove, squares := htsq,
      normalizes := htnorm, transitive := hp.2.1,
      thick := Assembly.BTwoSource.strict_path_thickness_source h t htfix htmove,
      odd := hp.2.2 }
  refine ⟨d,htclass,K,inferInstance,inferInstance,inferInstance,hK,e,?_⟩
  intro a b p hpath hl hT
  have hval' : Nat.card ((sourceGraph A).neighborSet (p.getVert 6)) =
      Nat.card (K ((bOne_tree_cover h).vertex (p.getVert 6)).type)+1 := by
    rw [hval,hK]
    change (if (p.getVert 6).type then 9 else 3)=
      (if (p.getVert 6).type then 8 else 2)+1
    cases (p.getVert 6).type <;> rfl
  exact ⟨source_six_halfPathLinearMap_surjective h c d p hpath hl hT (e _) hval',
    source_six_halfPathLinearMap_kernel h c d p hpath hl hT (e _) hval',
    source_six_halfPathActor_supplement h c d p hpath hl hT (e _) hval',
    sourceSixHalfPathQuotientEquiv h c d p hpath hl hT (e _) hval',
    sourceSixHalfPathQuotientEquiv_apply h c d p hpath hl hT (e _) hval'⟩

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
/-- The original binary/eight source constructs its full mixed-field
apartment geometry and all supported twelve-path canonical half-actor quotients. -/
theorem source_half_path_quotients
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasCanonicalHalfPathQuotients
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  have h : HypothesisF11 Lₛ (T : Subgroup G) :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  have hK (i : Bool) : Nat.card (pathFields i)=if i then 8 else 2 := by
    cases i
    · change Nat.card (ZMod 2)=2
      exact Nat.card_zmod 2
    · change Nat.card (GaloisField 2 3)=8
      rw [GaloisField.card 2 3 (by decide)]
      decide
  let em (v : Vertex (reducedFamily Lₛ (T : Subgroup G))) :=
    (Assembly.linear_graph_quotient h v.type
      (path_field_markings (residualQuotientEquiv H eR) eU v.type) v rfl).some
  exact half_path_quotients_of_source_geometry h c
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    pathFields hK em (source_path_profile hG T hempty hM hu hmany hcard e H hH eR)
    (SourceTreeReflections.source_tree_reflections hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathQuotients
