module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorFaithful
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor

/-!
# Faithfulness of every original supported half-path actor

Translate the midpoint by the same literal reflection group to an original
base endpoint. Both original centered cases have trivial full two-core.
Conjugation transports the actual two half-roots and hence their generated
actor, preserving that full-core conclusion for every supported path.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfActorFaithful
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A

/-- Every supported twelve-path actor retains its full trivial two-core. -/
@[expose] def HasFaithfulHalfActors (c:CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∀ d:SixPathSmallActorGeometry c,∀ {a b:SourceVertex A} (p:(sourceGraph A).Walk a b),
    p.IsPath → p.length=12 →
    (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
    pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥

private theorem faithful_of_centered (c:CompatibleCartans L (reducedSylow L S))
    (hbase:∀ d:SixPathSmallActorGeometry c,∀ {a b:SourceVertex A} (p:(sourceGraph A).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
      ∀ i:Bool,p.getVert 6=base F i → pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥) :
    HasFaithfulHalfActors c := by
  intro d a b p hp hl hT
  let N := reflectionGroup c d.reflection
  obtain ⟨g,hg,i,hmid⟩ := hT _ (p.getVert_mem_support 6)
  let f := (translationGraphIso F g⁻¹).toHom
  let q := p.map f
  have hq:q.IsPath := hp.map (MulAction.toPerm g⁻¹).injective
  have hql:q.length=12 := by simpa only [q,Walk.length_map] using hl
  have hqT:∀ z∈q.support,z∈cartanApartment A N := by
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact cartanApartment_preserves A N (N.inv_mem hg) (hT x hx)
  have hqm:q.getVert 6=base F i := by
    simp only [q,Walk.getVert_map,f]
    change g⁻¹ • p.getVert 6=base F i
    rw [←hmid,inv_smul_smul]
  have hzero := hbase d q hq hql hqT i hqm
  let D := halfPathActor (X := (A).Universal) p 6
  let E := halfPathActor (X := (A).Universal) q 6
  have hdrop:(pathRoot (X := (A).Universal) (p.drop 6)).map (MulAut.conj g⁻¹).toMonoidHom=
      pathRoot (X := (A).Universal) (q.drop 6) := by
    apply pathRoot_map_conj (p.drop 6) (q.drop 6) g⁻¹
    · rw [Walk.drop_length,Walk.drop_length,hl,hql]
    · intro k _
      simp only [Walk.drop_getVert,q,Walk.getVert_map,f]
      rfl
  have htake:(pathRoot (X := (A).Universal) (p.take 6)).map (MulAut.conj g⁻¹).toMonoidHom=
      pathRoot (X := (A).Universal) (q.take 6) := by
    apply pathRoot_map_conj (p.take 6) (q.take 6) g⁻¹
    · rw [Walk.take_length,Walk.take_length,hl,hql]
    · intro k _
      simp only [Walk.take_getVert,q,Walk.getVert_map,f]
      rfl
  have hDE:D.map (MulAut.conj g⁻¹).toMonoidHom=E := by
    change (pathRoot (X := (A).Universal) (p.drop 6) ⊔
      pathRoot (X := (A).Universal) (p.take 6)).map (MulAut.conj g⁻¹).toMonoidHom=_
    rw [Subgroup.map_sup,hdrop,htake]
  let e:D≃*E := ((MulAut.conj g⁻¹).subgroupMap D).trans (MulEquiv.subgroupCongr hDE)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso,hzero,Subgroup.map_bot]
end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
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
local notation "Sₛ" => (T : Subgroup G)
set_option maxHeartbeats 800000 in
/-- Both original centered cases imply faithfulness for every supported
half-path actor in every actual reflection geometry. -/
theorem source_half_actor_faithful
    (c:CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) : HasFaithfulHalfActors c := by
  apply faithful_of_centered (L := Lₛ) (S := Sₛ) c
  intro d a b p hp hl hT i hmid
  cases i
  · exact SourceBinaryHalfActorFaithful.source_binary_halfactor_core_eq_bot
      hG T hempty hM hu hmany hcard e H hH eR c d p hp hl hT hmid
  · exact SourceEightHalfActor.centered_eight_core_eq_bot
      hG T hempty hM hu hmany hcard e H hH eR c d p hp hl hT hmid
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfActorFaithful
