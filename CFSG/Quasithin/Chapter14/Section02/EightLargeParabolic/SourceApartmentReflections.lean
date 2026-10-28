module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCorrectedGeometry
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionPlacement
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightCenteredReflection

/-!
# Actual reversing reflections in every apartment half-path actor

The corrected original source geometry supplies both centered reflections.
Transport along its same Cartan apartment places a reversing element in the
literal half-path actor of every supported twelve-path.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentReflections
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S

private theorem reflections_of_centered (c:CompatibleCartans L (reducedSylow L S))
    (d:SixPathSmallActorGeometry c)
    (hbase:∀ {a b:SourceVertex A} (p:(sourceGraph A).Walk a b),p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
      ∀ i:Bool,p.getVert 6=base (Universal.cosetFamily A) i →
      ∃ x∈halfPathActor (X := (A).Universal) p 6,∀ k≤12,x • p.getVert k=p.getVert (12-k)) :
    ∀ {a b:SourceVertex A} (p:(sourceGraph A).Walk a b),p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
      ∃ x∈halfPathActor (X := (A).Universal) p 6,∀ k≤12,x • p.getVert k=p.getVert (12-k) := by
  intro a b p hp hl hT
  let N := reflectionGroup c d.reflection
  let U := Universal.cosetFamily A
  obtain ⟨g,hg,i,hmid⟩ := hT _ (p.getVert_mem_support 6)
  let f := (Subgroup.CosetGeometry.translationGraphIso U g⁻¹).toHom
  let q := p.map f
  have hq:q.IsPath := hp.map (MulAction.toPerm g⁻¹).injective
  have hql:q.length=12 := by simpa only [q,Walk.length_map] using hl
  have hqT:∀ z∈q.support,z∈cartanApartment A N := by
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact cartanApartment_preserves A N (N.inv_mem hg) (hT x hx)
  have hqv (k:ℕ):q.getVert k=g⁻¹ • p.getVert k := by
    simp only [q,Walk.getVert_map,f]
    rfl
  have hqm:q.getVert 6=base U i := by rw [hqv,←hmid,inv_smul_smul]
  obtain ⟨x,hx,hrev⟩ := hbase q hq hql hqT i hqm
  let D := halfPathActor (X := (A).Universal) p 6
  let E := halfPathActor (X := (A).Universal) q 6
  have hdrop:(pathRoot (X := (A).Universal) (p.drop 6)).map (MulAut.conj g⁻¹).toMonoidHom=
      pathRoot (X := (A).Universal) (q.drop 6) := by
    apply pathRoot_map_conj (p.drop 6) (q.drop 6) g⁻¹
    · rw [Walk.drop_length,Walk.drop_length,hl,hql]
    · intro k _
      rw [Walk.drop_getVert,Walk.drop_getVert,hqv]
  have htake:(pathRoot (X := (A).Universal) (p.take 6)).map (MulAut.conj g⁻¹).toMonoidHom=
      pathRoot (X := (A).Universal) (q.take 6) := by
    apply pathRoot_map_conj (p.take 6) (q.take 6) g⁻¹
    · rw [Walk.take_length,Walk.take_length,hl,hql]
    · intro k _
      rw [Walk.take_getVert,Walk.take_getVert,hqv]
  have hDE:D.map (MulAut.conj g⁻¹).toMonoidHom=E := by
    change (pathRoot (X := (A).Universal) (p.drop 6)⊔pathRoot (X := (A).Universal) (p.take 6)).map _=_
    rw [Subgroup.map_sup,hdrop,htake]
  have hx':x∈D.map (MulAut.conj g⁻¹).toMonoidHom := hDE.symm ▸ hx
  obtain ⟨y,hy,hyx⟩ := hx'
  refine ⟨y,hy,?_⟩
  intro k hk
  have hh := hrev k hk
  rw [hqv,hqv,←hyx] at hh
  change (g⁻¹*y*(g⁻¹)⁻¹) • (g⁻¹ • p.getVert k)=g⁻¹ • p.getVert (12-k) at hh
  simpa only [mul_smul,inv_smul_smul,smul_inv_smul] using congrArg (g • ·) hh


private theorem assemble (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hcorrect : SourceEightCorrectedGeometry.HasCorrectedEightGeometry h c)
    (hpaths : ∀ d : SixPathSmallActorGeometry c,
      let P := stabilizer (Universal.cosetFamily A) (base (Universal.cosetFamily A) true)
      let K := pathRoot (X := (A).Universal)
        (reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true).walk ⊔
          zpowers (d.reflection true)
      K≤P → (pCore 2 P).IsComplement' (K.subgroupOf P) →
      ∀ {a b : SourceVertex A} (p : (sourceGraph A).Walk a b),p.IsPath → p.length=12 →
        (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
        ∃ x∈halfPathActor (X := (A).Universal) p 6,
          ∀ k≤12,x•p.getVert k=p.getVert (12-k)) :
    ∃ d : SixPathSmallActorGeometry c,
      ∀ {a b : SourceVertex A} (p : (sourceGraph A).Walk a b),p.IsPath → p.length=12 →
        (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) →
        ∃ x∈halfPathActor (X := (A).Universal) p 6,
          ∀ k≤12,x•p.getVert k=p.getVert (12-k) := by
  obtain ⟨d,_,hKP,_,hcomp,_⟩ := hcorrect
  exact ⟨d,hpaths d hKP hcomp⟩

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
local notation "Fₛ" => reducedFamily Lₛ Sₛ

local notation "Aₛ" => reducedAmalgam Lₛ Sₛ

set_option maxHeartbeats 800000 in
private theorem source_reflections_of_eight_centered
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) (d : SixPathSmallActorGeometry c)
    (height : ∀ {a b : SourceVertex Aₛ} (p : (sourceGraph Aₛ).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment Aₛ (reflectionGroup c d.reflection)) →
      p.getVert 6=base (Universal.cosetFamily Aₛ) true →
      d.reflection true∈halfPathActor (X := (Aₛ).Universal) p 6) :
    ∀ {a b : SourceVertex Aₛ} (p : (sourceGraph Aₛ).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support,z∈cartanApartment Aₛ (reflectionGroup c d.reflection)) →
      ∃ x∈halfPathActor (X := (Aₛ).Universal) p 6,
        ∀ k≤12,x•p.getVert k=p.getVert (12-k) := by
  apply reflections_of_centered c d
  intro a b p hp hl hT i hm
  have hrev := SourceEightCenteredReflection.centered_reflection_reverses c d p hp hl hT i hm
  cases i with
  | false =>
    exact ⟨d.reflection false,
      SourceBinaryReflectionPlacement.source_binary_reflection_mem_halfactor
        hG T hempty hM hu hmany hcard e H hH eR c d p hp hl hT hm
        (d.reflection false) (d.squares false) (d.normalizes false) hrev,hrev⟩
  | true => exact ⟨d.reflection true,height p hp hl hT hm,hrev⟩

set_option maxHeartbeats 800000 in
/-- The original mixed source constructs one actual geometry whose every
supported twelve-path has a reversing element in its full half-path actor. -/
theorem source_apartment_reflections
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    ∃ d : SixPathSmallActorGeometry c,
      ∀ {a b : SourceVertex Aₛ} (p : (sourceGraph Aₛ).Walk a b),
        p.IsPath → p.length=12 →
        (∀ z∈p.support,z∈cartanApartment Aₛ (reflectionGroup c d.reflection)) →
        ∃ x∈halfPathActor (X := (Aₛ).Universal) p 6,
          ∀ k≤12,x•p.getVert k=p.getVert (12-k) := by
  let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  apply assemble (G := G) (L := Lₛ) (S := Sₛ) h c
    (SourceEightCorrectedGeometry.source_corrected_eight_geometry hG T hempty hM hu hmany hcard e H hH eR c)
  intro d P K hKP hcomp
  apply source_reflections_of_eight_centered hG T hempty hM hu hmany hcard e H hH eR c d
  intro a b p hp hl hT hm
  exact SourceEightCenteredReflection.source_eight_reflection_mem_halfactor
    hG T hempty hM hu hmany hcard e H hH eR c d p hp hl hT hm hKP hcomp

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentReflections
