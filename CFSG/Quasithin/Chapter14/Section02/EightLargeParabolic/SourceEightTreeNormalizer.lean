module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeEndpoint

/-!
# Complement normalizers in the original universal eight endpoint

Transport along the literal endpoint covering preserves the full two-core,
its complement and the exact normalizer center. That center fixes the
three-ball on this same universal tree. No abstract endpoint or center
placement is supplied by the caller.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeNormalizer
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan

private theorem complement_map {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (N K : Subgroup E) (h : N.IsComplement' K) :
    (N.map e.toMonoidHom).IsComplement' (K.map e.toMonoidHom) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have he' : y=x := e.injective he
    subst y
    rw [h.disjoint.le_bot ⟨hx,hy⟩,map_one]
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨n,k⟩,he⟩ := h.2 (e.symm x)
    refine ⟨e n,mem_map_of_mem _ n.property,e k,mem_map_of_mem _ k.property,?_⟩
    simpa only [map_mul,e.apply_symm_apply] using congrArg e he

private theorem centerIn_map {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (K : Subgroup E) :
    (centerIn K).map e.toMonoidHom=centerIn (K.map e.toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem _ hx.1,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact (map_mul e.toMonoidHom y x).symm.trans
      ((congrArg e.toMonoidHom (hx.2 y hy)).trans (map_mul e.toMonoidHom x y))
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    intro z hz
    apply e.injective
    change e.toMonoidHom (z*y)=e.toMonoidHom (y*z)
    rw [map_mul,map_mul]
    exact hx.2 (e.toMonoidHom z) (mem_map_of_mem _ hz)

section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "P" => RankTwo.stabilizer (Universal.cosetFamily A) (base (Universal.cosetFamily A) true)

/-- Every full-core complement in the original tree endpoint has its exact
normalizer center in the original center's radius-three fixer. -/
@[expose] def HasEightTreeNormalizer (h : HypothesisF11 L S) (H : Subgroup G) : Prop :=
  ∃ j : P ≃* H,
    (∀ x, (j x:G)=((G₀ L S).subtype.comp (bOne_tree_map h)) x) ∧
    ∀ K : Subgroup P, (pCore 2 P).IsComplement' K →
      let Z := (centerIn (H.pCoreIn 2)).comap (H.subtype.comp j.toMonoidHom)
      normalizer (K:Set P)=K ⊔ Z ∧
      centerIn (normalizer (K:Set P))=Z ∧
      Z ⊓ K=⊥ ∧
      Z.map (P).subtype≤graphBallFixer (sourceGraph A) (base (Universal.cosetFamily A) true) 3

private theorem assemble (h : HypothesisF11 L S) (H : Subgroup G)
    (he : ∃ j : P ≃* H, ∀ x, (j x:G)=((G₀ L S).subtype.comp (bOne_tree_map h)) x)
    (hball : SourceEightCentralBall.HasEightCentralBall h H)
    (hn : ∀ K : Subgroup H, (pCore 2 H).IsComplement' K →
      normalizer (K:Set H)=K ⊔ (centerIn (H.pCoreIn 2)).subgroupOf H)
    (hc : ∀ K : Subgroup H, (pCore 2 H).IsComplement' K →
      centerIn (normalizer (K:Set H))=(centerIn (H.pCoreIn 2)).subgroupOf H) :
    HasEightTreeNormalizer h H := by
  obtain ⟨j,hj⟩ := he
  refine ⟨j,hj,?_⟩
  intro K hK
  let Z := (centerIn (H.pCoreIn 2)).subgroupOf H
  have hcomp : (pCore 2 H).IsComplement' (K.map j.toMonoidHom) := by
    have hh := complement_map j (pCore 2 P) K hK
    rwa [pCore_map_iso] at hh
  have hmap : ((centerIn (H.pCoreIn 2)).comap
      (H.subtype.comp j.toMonoidHom)).map j.toMonoidHom=Z := by
    change (Z.comap j.toMonoidHom).map j.toMonoidHom=Z
    exact map_comap_eq_self_of_surjective j.surjective Z
  refine ⟨?_,?_,?_,?_⟩
  · apply map_injective (f := j.toMonoidHom) j.injective
    rw [map_normalizer_eq_of_bijective _ j.bijective,Subgroup.map_sup,hmap]
    exact hn _ hcomp
  · apply map_injective (f := j.toMonoidHom) j.injective
    rw [centerIn_map,map_normalizer_eq_of_bijective _ j.bijective,hmap]
    exact hc _ hcomp
  · apply bot_unique
    intro z hz
    have hzcore : j z∈pCore 2 H := by
      apply (comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)).le
      exact (show centerIn (H.pCoreIn 2)≤H.pCoreIn 2 from inf_le_left) hz.1
    have heq : j z=1 := hcomp.disjoint.le_bot ⟨hzcore,mem_map_of_mem _ hz.2⟩
    exact j.injective (heq.trans (map_one j).symm)
  · rintro _ ⟨z,hz,rfl⟩
    apply hball z z.property
    change (j z:G)∈centerIn (H.pCoreIn 2) at hz
    rwa [←hj]

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

set_option maxHeartbeats 800000 in
/-- Literal original-source complement normalizers and their exact centers
transport to the same universal endpoint with full radius-three fixation. -/
theorem source_eight_tree_normalizer :
    HasEightTreeNormalizer
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) H := by
  exact assemble _ H
    (SourceEightTreeEndpoint.source_eight_tree_endpoint hG T hempty hM hu hmany hcard e H hH eR).1
    (SourceEightCentralBall.source_eight_core_center_radius_three hG T hempty hM hu hmany hcard e H hH eR)
    (fun K hK => (SourceComplementNormalizer.source_complement_normalizer
      hG T hempty hM hu hmany hcard e H hH eR K hK).2)
    (fun K hK => SourceComplementCenter.source_complement_normalizer_center
      hG T hempty hM hu hmany hcard e H hH eR K hK)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeNormalizer
