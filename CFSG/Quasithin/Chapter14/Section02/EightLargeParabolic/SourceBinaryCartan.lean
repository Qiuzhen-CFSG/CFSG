module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathQuotients
public import Theory.GroupTheory.WeakBNPair.RegularTree.SevenCubicKernel
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCentralizer

/-!
# The full Cartan at the actual binary endpoint

Its order seven forces the full Cartan into the complete cubic permutation
kernel. On every supported twelve-path with binary midpoint, the same
Cartan centralizes the actual half-path actor. This uses the full local
permutation kernel, not a substitution of the endpoint two-core. The
source geometry and intrinsic root classes are constructed from the
original pair and retained in the conclusion.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceHalfPathQuotients
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "P" => Universal.cosetFamily A

private theorem binary_halfactor_centralization (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (d : SixPathSmallActorGeometry c)
    {a b} (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (htype : (p.getVert 6).type=false) :
    cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) := by
  let cov := bOne_tree_cover h
  have hCv : cartan c ≤ stabilizer P (p.getVert 6) := by
    intro k hk
    exact reflectionApartment_fixed c d.reflection d.normalizes k hk _
      (hT _ (p.getVert_mem_support 6))
  have hv : Nat.card ((sourceGraph A).neighborSet (p.getVert 6))=3 := by
    simpa only [htype,Bool.false_eq_true,if_false] using hval (p.getVert 6)
  have hker := seven_cubic_vertex_kernel P (cartan c) hC (p.getVert 6) hCv hv
  have hmap : cartan c ≤ (U F (cov.vertex (p.getVert 6))).comap (bOne_tree_map h) := by
    intro k hk
    exact cov.ballKernel_map_le (p.getVert 6) 1 (mem_map_of_mem _ (hker hk))
  have he := Assembly.BTwoSource.six_actor_cartan_centralizer h c d p hp hl hT
  exact inf_eq_left.mp (he.trans (inf_eq_left.mpr hmap))

private theorem binary_centralization_of_quotients (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hq : HasCanonicalHalfPathQuotients h c) :
    ∃ d : SixPathSmallActorGeometry c,
      (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=12 →
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) →
        (p.getVert 6).type=false →
        cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) := by
  obtain ⟨d,hclass,_⟩ := hq
  exact ⟨d,hclass,fun p hp hl hT ht => binary_halfactor_centralization h c hC hval d p hp hl hT ht⟩

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
local notation "Aₛ" => reducedAmalgam Lₛ (T : Subgroup G)
local notation "Pₛ" => Universal.cosetFamily Aₛ

/-- The whole original order-seven Cartan lies in the binary endpoint's
full local permutation kernel. -/
theorem source_binary_cartan_kernel
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    cartan c ≤ ballKernel Pₛ (base Pₛ false) 1 := by
  apply seven_cubic_vertex_kernel Pₛ (cartan c)
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
  · change cartan c ≤ MulAction.stabilizer (Aₛ).Universal (base Pₛ false)
    rw [Subgroup.CosetGeometry.stabilizer_base Pₛ false]
    apply (cartan_le c).trans
    rw [originalMiddle, ←Universal.overlap_eq Aₛ
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    exact inf_le_left
  · exact SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR
      (base Pₛ false)

set_option maxHeartbeats 800000 in
/-- The source geometry and its root classes can be chosen with the full
Cartan centralizing every actual binary-midpoint half-path actor. -/
theorem source_binary_halfactor_centralization
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    let h : HypothesisF11 Lₛ (T : Subgroup G) :=
      (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
    ∃ d : SixPathSmallActorGeometry c,
      (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
      ∀ {a b} (p : (sourceGraph Aₛ).Walk a b), p.IsPath → p.length=12 →
        (∀ z∈p.support, z∈cartanApartment Aₛ (reflectionGroup c d.reflection)) →
        (p.getVert 6).type=false →
        cartan c ≤ centralizer (halfPathActor (X := (Aₛ).Universal) p 6 : Set (Aₛ).Universal) := by
  exact binary_centralization_of_quotients _ c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (source_half_path_quotients hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCartan
