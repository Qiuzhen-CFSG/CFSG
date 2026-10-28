module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCentralLayers

/-!
# Elementary subgroups of the actual eight-endpoint edge radical

Every subgroup of the original full edge two-group which is disjoint from
the whole eight-endpoint two-core embeds by the canonical local quotient
into a Sylow subgroup of SL₂(8). It is therefore elementary abelian, of
order at most eight. This applies to the actual six-path radical already
constructed from the original source, without any root marking or
reflection assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootElementary
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "P" => Universal.cosetFamily A

private theorem twoGroup_image_le_edge_core (h : HypothesisF11 L S) :
    (twoGroup L S).map (bOne_tree_map h) ≤ (F false ⊓ F true).pCoreIn 2 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let E := F false ⊓ F true
  have hmapE : (originalMiddle A).map φ = E := by
    rw [originalMiddle, ←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    exact cov.map_inf
  have hUE : (twoGroup L S).map φ ≤ E := hmapE ▸ map_mono twoGroup_le
  have hn : E ≤ normalizer ((twoGroup L S).map φ : Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  exact le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hn

private theorem edge_subgroup_elementary (h : HypothesisF11 L S)
    (e8 : (graphLocalGroup F (base F true) ⧸ pCore 2 (graphLocalGroup F (base F true))) ≃*
      SL(2,GaloisField 2 3))
    (R : Subgroup (A).Universal) (hR : R ≤ twoGroup L S)
    (hd : Disjoint R ((P true).pCoreIn 2)) :
    IsElementaryAbelian 2 R ∧ Nat.card R ≤ 8 := by
  let φ := bOne_tree_map h
  let J := graphLocalGroup F (base F true)
  have hUP : twoGroup L S ≤ P true := by
    apply twoGroup_le.trans
    rw [originalMiddle, ←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    exact inf_le_right
  have hRJ : R.map φ ≤ J := by
    intro x hx
    have hu := twoGroup_image_le_edge_core h (map_mono hR hx)
    have he : F false ⊓ F true = stabilizer F (base F true) ⊓ stabilizer F (base F false) := by
      change F false ⊓ F true = MulAction.stabilizer (G₀ L S) (base F true) ⊓
        MulAction.stabilizer (G₀ L S) (base F false)
      rw [Subgroup.CosetGeometry.stabilizer_base F true,Subgroup.CosetGeometry.stabilizer_base F false]
      exact inf_comm _ _
    exact graph_intrinsic_edgeCore_le (reduced_triple h) (he ▸ hu)
  let j : R →* J :=
    { toFun x := ⟨φ x,hRJ (mem_map_of_mem φ x.property)⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' x y := Subtype.ext (map_mul φ (x : (A).Universal) (y : (A).Universal)) }
  let f : R →* SL(2,GaloisField 2 3) :=
    e8.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 J)).comp j)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    change e8 (QuotientGroup.mk' (pCore 2 J) (j x))=1 at hx
    have hj : j x ∈ pCore 2 J := (QuotientGroup.eq_one_iff (j x)).mp
      (e8.injective (hx.trans e8.map_one.symm))
    have hq : φ x ∈ Q F (base F true) :=
      (CommutingTrivial.graphLocalGroup_core (reduced_triple h) (base F true)).le
        (mem_map_of_mem J.subtype hj)
    have hxcore := (universalBOne_mem_core_iff h true x ((hR.trans hUP) x.property)).mp hq
    exact Subtype.ext (disjoint_def.mp hd x.property hxcore)
  obtain ⟨hel,hcard⟩ := CommutingOneProfile.linear_elementary_card
    ((twoGroup_isTwo h).to_le hR) f hf
  refine ⟨hel,?_⟩
  simpa only [GaloisField.card 2 3 (by decide),show (2:ℕ)^3=8 from rfl] using hcard

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

/-- The exact original edge radical embeds through the canonical eight
quotient whenever it misses the full original endpoint core. -/
theorem source_eight_root_subgroups_elementary
    (R : Subgroup (Aₛ).Universal) (hR : R ≤ twoGroup Lₛ (T : Subgroup G))
    (hd : Disjoint R ((Universal.cosetFamily Aₛ true).pCoreIn 2)) :
    IsElementaryAbelian 2 R ∧ Nat.card R ≤ 8 := by
  have h : HypothesisF11 Lₛ (T : Subgroup G) :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  exact edge_subgroup_elementary h
    (Assembly.linear_graph_quotient h true (residualQuotientEquiv H eR)
      (base (reducedFamily Lₛ (T : Subgroup G)) true) rfl).some R hR hd

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootElementary
