module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryNativePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalMarkedSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceRootTransitivityLowerBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover
public import Theory.GroupTheory.Amalgam.GeneratedCompletion.Overlap
public import Theory.GroupAction.RankTwoCosetGeometry.Reorientation
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# The exact exceptional source minimum

The native binary five-path calculation and six-path obstruction transfer
through the common universal completion of the compatible reduced amalgam.
The transfer preserves both endpoint actions and the entire Borel. Rooted
five-path transitivity bounds the first nonregular source length from below;
the nontrivial native six-path fixer gives the opposite bound. The existing
source-parameter theorem includes the closed paths permitted by the book.

The original critical-pair application uses exhaustive exceptional selection:
the new binary minimum and the completed field-four parameters give s = 5
without an assumed quotient model or field identification. The actual
opposite-core equality `hD` is retained. The binary maximum regular length
and the other Chapter 10 branches remain separate obligations.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
path convention p.60, extrema pp.73–74, and (10.9), printed pp.162–163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction OriginalExtension
open Atlas.G2 Atlas.G2.BinaryParabolicPair
namespace BinaryMinimum

private theorem pair_generate : derivedFirst ⊔ derivedSecond = ⊤ := by
  apply map_injective (f := DerivedModel.subtype) DerivedModel.subtype_injective
  rw [Subgroup.map_sup,derivedFirst_map_subtype,derivedSecond_map_subtype,
    ←MonoidHom.range_eq_map,DerivedModel.range_subtype]
  have h := DerivedParabolicGeneration.binary_restricted_pair_generate
  rw [LieParabolicSetup.parabolic₁_binary] at h
  exact h

private def mc : FaithfulCompletion derivedAmalgam (G := DerivedModel) :=
  FaithfulCompletion.ofSubgroups derivedFirst (derivedSylow : Subgroup DerivedModel)
    derivedSecond derivedSylow_le_first derivedSylow_le_second pair_generate

private theorem mc_family : mc.cosetFamily = BinaryPaths.family := by
  funext i
  cases i <;> simp [FaithfulCompletion.cosetFamily,mc,BinaryPaths.family]

private theorem mc_overlap : mc.left.range ⊓ mc.right.range = mc.middle.range := by
  have hl : mc.left.range = derivedFirst := Subgroup.range_subtype _
  have hr : mc.right.range = derivedSecond := Subgroup.range_subtype _
  have hm : mc.middle.range = (derivedSylow : Subgroup DerivedModel) := by
    ext x
    constructor
    · rintro ⟨d,rfl⟩; exact d.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  rw [hl,hr,hm]
  exact derived_parabolic_intersection_in_model

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem endpoint_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (SuzukiContainment.reducedSylow L S) i ≤ G₀ L S := by
  rw [← P₀_eq_source h i]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private noncomputable def completionOfSubgroups (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H) :
    FaithfulCompletion (RankTwoAmalgam.ofSubgroups A D C hDA hDC) (G := H) where
  left := inclusion hA
  right := inclusion hC
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := fun _ _ hxy => Subtype.ext (congrArg (fun x : H => (x : G)) hxy)
  generated := by
    rw [inclusion_range, inclusion_range, ← subgroupOf_sup hA hC, hgen]
    exact subgroupOf_self _

private theorem completionOfSubgroups_overlap (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (hinter : A ⊓ C = D) :
    (completionOfSubgroups A D C H hDA hDC hA hC hgen).left.range ⊓
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).right.range =
      (completionOfSubgroups A D C H hDA hDC hA hC hgen).middle.range := by
  change (inclusion hA).range ⊓ (inclusion hC).range = (inclusion (hDA.trans hA)).range
  rw [inclusion_range, inclusion_range, inclusion_range]
  change (A ⊓ C).subgroupOf H = D.subgroupOf H
  rw [hinter]

private noncomputable def sc (h : HypothesisF11 L S) :
    FaithfulCompletion (reducedAmalgam L S) (G := G₀ L S) :=
  completionOfSubgroups _ _ _ _ (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (endpoint_le h 0) (endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)

private theorem sc_family (h : HypothesisF11 L S) :
    (sc h).cosetFamily = reducedFamily L S := by
  funext i
  cases i
  · change (inclusion (endpoint_le h 0)).range = (P₀ L S 0).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 0]
  · change (inclusion (endpoint_le h 1)).range = (P₀ L S 1).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 1]

private theorem sc_overlap (h : HypothesisF11 L S) :
    (sc h).left.range ⊓ (sc h).right.range = (sc h).middle.range := by
  exact completionOfSubgroups_overlap _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (endpoint_le h 0) (endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)
    (lemma_F_1_3_6 (SuzukiContainment.reduced_hypothesis h))


private theorem swap_paths_iff {A : Type*} [Group A] (F : Bool → Subgroup A)
    (i : Bool) (n : ℕ) :
    RootPathTransitive (graph (swapFamily F)) A (base (swapFamily F) i) n ↔
      RootPathTransitive (graph F) A (base F (!i)) n := by
  constructor
  · intro ht
    have ht' := ht.map_graphIso (swapGraphIso F).symm
      (MonoidHom.id A) (by
        rintro g ⟨j,q⟩
        cases j <;> rfl)
    have he : (swapGraphIso F).symm (base (swapFamily F) i) = base F (!i) := by
      cases i <;> rfl
    rwa [he] at ht'
  · intro ht
    have ht' := ht.map_graphIso (swapGraphIso F)
      (MonoidHom.id A) (swapVertex_smul F)
    have he : swapGraphIso F (base F (!i)) = base (swapFamily F) i := by
      change swapVertex F (base F (!i)) = _
      simp only [swapVertex_base,Bool.not_not]
    rwa [he] at ht'

/-- Rooted transitivity in either orientation agrees through the two actual
universal covers of the compatible binary marking. -/
theorem marked_paths_iff (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse derivedAmalgam) (i : Bool) (n : ℕ) :
    RootPathTransitive (graph (reducedFamily L S)) (G₀ L S)
        (base (reducedFamily L S) i) n ↔
      RootPathTransitive (graph BinaryPaths.family) DerivedModel
        (base BinaryPaths.family (!i)) n := by
  let d : FaithfulCompletion (reducedAmalgam L S) (G := DerivedModel) :=
    mc.reverse.comapIso e.reverse
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    change (mc.reverse.comapIso e.reverse).left.range ⊓
      (mc.reverse.comapIso e.reverse).right.range =
      (mc.reverse.comapIso e.reverse).middle.range
    rw [FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,
      FaithfulCompletion.comapIso_middle_range]
    exact mc.reverse_overlap mc_overlap
  have hf : d.cosetFamily = swapFamily BinaryPaths.family := by
    funext j
    cases j
    · change (mc.reverse.comapIso e.reverse).left.range = BinaryPaths.family true
      rw [FaithfulCompletion.comapIso_left_range,FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change (mc.reverse.comapIso e.reverse).right.range = BinaryPaths.family false
      rw [FaithfulCompletion.comapIso_right_range,FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  have hh := Universal.rootPathTransitive_iff_of_overlap
    (reducedAmalgam L S) d (sc h) hd (sc_overlap h) i n
  rw [sc_family h,hf] at hh
  exact hh.symm.trans (swap_paths_iff BinaryPaths.family i n)

/-- The binary marked comparison determines the literal source minimum,
including both vertex orbits and the book's closed-path convention. -/
theorem sourceS_eq_five (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse derivedAmalgam) :
    DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 := by
  apply Nat.le_antisymm
  · by_contra hn
    have ht := sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h)
      (base (reducedFamily L S) false) (by omega : 6 ≤ DGS85.sourceS
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)))
    exact BinaryPaths.not_rootPathTransitive_six ((marked_paths_iff h e false 6).mp ht)
  · apply DGS85.sourceS_ge_of_root_transitive (reduced_triple h) (reduced_vertex_sylow h)
    intro i
    exact (marked_paths_iff h e i 5).mpr (BinaryPaths.rootPathTransitive_five (!i))

end BinaryMinimum

open Noncommuting
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance binaryPathAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- DGS (10.9), binary branch: the first nonregular source length is five.
The original opposite-core equality and both endpoint markings are retained. -/
theorem original_bTwo_binary_sourceS_eq_five
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 2) :
    DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 := by
  obtain ⟨eG⟩ := original_bTwo_exceptional_binary_reduced_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact BinaryMinimum.sourceS_eq_five h eG

/-- Exhaustive original critical-pair selection has minimum nonregular
length five in both exceptional rows, without an assumed beta model. -/
theorem original_bTwo_exceptional_sourceS_eq_five
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    DGS85.sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 := by
  rcases original_bTwo_exceptional_marked_selection h hc hne hb hβu ht htne hD with
    ⟨_,_,_,_,_,_,_,⟨eG⟩⟩ | ⟨_,_,_,_,_,_,_,hp⟩
  · exact BinaryMinimum.sourceS_eq_five h eG
  · exact (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hp.2

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
