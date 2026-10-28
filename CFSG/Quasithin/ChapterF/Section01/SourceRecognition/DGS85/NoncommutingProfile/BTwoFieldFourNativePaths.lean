module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourPathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourMarkedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PathCertificates
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Assembly
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover
public import Theory.GroupTheory.Amalgam.GeneratedCompletion.Overlap
public import Theory.GroupAction.RankTwoCosetGeometry.Reorientation
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

public import Theory.GroupAction.RankTwoCosetCover.PathRegularity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.RegularSixPath
public import Theory.GroupAction.CubicTree.ArcEquiv

/-!
# Native J₂ paths on the literal reduced source graph

The compatible reversed amalgam comparison gives two coset covers from the
same universal completion. Rooted five-path transitivity and the native
regular six-path transfer through those covers, preserving the alpha root
and both endpoint actions. The source order bound then identifies s with 5.

Source: DGS, *Groups and Graphs* (1985), (10.9), printed pp.162--163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction OriginalExtension
open GreenBook.HallJanko
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open scoped MatrixGroups

local notation "MF" => PathCertificates.family

noncomputable def mc : FaithfulCompletion j2Model.toMarking.amalgam (G := Carrier) where
  left := (j2Model.toMarking.P 0).subtype
  right := (j2Model.toMarking.P 1).subtype
  compatible := rfl
  left_injective := Subtype.val_injective
  right_injective := Subtype.val_injective
  middle_injective := by
    intro x y hxy
    apply Subtype.ext
    change (x : Carrier) = (y : Carrier) at hxy
    exact hxy
  generated := by
    simpa only [Subgroup.range_subtype] using j2Model.toMarking.P_generate

theorem mc_family : mc.cosetFamily = MF := by
  funext i
  cases i
  · simp [FaithfulCompletion.cosetFamily, mc, PathCertificates.family]
  · simp [FaithfulCompletion.cosetFamily, mc, PathCertificates.family]

theorem mc_overlap : mc.left.range ⊓ mc.right.range = mc.middle.range := by
  have hleft : mc.left.range = j2Model.toMarking.P 0 := by
    change (j2Model.toMarking.P 0).subtype.range = _
    exact Subgroup.range_subtype (j2Model.toMarking.P 0)
  have hright : mc.right.range = j2Model.toMarking.P 1 := by
    change (j2Model.toMarking.P 1).subtype.range = _
    exact Subgroup.range_subtype (j2Model.toMarking.P 1)
  have hmiddle : mc.middle.range = j2Model.toMarking.B := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact d.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hleft, hright, hmiddle]
  exact j2Model.toMarking.overlap

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

local instance fieldFourNativePathsAlgebra {k₀ : Type*} [Field k₀]
    [CharP k₀ 2] : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

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

theorem marked_transfer (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse j2Model.toMarking.amalgam)
    (ht : ∀ i, RootPathTransitive (graph MF) Carrier (base MF i) 5) :
    ∀ i, RootPathTransitive (graph (reducedFamily L S)) (G₀ L S)
      (base (reducedFamily L S) i) 5 := by
  let d : FaithfulCompletion (reducedAmalgam L S) (G := Carrier) :=
    mc.reverse.comapIso e.reverse
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    change (mc.reverse.comapIso e.reverse).left.range ⊓
      (mc.reverse.comapIso e.reverse).right.range =
      (mc.reverse.comapIso e.reverse).middle.range
    rw [FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,
      FaithfulCompletion.comapIso_middle_range]
    exact mc.reverse_overlap mc_overlap
  have hf : d.cosetFamily = swapFamily MF := by
    funext i
    cases i
    · change d.left.range = MF true
      change (mc.reverse.comapIso e.reverse).left.range = MF true
      rw [FaithfulCompletion.comapIso_left_range, FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change d.right.range = MF false
      change (mc.reverse.comapIso e.reverse).right.range = MF false
      rw [FaithfulCompletion.comapIso_right_range, FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  intro i
  have hm : RootPathTransitive (graph d.cosetFamily) Carrier
      (base d.cosetFamily i) 5 := by
    rw [hf]
    have hh := (ht (!i)).map_graphIso (swapGraphIso MF) (MonoidHom.id Carrier)
      (fun g v => swapVertex_smul MF g v)
    have he : swapGraphIso MF (base MF (!i)) = base (swapFamily MF) i := by
      change swapVertex MF (base MF (!i)) = base (swapFamily MF) i
      simp only [swapVertex_base, Bool.not_not]
    rw [← he]
    exact hh
  have hh := Universal.rootPathTransitive_transfer_of_overlap
    (reducedAmalgam L S) d (sc h) hd (sc_overlap h) i 5 hm
  rw [sc_family h] at hh
  exact hh

/-- The native J₂ five-path certificate supplies the missing lower bound in
the field-four source branch.  Combining it with the marked reduced
comparison and the order upper bound gives the literal equality `sourceS = 5`.
-/
theorem original_bTwo_field_four_sourceS_eq_five
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    DGS85.sourceS
      (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 5 := by
  obtain ⟨eJ⟩ := original_bTwo_field_four_reduced_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hnative : ∀ i, RootPathTransitive (graph MF) Carrier (base MF i) 5 :=
    PathCertificates.rootPathTransitive_five
  have hsource := marked_transfer h eJ hnative
  exact original_bTwo_field_four_sourceS_eq_five_of_reduced_path_transitive
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK hsource

open Theory.GroupAction.CubicTree

private theorem regular_graphIso {X Y A : Type*} [Group A]
    [MulAction A X] [MulAction A Y] {Γ : SimpleGraph X} {Δ : SimpleGraph Y}
    (e : Γ ≃g Δ) (he : ∀ (a : A) v, e (a • v) = a • e v)
    {n : ℕ} {v : X} (p : BasedWalk Γ n v) (hp : Regular (A := A) p) :
    Regular (A := A) (p.map e.toHom) := by
  refine ⟨(rightRegular_reverse_iff _).mp ?_,(rightRegular_graphIso_iff e he p).mpr hp.2⟩
  have hh := (rightRegular_graphIso_iff e he (reverse p)).mpr
    ((rightRegular_reverse_iff p).mpr hp.1)
  apply rightRegular_of_vertices_eq _ _ _ hh
  simp only [BasedWalk.vertices_map,vertices_reverse,List.map_reverse]

/-- The compatible marked comparison transports regular paths at the
source alpha root through the actual common coset covers. -/
theorem marked_regular_transfer (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse j2Model.toMarking.amalgam)
    (n : ℕ) (ht : ∃ p : BasedWalk (graph MF) n (base MF true),
      p.Nonbacktracking ∧ Regular (A := Carrier) p) :
    ∃ p : BasedWalk (graph F₀) n α,
      p.Nonbacktracking ∧ Regular (A := G₀ L S) p := by
  let d : FaithfulCompletion (reducedAmalgam L S) (G := Carrier) :=
    mc.reverse.comapIso e.reverse
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    change (mc.reverse.comapIso e.reverse).left.range ⊓
      (mc.reverse.comapIso e.reverse).right.range =
      (mc.reverse.comapIso e.reverse).middle.range
    rw [FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range,
      FaithfulCompletion.comapIso_middle_range]
    exact mc.reverse_overlap mc_overlap
  have hf : d.cosetFamily = swapFamily MF := by
    funext i
    cases i
    · change (mc.reverse.comapIso e.reverse).left.range = MF true
      rw [FaithfulCompletion.comapIso_left_range, FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change (mc.reverse.comapIso e.reverse).right.range = MF false
      rw [FaithfulCompletion.comapIso_right_range, FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  have hm : ∃ p : BasedWalk (graph d.cosetFamily) n (base d.cosetFamily false),
      p.Nonbacktracking ∧ Regular (A := Carrier) p := by
    rw [hf]
    obtain ⟨p,hp,hr⟩ := ht
    have hbase : swapGraphIso MF (base MF true) = base (swapFamily MF) false := rfl
    rw [←hbase]
    exact ⟨p.map (swapGraphIso MF).toHom,
      (BasedWalk.nonbacktracking_map_iff (swapGraphIso MF).toHom
        (fun v => ((swapGraphIso MF).mapNeighborSet v).injective) p).mpr hp,
      regular_graphIso (swapGraphIso MF) (swapVertex_smul MF) p hr⟩
  let cM := Universal.coverData_of_overlap (reducedAmalgam L S) d hd
  let cS := Universal.coverData_of_overlap (reducedAmalgam L S) (sc h) (sc_overlap h)
  have hm' : ∃ p : BasedWalk (graph d.cosetFamily) n
      (cM.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) false)),
      p.Nonbacktracking ∧ Regular (A := Carrier) p := by
    rw [show cM.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) false) =
      base d.cosetFamily false from cM.vertex_base false]
    exact hm
  have hh := (cS.exists_regular_path_iff n
      (base (Universal.cosetFamily (reducedAmalgam L S)) false)).mpr
    ((cM.exists_regular_path_iff n _).mp hm')
  rw [show cS.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) false) =
    base (sc h).cosetFamily false from cS.vertex_base false] at hh
  rw [sc_family h] at hh
  exact hh

/-- The native J₂ regular six-path supplies a regular nonbacktracking
six-path at the original reduced alpha vertex, with no path premise. -/
theorem original_bTwo_field_four_regular_six_walk
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ p : BasedWalk (graph F₀) 6 α,
      p.Nonbacktracking ∧ Regular (A := G₀ L S) p := by
  obtain ⟨eJ⟩ := original_bTwo_field_four_reduced_iso
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact marked_regular_transfer h eJ 6
    ⟨PathCertificates.sixPath,PathCertificates.sixPath_nb,PathCertificates.sixPath_regular⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
