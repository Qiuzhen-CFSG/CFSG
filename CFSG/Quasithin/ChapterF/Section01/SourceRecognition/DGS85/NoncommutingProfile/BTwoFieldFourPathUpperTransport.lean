module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourSevenFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourRegularPaths

/-!
# Transporting the field-four maximum through the marked covers

The reduced source and native J₂ graphs are covered by the same universal
completion of the fully marked amalgam. A regular source path lifts through
the source cover and descends through the native cover, with both endpoint
actions retained. Reversing the native vertex labels then applies the
native maximum six. This uses the same completion maps and whole-overlap
identities as the previously constructed lower witness.

Source: DGS, *Groups and Graphs* (1985), (10.9), printed pp.162--163.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupAction.CubicTree
open Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction OriginalExtension GreenBook.HallJanko
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
local notation "MF" => PathCertificates.family
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S

private theorem upper_endpoint_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (SuzukiContainment.reducedSylow L S) i ≤ G₀ L S := by
  rw [← P₀_eq_source h i]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private noncomputable def upper_completionOfSubgroups (A D C H : Subgroup G)
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

private theorem upper_completionOfSubgroups_overlap (A D C H : Subgroup G)
    (hDA : D ≤ A) (hDC : D ≤ C) (hA : A ≤ H) (hC : C ≤ H) (hgen : A ⊔ C = H)
    (hinter : A ⊓ C = D) :
    (upper_completionOfSubgroups A D C H hDA hDC hA hC hgen).left.range ⊓
      (upper_completionOfSubgroups A D C H hDA hDC hA hC hgen).right.range =
      (upper_completionOfSubgroups A D C H hDA hDC hA hC hgen).middle.range := by
  change (inclusion hA).range ⊓ (inclusion hC).range = (inclusion (hDA.trans hA)).range
  rw [inclusion_range, inclusion_range, inclusion_range]
  change (A ⊓ C).subgroupOf H = D.subgroupOf H
  rw [hinter]

private noncomputable def upper_sc (h : HypothesisF11 L S) :
    FaithfulCompletion (reducedAmalgam L S) (G := G₀ L S) :=
  upper_completionOfSubgroups _ _ _ _ (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (upper_endpoint_le h 0) (upper_endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)

private theorem upper_sc_family (h : HypothesisF11 L S) :
    (upper_sc h).cosetFamily = reducedFamily L S := by
  funext i
  cases i
  · change (inclusion (upper_endpoint_le h 0)).range = (P₀ L S 0).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 0]
  · change (inclusion (upper_endpoint_le h 1)).range = (P₀ L S 1).subgroupOf (G₀ L S)
    rw [inclusion_range,P₀_eq_source h 1]

private theorem upper_sc_overlap (h : HypothesisF11 L S) :
    (upper_sc h).left.range ⊓ (upper_sc h).right.range = (upper_sc h).middle.range := by
  exact upper_completionOfSubgroups_overlap _ _ _ _
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
    (upper_endpoint_le h 0) (upper_endpoint_le h 1)
    (by rw [← P₀_eq_source h 0, ← P₀_eq_source h 1]; rfl)
    (lemma_F_1_3_6 (SuzukiContainment.reduced_hypothesis h))

private theorem upper_regular_graphIso {X Y A : Type*} [Group A]
    [MulAction A X] [MulAction A Y] {Γ : SimpleGraph X} {Δ : SimpleGraph Y}
    (e : Γ ≃g Δ) (he : ∀ (a : A) v, e (a • v) = a • e v)
    {n : ℕ} {v : X} (p : BasedWalk Γ n v) (hp : Regular (A := A) p) :
    Regular (A := A) (p.map e.toHom) := by
  refine ⟨(rightRegular_reverse_iff _).mp ?_,(rightRegular_graphIso_iff e he p).mpr hp.2⟩
  have hh := (rightRegular_graphIso_iff e he (reverse p)).mpr
    ((rightRegular_reverse_iff p).mpr hp.1)
  apply rightRegular_of_vertices_eq _ _ _ hh
  simp only [BasedWalk.vertices_map,vertices_reverse,List.map_reverse]

/-- The universal covers used for the marked lower witness also transport
nonexistence of longer regular paths, at both roots and every base vertex. -/
theorem marked_regular_length_le_six (h : HypothesisF11 L S)
    (e : Iso (reducedAmalgam L S).reverse j2Model.toMarking.amalgam)
    {n : ℕ} {v : Vertex F₀} (p : BasedWalk (graph F₀) n v)
    (hp : p.Nonbacktracking) (hr : Regular (A := G₀ L S) p) : n ≤ 6 := by
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
      rw [FaithfulCompletion.comapIso_left_range,FaithfulCompletion.reverse_left]
      exact congrFun mc_family true
    · change (mc.reverse.comapIso e.reverse).right.range = MF false
      rw [FaithfulCompletion.comapIso_right_range,FaithfulCompletion.reverse_right]
      exact congrFun mc_family false
  obtain ⟨q,hq,g,hg⟩ := exists_base_path_translate F₀ rfl p hp
  have hrev : p.vertices.map (g⁻¹ • ·) = q.vertices := by
    rw [←hg,List.map_map]
    simp only [Function.comp_def,inv_smul_smul]
    exact List.map_id _
  have hact : GraphAction (graph F₀) (G₀ L S) :=
    ⟨fun a _ _ ha => (Subgroup.CosetGeometry.translationGraphIso F₀ a).toHom.map_adj ha⟩
  have hqr : Regular (A := G₀ L S) q :=
    ⟨leftRegular_of_conjugate hact p q g⁻¹ hrev hr.1,
      rightRegular_of_conjugate hact p q g⁻¹ hrev hr.2⟩
  let cM := Universal.coverData_of_overlap (reducedAmalgam L S) d hd
  let cS := Universal.coverData_of_overlap (reducedAmalgam L S) (upper_sc h) (upper_sc_overlap h)
  have hs : ∃ q : BasedWalk (graph (upper_sc h).cosetFamily) n
      (cS.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) v.type)),
      q.Nonbacktracking ∧ Regular (A := G₀ L S) q := by
    rw [show cS.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) v.type) =
      base (upper_sc h).cosetFamily v.type from cS.vertex_base v.type,upper_sc_family h]
    exact ⟨q,hq,hqr⟩
  have hm := (cM.exists_regular_path_iff n
      (base (Universal.cosetFamily (reducedAmalgam L S)) v.type)).mpr
    ((cS.exists_regular_path_iff n _).mp hs)
  rw [show cM.vertex (base (Universal.cosetFamily (reducedAmalgam L S)) v.type) =
    base d.cosetFamily v.type from cM.vertex_base v.type,hf] at hm
  obtain ⟨r,hrnb,hrr⟩ := hm
  let t := r.map (swapGraphIso MF).symm.toHom
  have ht : t.Nonbacktracking :=
    (BasedWalk.nonbacktracking_map_iff (swapGraphIso MF).symm.toHom
      (fun v => ((swapGraphIso MF).symm.mapNeighborSet v).injective) r).mpr hrnb
  have htr : Regular (A := Carrier) t := upper_regular_graphIso (swapGraphIso MF).symm
    (by intro a v; rcases v with ⟨i,v⟩; cases i <;> rfl) r hrr
  exact FieldFourPathUpper.regular_length_le_six t ht htr

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
