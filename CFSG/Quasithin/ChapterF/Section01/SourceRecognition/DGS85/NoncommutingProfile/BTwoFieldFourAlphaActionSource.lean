module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaCenter
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.SourceActionSplitting

/-!
# The full field-four alpha endpoint in root-normalizer coordinates

The alpha core is the marked `UT₃(F₄)` root subgroup, and the complete
conjugation image is the standard inner--actor subgroup after a coordinate
change. The split root-normalizer construction then identifies the whole
reduced alpha endpoint with the explicit semidirect-product model, while
preserving the core inclusion on the nose.

Source: DGS, *Groups and Graphs* (1985), (10.9), p.163; Aschbacher,
*Sporadic Groups* (1994), 46.3(3) and 46.14.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
open SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "Root" => Matrix.PSL3Four.RootNormalizerModel.Root
local notation "Model" => Matrix.PSL3Four.RootNormalizerModel.Model
local instance fieldFourAlphaActionAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

theorem original_bTwo_field_four_alpha_center_action
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
    ∀ b : MulAut (center (pCore 2 (P₀ L S 0))), ∃ a : P₀ L S 0,
      ∀ z : center (pCore 2 (P₀ L S 0)),
        MulAut.conjNormal a z = (b z : pCore 2 (P₀ L S 0)) := by
  let P := P₀ L S 0
  let N := pCore 2 P
  let ι := (G₀ L S).subtype
  have hN : N.map P.subtype = (parabolic L S 0).pCoreIn 2 := P₀_core h 0
  have hcenter := map_center_image_of_injective N P.subtype P.subtype_injective
  rw [hN] at hcenter
  have hmark : (center N).map (P.subtype.comp N.subtype) = (Z F₀ α).map ι :=
    hcenter.symm.trans (original_bTwo_field_four_structure
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK).2.1
  let ec : center N ≃* (center N).map (P.subtype.comp N.subtype) :=
    (center N).equivMapOfInjective (P.subtype.comp N.subtype)
      (P.subtype_injective.comp N.subtype_injective)
  let ez : Z F₀ α ≃* center N :=
    ((Z F₀ α).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      ((MulEquiv.subgroupCongr hmark.symm).trans ec.symm)
  have hez (z : Z F₀ α) : (((ez z : N) : P) : G) = ι z := by
    have he := congrArg (fun x : (center N).map (P.subtype.comp N.subtype) => (x : G))
      (ec.apply_symm_apply
        (MulEquiv.subgroupCongr hmark.symm
          ((Z F₀ α).equivMapOfInjective ι (G₀ L S).subtype_injective z)))
    exact he
  have hAP : c.actor.map ι ≤ P := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  let j : c.actor →* P := (ι.comp c.actor.subtype).codRestrict P
    (fun a => hAP (mem_map_of_mem ι a.property))
  have hk := (original_bTwo_exceptional_fields_and_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E).1
  have hω := c.omega_eq_bot_of_central_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor hcentral
  have hs := c.binary_center_action_surjective (reduced_triple h) E hω hk
  intro b
  obtain ⟨a,ha⟩ := hs (MulAut.congr ez.symm b)
  refine ⟨j a,fun z => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun z : Z F₀ α => ι z) (MulEquiv.congr_fun ha (ez.symm z))
  change ι ((a : G₀ L S) * (ez.symm z : G₀ L S) * (a : G₀ L S)⁻¹) =
    ι (ez.symm (b (ez (ez.symm z)))) at he
  rw [ez.apply_symm_apply] at he
  have hz := hez (ez.symm z)
  have hbz := hez (ez.symm (b z))
  rw [ez.apply_symm_apply] at hz hbz
  rw [map_mul,map_mul,map_inv,←hz,←hbz] at he
  exact he

private theorem alpha_root_automizer_data
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
    ∃ d : pCore 2 (P₀ L S 0) ≃* Root,
      (Matrix.PSL3Four.RootNormalizerModel.SourceAction.conjugation
        (pCore 2 (P₀ L S 0)) d).range =
          (MulAut.conj : Root →* MulAut Root).range ⊔
            Matrix.PSL3Four.RootNormalizerModel.actor := by
  let P := P₀ L S 0
  let N := pCore 2 P
  have hN : N.map P.subtype = (parabolic L S 0).pCoreIn 2 := P₀_core h 0
  obtain ⟨eQ⟩ := original_bTwo_field_four_alpha_root
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let d : N ≃* Root := ((N.equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hN)).trans eQ
  have hcP : centralizer (N : Set P) ≤ N := by
    let := (reduced_hypothesis h).finite_parabolic 0
    have hh := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      ((reduced_hypothesis h).characteristic_two 0)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (MulEquiv.subgroupCongr (P₀_eq_source h 0))).mpr hh
  have hP := (original_bTwo_field_four_reduced_alpha_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).2.1
  exact Matrix.PSL3Four.RootNormalizerModel.SourceAction.exists_adjusted_coordinates N d hcP hP
    (original_bTwo_field_four_alpha_center_action
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK)
    (original_bTwo_field_four_alpha_central_cubic
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK)

/-- The reduced field-four alpha endpoint is the split root-normalizer model. -/
theorem original_bTwo_field_four_alpha_model
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
    ∃ f : P₀ L S 0 ≃* Model,
      ∃ d : pCore 2 (P₀ L S 0) ≃* Root,
        (∀ q : pCore 2 (P₀ L S 0),
          f (q : P₀ L S 0) =
            SemidirectProduct.inl (d q)) := by
  let P := P₀ L S 0
  let N := pCore 2 P
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite P := Finite.of_injective (inclusion (P₀_le h 0))
    (inclusion_injective _)
  obtain ⟨d, hd⟩ := alpha_root_automizer_data h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hP := (original_bTwo_field_four_reduced_alpha_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).2.1
  have hcP : centralizer (N : Set P) ≤ N := by
    let := (reduced_hypothesis h).finite_parabolic 0
    have hh := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      ((reduced_hypothesis h).characteristic_two 0)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (MulEquiv.subgroupCongr (P₀_eq_source h 0))).mpr hh
  obtain ⟨f, hf⟩ := Matrix.PSL3Four.RootNormalizerModel.SourceAction.exists_model_equiv
    N d hcP hd
  exact ⟨f, d, hf⟩

/-- The model coordinates retain the literal action of the full reduced Borel
on the alpha core. -/
theorem original_bTwo_field_four_alpha_model_borel_action
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
    ∃ f : P₀ L S 0 ≃* Model,
      ∃ d : pCore 2 (P₀ L S 0) ≃* Root,
        ∃ hn : (B₀ L S).subgroupOf (P₀ L S 0) ≤
            normalizer (pCore 2 (P₀ L S 0) : Set (P₀ L S 0)),
          (∀ q : pCore 2 (P₀ L S 0),
            f (q : P₀ L S 0) = SemidirectProduct.inl (d q)) ∧
          ∀ (b : (B₀ L S).subgroupOf (P₀ L S 0))
            (q : pCore 2 (P₀ L S 0)),
            f ((pCore 2 (P₀ L S 0)).normalizerMonoidHom
                ⟨b, hn b.property⟩ q) =
              f (b : P₀ L S 0) * f (q : P₀ L S 0) *
                (f (b : P₀ L S 0))⁻¹ := by
  let P := P₀ L S 0
  let N := pCore 2 P
  obtain ⟨f,d,hf⟩ := original_bTwo_field_four_alpha_model
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hn : (B₀ L S).subgroupOf P ≤ normalizer (N : Set P) := by
    intro b hb
    have htop : (⊤ : Subgroup P) ≤ normalizer (N : Set P) := le_normalizer_of_normal
    exact htop (show (b : P) ∈ (⊤ : Subgroup P) from trivial)
  refine ⟨f,d,hn,hf,?_⟩
  intro b q
  change f ((b : P) * (q : P) * (b : P)⁻¹) = _
  rw [map_mul, map_mul, map_inv]


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
