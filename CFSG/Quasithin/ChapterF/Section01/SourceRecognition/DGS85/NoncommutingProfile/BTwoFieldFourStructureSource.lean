module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCartanSource
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Original field-four core structure and the centralizing Cartan

The constructed quintic actor supplies extraspeciality and the elementary
rank bound for the original beta core. Transport through the literal
reduced-completion inclusion proves that the original alpha core is special
of order sixty-four, with center, derived subgroup and Frattini subgroup
all equal to the image of Z_alpha.

Every involution in the intersection of the two full original cores lies
in this alpha center. Consequently an elementary alpha subgroup meets the
beta core exactly in its alpha-center part. The already constructed cubic
Cartan centralizes that center, complements the Borel two-core inside the
beta enlargement's Borel, and preserves every neighboring core intersection.
Both original endpoint maps, the full Borel, and the scalar/projective
quotient markings are retained.

These are inputs to the two invariant four-group complements in DGS (5.16).
Their construction, the extension splitting and J₂ parabolic recognition
remain obligations. The earlier natural-center and (7.4) commutator premises
remain explicit source inputs.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.16), pp.116--117, (10.9), p.163, and the original reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourStructureSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- Speciality and the involution intersection on the full original cores,
with extraspeciality and rank discharged by the original quintic actor. -/
theorem original_bTwo_field_four_structure
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
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Z₀ := (Z F₀ α).map (G₀ L S).subtype
    Nat.card Q₀ = 64 ∧
      (center Q₀).map Q₀.subtype = Z₀ ∧
      ⁅Q₀,Q₀⁆ = Z₀ ∧
      (frattini Q₀).map Q₀.subtype = Z₀ ∧
      ∀ x ∈ Q₀ ⊓ Q₁, x ^ 2 = 1 ↔ x ∈ Z₀ := by
  let ι := (G₀ L S).subtype
  have hmap₀ : (Q F₀ α).map ι = (parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective
    (inclusion (pCoreIn_le 2 (parabolic L S 1))) (inclusion_injective _)
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  have hk := (original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  obtain ⟨hExtra,⟨emodel⟩⟩ := original_bTwo_field_four_beta_recognition h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 Q₁ := hExtra
  let eQ : Q F₀ β ≃* Q₁ :=
    ((Q F₀ β).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_base_Q_map h true))
  have hExtraGraph : IsExtraspecial 2 (Q F₀ β) := IsExtraspecial.of_mulEquiv eQ.symm hExtra
  obtain ⟨hQa,hZa,hder,hPhi⟩ := c.field_four_alpha_special (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm.le hnot eβ hD' E hk hK hExtraGraph
  change Nat.card (Q F₀ α) = 64 at hQa
  change (center (Q F₀ α)).map (Q F₀ α).subtype = Z F₀ α at hZa
  change (commutator (Q F₀ α)).map (Q F₀ α).subtype = Z F₀ α at hder
  change (frattini (Q F₀ α)).map (Q F₀ α).subtype = Z F₀ α at hPhi
  have hcenter := map_center_image_of_injective (Q F₀ α) ι (G₀ L S).subtype_injective
  rw [reduced_base_Q_map h false,←map_map,hZa] at hcenter
  have hderived : ⁅(parabolic L S 0).pCoreIn 2,(parabolic L S 0).pCoreIn 2⁆ =
      (Z F₀ α).map ι := by
    have hh := congrArg (map ι) hder
    rw [map_subtype_commutator,map_commutator,reduced_base_Q_map h false] at hh
    exact hh
  have hPhi₀ := frattini_image_map (Q F₀ α) ι (G₀ L S).subtype_injective
  rw [reduced_base_Q_map h false,hPhi] at hPhi₀
  have hcard₁ : Nat.card Q₁ = 32 :=
    (Nat.card_congr emodel.toEquiv).trans MinusExtraspecial.card_model
  have hphi₁ : Nat.card (frattini Q₁) = 2 := by
    rw [IsExtraspecial.frattini_eq_center (p := 2),IsExtraspecial.center_order_p 2 Q₁]
  have hnon : ¬ IsMulCommutative Q₁ := by
    intro ha
    have he := (commutator_eq_bot_iff Q₁).mpr ha
    rw [IsExtraspecial.commutator_eq_center (p := 2)] at he
    have hh := congrArg (fun H : Subgroup Q₁ => Nat.card H) he
    rw [IsExtraspecial.center_order_p 2 Q₁,card_bot] at hh
    omega
  obtain ⟨_,_,a,ha,_,_⟩ := original_field_four_beta_frattini_actor h e hK
  have hrank₁ := Theory.GroupTheory.QuinticFrattini.elementary_card_lt_eight
    (show IsPGroup 2 Q₁ from isPGroup_pCoreIn 2 (parabolic L S 1))
    hnon hcard₁ hphi₁ a ha
  have hrank : ∀ A : Subgroup (Q F₀ β), IsElementaryAbelian 2 A → Nat.card A < 8 := by
    intro A hA
    let := hA
    have hh := hrank₁ (A.map eQ.toMonoidHom) (IsElementaryAbelian.map _)
    rwa [card_map_of_injective eQ.injective] at hh
  have hsq := c.square_one_intersection (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb E
    (c.omega_eq_bot_of_central_neighbor (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hactor hcentral) hk hrank
  refine ⟨?_,hcenter,hderived,hPhi₀,?_⟩
  · rw [←hmap₀,card_map_of_injective (G₀ L S).subtype_injective]
    exact hQa
  · intro x hx
    have hxmap : x ∈ (Q F₀ α).map ι := (reduced_base_Q_map h false).symm ▸ hx.1
    obtain ⟨y,hy,he⟩ := hxmap
    have hyβ : y ∈ Q F₀ β := by
      have hyMap : ι y ∈ (Q F₀ β).map ι := by
        rw [reduced_base_Q_map h true,he]
        exact hx.2
      obtain ⟨z,hz,hzy⟩ := hyMap
      exact (G₀ L S).subtype_injective hzy ▸ hz
    constructor
    · intro hxx
      have hyy : y ^ 2 = 1 := (G₀ L S).subtype_injective (by
        change ι (y^2) = ι 1
        rw [map_pow,map_one,he]
        exact hxx)
      exact ⟨y,(hsq y ⟨hyβ,hy⟩).mp hyy,he⟩
    · intro hxZ
      obtain ⟨z,hz,rfl⟩ := hxZ
      let : IsElementaryAbelian 2 (Z F₀ α) := graph_Z_elementary (reduced_triple h) α
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian z hz,map_one]

/-- Every actual elementary alpha subgroup meets the beta core precisely in its alpha-center part. -/
theorem original_bTwo_field_four_elementary_intersection
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) (A : Subgroup G)
    (hA : A ≤ (parabolic L S 0).pCoreIn 2) (hE : IsElementaryAbelian 2 A) :
    A ⊓ (parabolic L S 1).pCoreIn 2 = A ⊓ (Z F₀ α).map (G₀ L S).subtype := by
  have hs := original_bTwo_field_four_structure h hb c hactor hcentral ht hne hcomm
    hnot e hD E hK
  let := hE
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1,(hs.2.2.2.2 x ⟨hA hx.1,hx.2⟩).mp
      (elemPow_eq_one_of_isElementaryAbelian x hx.1)⟩
  · have hZQ : (Z F₀ α).map (G₀ L S).subtype ≤ (parabolic L S 1).pCoreIn 2 := by
      rw [←hD]
      exact inf_le_left
    exact inf_le_inf_left A hZQ

/-- The constructed original Cartan centralizes the alpha center as well as preserving every neighboring core factor. -/
theorem original_bTwo_field_four_centralizing_cartan
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
    ∃ a : commonBorel L S, orderOf a = 3 ∧
      (a : G) ∈ centralizer ((Z F₀ α).map (G₀ L S).subtype : Set G) ∧
      (a : G) ∈ enlargedEndpoint L S 1 ∧
      (a : G) ∈ (U F₀ α).map (G₀ L S).subtype ∧
      Disjoint ((commonBorel L S).pCoreIn 2) (zpowers (a : G)) ∧
      (commonBorel L S).pCoreIn 2 ⊔ zpowers (a : G) =
        enlargedEndpoint L S 1 ⊓ commonBorel L S ∧
      ∀ μ, (graph F₀).Adj α μ →
        (Q F₀ μ).map (G₀ L S).subtype = (V F₀ μ 1).map (G₀ L S).subtype ∧
        (a : G) ∈ normalizer
          (((Q F₀ μ).map (G₀ L S).subtype ⊓ (parabolic L S 0).pCoreIn 2 : Subgroup G) : Set G) := by
  let ι := (G₀ L S).subtype
  obtain ⟨a,hoa,hL,hU,hd,hgen,hfactors⟩ := original_bTwo_field_four_cartan
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨g,hg,hga⟩ := hU
  have hα : g ∈ stabilizer F₀ α := (ballKernel_one_le_edge F₀ c.middle hg).1
  have hβ : g ∈ graphLocalGroup F₀ β := by
    have hm : ι g ∈ (graphLocalGroup F₀ β).map ι := by
      rw [reduced_graphLocalGroup_image h true,hga]
      exact hL
    obtain ⟨x,hx,hxg⟩ := hm
    exact (G₀ L S).subtype_injective hxg ▸ hx
  have hcube : g ^ 3 = 1 := (G₀ L S).subtype_injective (by
    change ι (g^3) = ι 1
    rw [map_pow,map_one,hga]
    exact congrArg (fun x : commonBorel L S => (x : G))
      (show a^3=1 from hoa ▸ pow_orderOf_eq_one a))
  have hk := (original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  have hc := c.binary_beta_cubic_centralizes_center (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hcentral
    (base_Z_ne_bot (reduced_triple h) true) E
    (c.omega_eq_bot_of_central_neighbor (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hactor hcentral) hk g hα hβ hcube
  refine ⟨a,hoa,?_,hL,⟨g,hg,hga⟩,hd,hgen,hfactors⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  change ι y * (a : G) = (a : G) * ι y
  rw [←hga,←map_mul,←map_mul]
  exact congrArg ι (hc y hy)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
