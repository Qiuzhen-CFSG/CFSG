module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourRootSource
public import Theory.SpecificGroups.PSL3Four.CubicRootPlanes
public import Theory.GroupTheory.ElementaryFourComplement

/-!
# The two actual Cartan-invariant complements in the field-four branch

Recognize the original alpha core as UT₃(F₄), then take its two elementary
sixteen-groups. The original cubic Cartan preserves each. Coprime action
splits off the actual alpha center in each plane, producing two distinct
invariant four-groups inside the original alpha core.

The involution-intersection theorem makes both four-groups disjoint from
the original beta core. The exact orders then show that each supplements
that core to the full Borel two-core. The Cartan remains marked in the full
original Borel and beta enlargement, with its original Borel complement
identity. This discharges the two-complement premise of DGS (5.16).
The extension splitting and full J₂ parabolic recognition remain separate
steps, with the earlier natural-center and (7.4) premises still explicit.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), (5.16),
pp.116--117, and the field-four case of (10.9), p.163.
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
local instance complementSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

theorem original_bTwo_field_four_invariant_complements
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
    ∃ a : commonBorel L S, orderOf a = 3 ∧
      (a : G) ∈ centralizer ((Z F₀ α).map (G₀ L S).subtype : Set G) ∧
      (a : G) ∈ enlargedEndpoint L S 1 ∧
      Disjoint ((commonBorel L S).pCoreIn 2) (zpowers (a : G)) ∧
      (commonBorel L S).pCoreIn 2 ⊔ zpowers (a : G) =
        enlargedEndpoint L S 1 ⊓ commonBorel L S ∧
      ∃ A B : Subgroup G, A ≠ B ∧
        (∀ D ∈ ({A,B} : Set (Subgroup G)), D ≤ Q₀ ∧ Nat.card D = 4 ∧
          IsElementaryAbelian 2 D ∧ Disjoint Q₁ D ∧
          Q₁ ⊔ D = (commonBorel L S).pCoreIn 2 ∧
          (a : G) ∈ normalizer (D : Set G)) := by
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₀ := (Z F₀ α).map (G₀ L S).subtype
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 (parabolic L S 0)))
    (inclusion_injective _)
  obtain ⟨eroot⟩ := original_bTwo_field_four_alpha_root h hb c hactor hcentral
    ht hne hcomm hnot e hD E hK
  obtain ⟨a,ha,hac,haL,haU,hd,hgen,hfactors⟩ := original_bTwo_field_four_centralizing_cartan
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hnormal (i : Fin 2) : parabolic L S i ≤ normalizer ((parabolic L S i).pCoreIn 2 : Set G) := by
    change parabolic L S i ≤ normalizer
      (((pCore 2 (parabolic L S i)).map (parabolic L S i).subtype : Subgroup G) : Set G)
    have hh := (pCore 2 (parabolic L S i)).le_normalizer_map (parabolic L S i).subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  let an : normalizer (Q₀ : Set G) := ⟨a,hnormal 0 (commonBorel_le_parabolic 0 a.property)⟩
  let φ := Q₀.normalizerMonoidHom an
  have han : an ^ 3 = 1 := Subtype.ext
    (congrArg (fun x : commonBorel L S => (x : G)) (ha ▸ pow_orderOf_eq_one a))
  have hφ : φ ^ 3 = 1 := by
    change (Q₀.normalizerMonoidHom an) ^ 3 = 1
    rw [←map_pow,han,map_one]
  obtain ⟨hinv₁,hinv₂⟩ := Theory.GroupTheory.HyperbolicRecognition.cubic_preserves_transported_planes eroot φ hφ
  let E₁ := Theory.GroupTheory.HyperbolicRecognition.transportedPlane₁ eroot
  let E₂ := Theory.GroupTheory.HyperbolicRecognition.transportedPlane₂ eroot
  let T := zpowers (a : G)
  have hT : Nat.card T = 3 := by
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,ha]
  let : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; decide)
  have hcop : Nat.Coprime 2 (Nat.card T) := by rw [hT]; decide
  obtain ⟨hQ,hZa,hder,hPhi,hsq⟩ := original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  change (center Q₀).map Q₀.subtype = Z₀ at hZa
  obtain ⟨hI,hZcard,_,_⟩ := original_bTwo_field_four_anisotropic_intersection
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hZ : Nat.card Z₀ = 4 := by
    rw [←hZa,card_map_of_injective Q₀.subtype_injective]
    exact hZcard
  have hTZ : T ≤ normalizer (Z₀ : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hac)
  have hQ₀S : Q₀ ≤ (commonBorel L S).pCoreIn 2 := by
    rw [original_bTwo_borel_core_eq_product h c]
    exact le_sup_left
  have hnQ : Q₀ ≤ normalizer (Q₁ : Set G) :=
    hQ₀S.trans ((pCoreIn_le 2 _).trans ((commonBorel_le_parabolic 1).trans (hnormal 1)))
  have hplanes : E₁ ⊓ E₂ = center Q₀ := Theory.GroupTheory.HyperbolicRecognition.transportedPlanes_inf eroot
  have construct (V : Subgroup Q₀) [IsElementaryAbelian 2 V]
      (hV : Nat.card V = 16) (hZV : center Q₀ ≤ V)
      (hinv : V.map φ.toMonoidHom = V) :
      ∃ D : Subgroup G, D ≤ Q₀ ∧ Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
        Disjoint Q₁ D ∧ Q₁ ⊔ D = (commonBorel L S).pCoreIn 2 ∧
        (a : G) ∈ normalizer (D : Set G) ∧ Z₀ ⊔ D = V.map Q₀.subtype := by
    let V₀ := V.map Q₀.subtype
    let : Finite V₀ := Finite.of_injective (inclusion (map_subtype_le V)) (inclusion_injective _)
    let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.map Q₀.subtype
    have hV₀ : Nat.card V₀ = 16 := by rw [card_map_of_injective Q₀.subtype_injective,hV]
    have hZV₀ : Z₀ ≤ V₀ := hZa ▸ map_mono hZV
    have hTV : T ≤ normalizer (V₀ : Set G) := by
      apply zpowers_le.mpr
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hh : (MulAut.conj (a : G)).toMonoidHom.comp Q₀.subtype =
          Q₀.subtype.comp φ.toMonoidHom := by ext x; rfl
      change (V.map Q₀.subtype).map (MulAut.conj (a : G)).toMonoidHom = _
      rw [map_map,hh,←map_map,hinv]
    obtain ⟨D,hDV,hDc,hDe,hdZD,hDVgen,hTD⟩ := Theory.GroupTheory.invariant_four_complement
      V₀ Z₀ T hZV₀ hV₀ hZ hcop hTV hTZ
    have hDQ : D ≤ Q₀ := hDV.trans (map_subtype_le V)
    have hIZ := original_bTwo_field_four_elementary_intersection h hb c hactor
      hcentral ht hne hcomm hnot e hD E hK D hDQ hDe
    have hdQD : Disjoint Q₁ D := by
      apply Subgroup.disjoint_def.mpr
      intro x hxR hxD
      have hxZ : x ∈ Z₀ := (show x ∈ D ⊓ Z₀ from hIZ ▸ ⟨hxD,hxR⟩).2
      exact Subgroup.disjoint_def.mp hdZD hxZ hxD
    have hDgen := Theory.GroupTheory.sup_eq_of_disjoint_four Q₀ Q₁ D hQ hI hDQ hDc hdQD hnQ
    rw [sup_comm Q₁ Q₀,←original_bTwo_borel_core_eq_product h c] at hDgen
    exact ⟨D,hDQ,hDc,hDe,hdQD,hDgen,hTD (mem_zpowers _),hDVgen⟩
  obtain ⟨D₁,hD₁,hc₁,he₁,hd₁,hg₁,hn₁,hz₁⟩ := construct E₁
    (Theory.GroupTheory.HyperbolicRecognition.card_transportedPlane₁ eroot)
    (hplanes ▸ inf_le_left) hinv₁
  obtain ⟨D₂,hD₂,hc₂,he₂,hd₂,hg₂,hn₂,hz₂⟩ := construct E₂
    (Theory.GroupTheory.HyperbolicRecognition.card_transportedPlane₂ eroot)
    (hplanes ▸ inf_le_right) hinv₂
  refine ⟨a,ha,hac,haL,hd,hgen,D₁,D₂,?_,?_⟩
  · intro heq
    apply Theory.GroupTheory.HyperbolicRecognition.transportedPlanes_ne eroot
    apply map_injective Q₀.subtype_injective
    exact hz₁.symm.trans ((congrArg (Z₀ ⊔ ·) heq).trans hz₂)
  · intro D hDmem
    rcases hDmem with rfl | hDmem
    · exact ⟨hD₁,hc₁,he₁,hd₁,hg₁,hn₁⟩
    · have heq : D = D₂ := hDmem
      subst D
      exact ⟨hD₂,hc₂,he₂,hd₂,hg₂,hn₂⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
