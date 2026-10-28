module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySection
public import CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition.Source
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Recognizing the escaping section from its field-four index

The actual G.2.3 marking is transported coefficientwise to the concrete
field of order four, preserving the point and conjugation equations.
The proved field-four projective criterion then gives a direct sum of
natural planes on the literal R/E. Its multiplicity determines both
relative indices and the order of U. When |C_U(V_L):E| = 4, that
multiplicity is one, yielding the genuine equivariant natural section.

This discharges the module-recognition step of 6.1.25(3) from the source
parameter, nonabelianness and marked index. These numerical and geometric
inputs, the initial natural action and PSL₂ component selection remain
with qt-d-1222-rankone-recognition-natural. No universal recognition
callback is required, and no escaping input is asserted here.

Source: Aschbacher–Smith, 6.1.21(4), 6.1.24(2), 6.1.25(3), pp.675–678,
using G.1.3 and G.2.3, pp.327,333–334.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterG.Section02.RankOneHigherFields
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private def columnEquiv {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) : (Fin 2 → F) ≃ₛₗ[(e : F →+* K)] (Fin 2 → K) where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by funext i; exact e.symm_apply_apply (v i)
  right_inv v := by funext i; exact e.apply_symm_apply (v i)
  map_add' v w := by funext i; exact e.map_add (v i) (w i)
  map_smul' a v := by funext i; exact e.map_mul a (v i)

private theorem four_marking {D : ChapterG.Section02.Setup G}
    {F : Type*} [Field F] [Finite F] {l : G} (d : Hypothesis D F 2 l) :
    Nonempty (Hypothesis D F4 2 l) := by
  let := Fintype.ofFinite F
  let e : F ≃+* F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, d.field_card, field_card]
    norm_num)
  let c := columnEquiv e
  let P := d.point.map c.toLinearMap
  have hcard : Nat.card P = 4 := by
    rw [← Nat.card_congr (c.submoduleMap d.point).toEquiv,
      Module.natCard_eq_pow_finrank (K := F), d.point_dimension, pow_one, d.field_card]
    norm_num
  have hdim : Module.finrank F4 P = 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 4)
    change 4 ^ Module.finrank F4 P = 4 ^ 1
    rw [← field_card, ← Module.natCard_eq_pow_finrank, hcard, pow_one, field_card]
  refine ⟨{ d with
    field_card := by simpa using field_card
    model := d.model.trans (Atlas.fieldEquivSL 2 e)
    coordinates := d.coordinates.trans (AddEquiv.toMultiplicative c.toAddEquiv)
    equivariant := ?_
    point := P
    point_dimension := hdim
    point_mem := ?_ }⟩
  · intro a v
    change c (d.coordinates _).toAdd = _
    rw [d.equivariant]
    funext i
    change e (∑ j, (d.model (starProjection D a)).val i j * (d.coordinates v).toAdd j) = _
    simp only [map_sum, map_mul]
    rfl
  · intro v
    change (v : G) ∈ D.V₁ ↔ c (d.coordinates v).toAdd ∈ d.point.map c.toLinearMap
    rw [d.point_mem]
    rw [Submodule.mem_map_equiv, c.symm_apply_apply]


private theorem section_model_of_four_index {D : ChapterG.Section02.Setup G}
    {l : G} (d : Hypothesis D F4 2 l) (hut : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hindex : (D.S₂ l).relIndex (D.W l) = 4) :
    Nonempty (Escape.NaturalSectionModel (D.I l) (D.S l) (D.S₂ l) F4) := by
  let hn := d.quotientIntersection_normal hut hf
  let := hn
  have hstar := d.star_I_eq_star_L hut hf
  have hsplit := d.S_eq_WProduct_of_source hut hf
  let := d.quotient_elementary hut hf hstar hsplit
  obtain ⟨σ,c,φ,_,hcrit,_,_⟩ := d.exists_quotient_projective_map hut hf hstar
    (d.exists_star_U_sylow hut hf) (d.star_L₁_eq_normalizer hut hf) hsplit
  let : Module (ZMod 2) F4 := @Algebra.toModule (ZMod 2) F4 _ _ (ZMod.algebra F4 2)
  obtain ⟨s,e,he⟩ := ChapterG.Section01.SL2FourRecognition.naturalCopies hcrit
  have hc := d.quotient_mark_index hut hf hstar hsplit σ c s e.toEquiv
  have hexp : 2 * s = 2 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ (2 * s) = 2 ^ 2
    rw [←hc,hindex]
  have hs : s = 1 := by omega
  subst s
  let v := e.toAddEquiv.trans (AddEquiv.funUnique (Fin 1) (Fin 2 → F4))
  let f := c.quotientEquiv.trans (AddEquiv.toMultiplicative v)
  have hR : ((D.S l).subgroupOf (D.I l)).Normal := (d.series hut hf).2.2.2.2.1
  let := hR
  have hk : (D.S l).subgroupOf (D.I l) = pCore 2 (D.I l) :=
    (pCore 2 (D.I l)).comap_map_eq_self_of_injective (D.I l).subtype_injective
  let a := (QuotientGroup.quotientMulEquivOfEq hk).trans (d.generatedCoreQuotientEquiv hut hf)
  refine ⟨{
    R_le := pCoreIn_le 2 (D.I l)
    E_le := (d.series hut hf).2.1
    R_normal := hR
    E_normal := hn
    actor := a
    vectors := f
    intertwining := ?_ }⟩
  intro j r
  change f (QuotientGroup.mk' ((D.S₂ l).subgroupOf (D.S l)) _) = _
  apply Multiplicative.toAdd.injective
  change v (c.quotientEquiv (QuotientGroup.mk' ((D.S₂ l).subgroupOf (D.S l)) _)).toAdd = _
  rw [c.quotientEquiv_mk,c.equivariant]
  exact he (d.quotientActionProjection hut hstar j) (c.coordinates r).toAdd 0

private theorem four_marked_indices {D : ChapterG.Section02.Setup G}
    {l : G} (d : Hypothesis D F4 2 l) (hut : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ∃ s : ℕ, (D.S₂ l).relIndex (D.W l) = 2 ^ (2 * s) ∧
      Nat.card D.U = 2 ^ (2 * (s + 3)) * D.V.relIndex (D.S₂ l) := by
  let := d.quotientIntersection_normal hut hf
  have hstar := d.star_I_eq_star_L hut hf
  have hsplit := d.S_eq_WProduct_of_source hut hf
  let := d.quotient_elementary hut hf hstar hsplit
  obtain ⟨σ,c,φ,_,hcrit,_,_⟩ := d.exists_quotient_projective_map hut hf hstar
    (d.exists_star_U_sylow hut hf) (d.star_L₁_eq_normalizer hut hf) hsplit
  let : Module (ZMod 2) F4 := @Algebra.toModule (ZMod 2) F4 _ _ (ZMod.algebra F4 2)
  obtain ⟨s,e,_⟩ := ChapterG.Section01.SL2FourRecognition.naturalCopies hcrit
  have hi := d.quotient_mark_index hut hf hstar hsplit σ c s e.toEquiv
  exact ⟨s,hi,d.order_of_natural_indices hut hf hstar (d.card_star_U hut hf) s hi⟩

variable {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G}

/-- Recognize the literal R/E action from the source parameter and marked index. -/
theorem natural_escape_section_of_index_four
    (h : Hypothesis611 κ T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hindex : (Escape.E (T : Subgroup G) L V l).relIndex
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 4) :
    Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L V l)
      (Escape.R (T : Subgroup G) L V l) (Escape.E (T : Subgroup G) L V l) := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨d₄⟩ := four_marking d
  obtain ⟨hU,hI,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
  have hf := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hW : D.W l = Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G) := by
    change D.U ⊓ D.S l = _
    rw [d.S_eq_star_kernel hut hf, ← inf_assoc,
      inf_eq_left.mpr (show D.U ≤ D.I l from le_sup_left)]
    change D.U ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [← local_layer_centralizer_eq_core h hnatural, ← inf_assoc,
      inf_eq_left.mpr (show D.U ≤ L ⊔ (T : Subgroup G) from hut.trans le_sup_right), hU]
  have hi : (D.S₂ l).relIndex (D.W l) = 4 := by rw [hE',hW]; exact hindex
  have hm := section_model_of_four_index d₄ hut hf hi
  rw [hI,hR,hE'] at hm
  exact ⟨F4,inferInstance,inferInstance,inferInstance,field_card,hm⟩

/-- The actual field-four section has one common multiplicity in both
relative indices and the order of its conjugate closure. -/
theorem natural_escape_four_multiplicity
    (h : Hypothesis611 κ T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    ∃ s : ℕ,
      (Escape.E (T : Subgroup G) L V l).relIndex
        (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 2 ^ (2 * s) ∧
      (Escape.E (T : Subgroup G) L V l).relIndex (Escape.R (T : Subgroup G) L V l) =
        2 ^ (4 * s) ∧
      Nat.card (Escape.U (T : Subgroup G) L V) =
        2 ^ (2 * (s + 3)) * (layer L V).relIndex (Escape.E (T : Subgroup G) L V l) := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨d₄⟩ := four_marking d
  obtain ⟨hU,hI,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
  have hf := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hW : D.W l = Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G) := by
    change D.U ⊓ D.S l = _
    rw [d.S_eq_star_kernel hut hf, ← inf_assoc,
      inf_eq_left.mpr (show D.U ≤ D.I l from le_sup_left)]
    change D.U ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [← local_layer_centralizer_eq_core h hnatural, ← inf_assoc,
      inf_eq_left.mpr (show D.U ≤ L ⊔ (T : Subgroup G) from hut.trans le_sup_right), hU]
  obtain ⟨s,hi,hcard⟩ := four_marked_indices d₄ hut hf
  rw [hE',hW] at hi
  change Nat.card D.U = 2 ^ (2 * (s + 3)) * (layer L V).relIndex (D.S₂ l) at hcard
  rw [hU,hE'] at hcard
  refine ⟨s,hi,?_,hcard⟩
  rw [← natural_escape_core_index_square h hnatural hE hNS hnon hl hlout,hi,← pow_mul]
  congr 1
  omega

end
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
