module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.AlternatingLocals
public import Theory.GroupAction.SmallSylowCenter
public import Theory.Mathieu.M22.Properties.FixedHexadLocal
public import Theory.Mathieu.M22.Properties.HexadPointwise

/-!
# The original M₂₂ exclusion in E.6.8

The source involution fixes the original quotient Sylow subgroup pointwise.
It is inner, hence represented by its unique central involution. The actual
fixed hexad is therefore preserved by every Sylow-stabilizing automorphism.
Its stabilizer has characteristic two and two-kernel quotient A₆; central
component coordinates exclude every chi-zero block and E.6.7 places its
whole lift in M. Its generation by two-elements and the source residual
condition make the original involution fix the entire hexad stabilizer.
The checked native pointwise-fixer theorem makes that action trivial.
All choices use the original quotient map and retain its complete two-kernel.

Source: Aschbacher–Smith E.6.8, printed p.248 (PDF p.259), GLS3 Table 5.3c.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
open _root_.Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G} {K : GroupClass} {z : G}
open Chapter15.Section03.Candidates.ComponentStructure

theorem m22_excluded (h : HypothesisE61 K T M V)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) (e : (L ⧸ pCore 2 L) ≃* M22) : False := by
  obtain ⟨S,hS⟩ := component_sylow_intersection h hU hL
  let R := S.mapSurjective (f := modelMap e) (modelMap_surjective e)
  let a := modelAction e α
  have ho : orderOf a = 2 :=
    (orderOf_injective (modelAction e) (modelAction_injective hL e) α).trans ha.2.1
  have hi : a ∈ (MulAut.conj (G := M22)).range := by
    obtain ⟨l,hl⟩ := ha.1
    exact ⟨modelMap e l, by dsimp [a]; rw [← hl, modelAction_conj]⟩
  have hfix := modelAction_fixed_sylow e hz α hα S hS
  obtain ⟨t,ht,hta,htR⟩ := Theory.GroupAction.exists_inner_involution_in_sylow_center
    m22_center_eq_bot R a ho hi hfix
  let B := m22FixedPoints t
  have hB : B ∈ m22Blocks := m22FixedPoints_mem_blocks t ht
  let P := MulAction.stabilizer M22 B
  have hRP : (R : Subgroup M22) ≤ P := by
    apply le_trans _ (m22_centralizer_le_fixedPoints_stabilizer t)
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have he : a x = x := hfix x hx
    rw [← hta] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hinv (b : MulAut M22) (hb : (R : Subgroup M22).map b.toMonoidHom = R) :
      P.map b.toMonoidHom = P :=
    m22FixedPoints_stabilizer_map t ht b
      (Theory.GroupAction.fixes_small_sylow_center R (m22_sylow_center_card_le_two R) t htR b hb)
  let f := (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    (QuotientGroup.mk' (m22SetAction B).ker)
  have hf : Function.Surjective f := (m22HexadQuotientAlternatingEquiv hB).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (m22HexadQuotientAlternatingEquiv hB).injective,
      QuotientGroup.ker_mk']
    let := m22HexadKernel_elementaryAbelian hB
    exact IsElementaryAbelian.isPGroup 2 _
  have hplace := seedLift_le_M_of_central_coordinates h67 hU hL e m22_center_eq_bot S hS P
    hinv (m22Hexad_stabilizer_core_selfCentralizing hB)
    (by
      intro C _ hC n q hqc hqs
      exact no_chiZero_central_coordinates_alternating hC (Or.inl rfl) f hf hk q hqc hqs)
  have he : a = 1 := m22_automorphism_eq_one_of_fixes_hexad hB R hRP a
    (modelAction_fixes_placed_seed hU hL e P hplace
      (primeToResidual_top_of_alternating_two_kernel (Or.inl rfl) f hf hk) hz.1 α hα)
  rw [he,orderOf_one] at ho
  omega
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
