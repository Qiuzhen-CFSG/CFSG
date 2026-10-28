module
public import Theory.Representation.BinaryConjugationSection.FullLinearCoordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import CFSG.Quasithin.ChapterF.Section09.QuinticCoreEscape
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs

/-!
# Constructing the original natural four-space marking

F.9.2 gives a faithful action of H/O₂(H) on the literal U_H/V₁. The source
orders |U_H|=32 and |V₁|=2 make this a four-space. Its faithful image fills
GL₄(2) by equality of orders. Choosing coordinates sends the actual V₂/V₁
line to the first coordinate line; composing with GL₄(2)≃SL₄(2) gives the
matrix marking used by the linear-four calculations.

The given group isomorphism supplies only the order comparison. The
intertwining marking is constructed from the original conjugation action,
through the canonical H→H/O₂(H), with literal kernel V₁. No prior natural
representation or point marking is assumed. The earlier 13.8.27 orders
and quotient remain the input of qt-d-138-six-g2-source; the compatible
exterior and tensor markings remain obligations of this linear-four task.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
F.9.2(3),13.8.27(1b),13.8.29, printed pp.318,963--964.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- Construct the natural action, with the original point sent to the first coordinate. -/
theorem source_natural_point_marking
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 : Subgroup G) (h12 : F.V₁ ≤ V2) (h2U : V2 ≤ F.UH) (h2 : Nat.card V2 = 4) :
    ∃ (ρ : Representation (ZMod 2) F.H (Space 4))
      (d : BinaryConjugationSection F.H F.UH F.V₁ ρ)
      (π : F.H →* SL(4,ZMod 2)),
      π.ker = (Source.QH F.H).subgroupOf F.H ∧ Function.Surjective π ∧
      (∀ h w, ρ h w = Matrix.mulVec (π h).val w) ∧
      d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1} := by
  let : (F.V₁.subgroupOf F.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨σ,c,hfaith,hcoord⟩ := hF.faithful_UH_section
  let W := Additive (F.UH ⧸ F.V₁.subgroupOf F.UH)
  have hW : Nat.card W = 16 := by
    have hh := c.card_section
    rw [hU,hF.point_card] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  have hdim : Module.finrank (ZMod 2) W = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [Nat.card_zmod,hW] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  let E₀ : W ≃ₗ[ZMod 2] Space 4 := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  have hidx : F.V₁.relIndex V2 = 2 := by
    have hh := (F.V₁.subgroupOf V2).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h12).toEquiv,hF.point_card,h2] at hh
    change 2 * F.V₁.relIndex V2 = 4 at hh
    omega
  have hline := c.imageSpace_finrank_of_index V2 h2U 1 (by simpa using hidx)
  have hne : c.imageSpace V2 ≠ ⊥ := by
    intro he
    have hz : Module.finrank (ZMod 2) (c.imageSpace V2) = 0 :=
      Submodule.finrank_eq_zero.mpr he
    omega
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  have he0 : (Pi.single 0 1 : Space 4) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  obtain ⟨g,hg⟩ := exists_linearEquiv_apply_eq
    (show E₀ v ≠ 0 from fun he => hv0 (E₀.injective (he.trans (map_zero E₀).symm))) he0
  let E := E₀.trans g
  let q := QuotientGroup.mk' (pCore 2 F.H)
  obtain ⟨e,d,hd⟩ := BinaryConjugationSection.full_linear_coordinates q c hfaith E (Nat.card_congr e₀.toEquiv)
  let φ := e.toMonoidHom.comp q
  let ρ : Representation (ZMod 2) F.H (Space 4) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp φ
  let π := (slEquivLinear 4).symm.toMonoidHom.comp φ
  have hk : π.ker = pCore 2 F.H := by
    dsimp only [π,φ,q]
    rw [MonoidHom.ker_comp_of_injective _ _ (slEquivLinear 4).symm.injective,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  refine ⟨ρ,d,π,?_,(slEquivLinear 4).symm.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _)),?_,?_⟩
  · rw [hk]
    exact (comap_map_eq_self_of_injective F.H.subtype_injective _).symm
  · intro h w
    change φ h w = Matrix.mulVec ((slEquivLinear 4).symm (φ h)).val w
    rw [←slEquivLinear_apply,(slEquivLinear 4).apply_symm_apply]
  · have hv' : (Pi.single 0 1 : Space 4) ∈ d.imageSpace V2 := by
      obtain ⟨x,hx,hxv⟩ := (c.mem_imageSpace_iff V2 v).mp hv
      apply (d.mem_imageSpace_iff V2 _).mpr
      exact ⟨x,hx,(hd x).trans (by rw [hxv]; exact hg)⟩
    exact eq_span_singleton_of_mem_of_finrank_eq_one
      (d.imageSpace_finrank_of_index V2 h2U 1 (by simpa using hidx)) hv' he0

end CFSG.Quasithin.Chapter13.Section08.LinearFour
