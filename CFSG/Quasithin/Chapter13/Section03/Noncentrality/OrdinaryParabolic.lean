module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import Theory.GroupTheory.CoprimeCentralizerImage
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Ordinary parabolic inputs for reduction 13.3.14(c)

The actual point residual X is two-perfect and X/O₂(X) has order three.
If its two-core centralized the seed V₃, its action would have odd order.
Coprime splitting would then contradict both [V₃,X]=V₃ and the fixed line
V₁ of order two. Thus O₂(X) moves V₃, and the literal star projection gives
reduction (c) whenever O₂(G₁) centralizes the seed.

Source: Aschbacher–Smith, Lemma 13.3.14(c), printed pp.891–892;
the preceding natural point-residual calculation is 13.7.5(2), p.938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section07.ModelExclusions
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

omit d in
/-- The original point residual is two-perfect. -/
theorem ordinary_point_residual_twoPerfect : IsPPerfect 2 (sourceOne L T V₁) :=
  residual_isPPerfect _

/-- The ordinary six-letter quotient gives the intrinsic cubic quotient of X. -/
theorem ordinary_point_residual_quotient_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Nat.card (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 3 := by
  rcases NaturalModels.quotient_alternatives d with ⟨e', he⟩ | ⟨e', he⟩
  · obtain ⟨a⟩ := NaturalModels.ordinary_natural d e' he
    exact Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.source_residual_quotient_card a _ rfl
  · have hc := Nat.card_congr (centerCongr (e'.symm.trans e)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp), card_bot] at hc
    omega

/-- The original two-core acts nontrivially on the actual seed. -/
theorem ordinary_point_core_moves_seed
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ¬ (sourceOne L T V₁).pCoreIn 2 ≤ centralizer (V₃ : Set G) := by
  intro hc
  let X := sourceOne L T V₁
  let f := V₃.normalizerMonoidHom.comp (inclusion (point_residual_normalizes_seed d))
  have hk : pCore 2 X ≤ f.ker := by
    intro x hx
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    have he := mem_centralizer_iff.mp (hc (mem_map_of_mem X.subtype hx)) v v.property
    change (v:G) * (x:G) = (x:G) * (v:G) at he
    change (x:G) * (v:G) * (x:G)⁻¹ = (v:G)
    rw [←he, mul_inv_cancel_right]
  let fbar := QuotientGroup.lift (pCore 2 X) f hk
  have hr : fbar.range = f.range := by
    ext a
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
      exact ⟨x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 X) x,rfl⟩
  have hdiv : Nat.card f.range ∣ 3 := by
    rw [←hr, ←ordinary_point_residual_quotient_card d e]
    exact card_range_dvd fbar
  let := Section07.NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  have hcop : Nat.Coprime (Nat.card f.range) (Nat.card V₃) := by
    rw [d.seed_card]
    exact (by decide : Nat.Coprime 3 8).coprime_dvd_left hdiv
  have hd := commutator_disjoint_centralizer_of_actionRange_coprime
    V₃ X (point_residual_normalizes_seed d) hcop
  rw [seed_commutator_point_residual d] at hd
  have hline : V₁ ≤ V₃ ⊓ centralizer (X : Set G) :=
    le_inf (d.line_le_plane.trans d.plane_le_seed)
      (le_centralizer_iff.mp (((one_le L T V₁).trans inf_le_right).trans
        (normalizer_le_centralizer_of_card_two V₁ d.line_card)))
  have hb : V₁ = ⊥ := le_bot_iff.mp
    ((le_inf (d.line_le_plane.trans d.plane_le_seed) hline).trans hd.le_bot)
  have ht := d.line_card
  rw [hb, card_bot] at ht
  omega

/-- Inclusion in the prescribed point normalizer, used by the star projection. -/
theorem ordinary_point_residual_le_point : sourceOne L T V₁ ≤ G₁ := by
  rw [d.first_normalizer]
  exact (one_le L T V₁).trans inf_le_right

/-- Reduction (c) for the literal ordinary parabolic, with its movement input discharged. -/
theorem ordinary_reduction_c
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hcentral : G₁.pCoreIn 2 ≤ centralizer (V₃ : Set G)) :
    pCore 2 (star G₁ (sourceOne L T V₁) (ordinary_point_residual_le_point d)) ≠ ⊥ :=
  reduction_c G₁ (sourceOne L T V₁) V₃ (ordinary_point_residual_le_point d)
    hcentral (ordinary_point_core_moves_seed d e)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
