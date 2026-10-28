module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LinearObstruction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# Faithful normalizer action in the elementary-abelian branch

An element centralizing R normalizes B, so the actual product R T_R
and the faithful T_R action force C_G(R)=R when R is abelian. Thus
conjugation embeds the literal quotient N_G(R)/R in Aut(R), and the
proved elementary-abelian structure embeds it in the actual GL₃(3).
The existing linear-group obstruction then rules out a factor five and
order 208. OrbitIndex derives the contradictory order from the points.

Source: Aschbacher–Smith, final paragraph of J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup LocalAction
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable {hB : Nat.card c.B = 3}
variable {e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))}
variable (D : LocalAction.Data c hB e)

/-- In the elementary-abelian branch, R is self-centralizing in the original G. -/
theorem centralizer_eq_of_abelian (hc : IsMulCommutative (ambient c D.R)) :
    centralizer (ambient c D.R : Set G) = ambient c D.R := by
  let := hc
  have hRC : ambient c D.R ≤ centralizer (ambient c D.R : Set G) := by
    intro r hr x hx
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ambient c D.R) ⟨r, hr⟩)
  apply le_antisymm ?_ hRC
  intro g hg
  have hgN : g ∈ c.NB ⊓ normalizer (ambient c D.R : Set G) :=
    ⟨c.GB_le_NB (centralizer_le D.base_le hg), centralizer_le_normalizer _ hg⟩
  change g ∈ ((c.NB ⊓ normalizer (ambient c D.R : Set G) : Subgroup G) : Set G) at hgN
  rw [D.normalizer_product] at hgN
  obtain ⟨r, hr, t, ht, rfl⟩ := hgN
  have htC : t ∈ centralizer (ambient c D.R : Set G) := by
    have hh := (centralizer (ambient c D.R : Set G)).mul_mem
      ((centralizer (ambient c D.R : Set G)).inv_mem (hRC hr)) hg
    simpa only [inv_mul_cancel_left] using hh
  have ha : action c D.R D.Tplus ⟨t, ht⟩ = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change t * (x : G) * t⁻¹ = (x : G)
    rw [← htC x x.property, mul_inv_cancel_right]
  have ht1 : (⟨t, ht⟩ : TR c D.R D.Tplus) = 1 :=
    D.faithful (ha.trans (map_one _).symm)
  change r * t ∈ ambient c D.R
  rw [show t = 1 from congrArg Subtype.val ht1, mul_one]
  exact hr

/-- The quotient in the source is the literal normalizer modulo the original R. -/
abbrev AmbientNormalizerQuotient (R : Sylow 3 c.NB) :=
  normalizer (ambient c R : Set G) ⧸
    (ambient c R).subgroupOf (normalizer (ambient c R : Set G))

/-- Faithful conjugation of the actual quotient into Aut(R) in the abelian branch. -/
def abelianNormalizerAction (hc : IsMulCommutative (ambient c D.R)) :
    AmbientNormalizerQuotient c D.R →* MulAut (ambient c D.R) :=
  QuotientGroup.lift _ (ambient c D.R).normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, centralizer_eq_of_abelian c D hc])

theorem abelianNormalizerAction_mk (hc : IsMulCommutative (ambient c D.R))
    (g : normalizer (ambient c D.R : Set G)) (x : ambient c D.R) :
    (abelianNormalizerAction c D hc (QuotientGroup.mk' _ g) x : G) =
      (g : G) * (x : G) * (g : G)⁻¹ := rfl

theorem abelianNormalizerAction_injective (hc : IsMulCommutative (ambient c D.R)) :
    Function.Injective (abelianNormalizerAction c D hc) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, centralizer_eq_of_abelian c D hc]

/-- The normalizer quotient embeds in the actual GL₃(3), through its faithful
conjugation action on the original elementary abelian group R. -/
theorem exists_faithful_linear_action (hc : IsMulCommutative (ambient c D.R)) :
    ∃ ρ : AmbientNormalizerQuotient c D.R →* LinearThreeTernary.LinearGroup,
      Function.Injective ρ := by
  let := (D.abelian_points hc).1
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 3) (ambient c D.R) (by rw [D.r_card]; decide)
  exact ⟨LinearThreeTernary.matrixEquiv.toMonoidHom.comp
      (f.comp (abelianNormalizerAction c D hc)),
    LinearThreeTernary.matrixEquiv.injective.comp
      (hf.comp (abelianNormalizerAction_injective c D hc))⟩

/-- Five cannot divide the order of the source quotient in the abelian branch. -/
theorem abelian_normalizer_quotient_not_five (hc : IsMulCommutative (ambient c D.R)) :
    ¬ 5 ∣ Nat.card (AmbientNormalizerQuotient c D.R) := by
  obtain ⟨ρ, hρ⟩ := exists_faithful_linear_action c D hc
  exact normalizerQuotient_not_five_dvd_card c D.R ρ hρ

/-- The source quotient cannot have order 208 in the abelian branch. -/
theorem abelian_normalizer_quotient_ne_208 (hc : IsMulCommutative (ambient c D.R)) :
    Nat.card (AmbientNormalizerQuotient c D.R) ≠ 16 * 13 := by
  obtain ⟨ρ, hρ⟩ := exists_faithful_linear_action c D hc
  exact normalizerQuotient_card_ne_208 c D.R ρ hρ

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
