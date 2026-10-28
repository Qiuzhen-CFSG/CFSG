module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ParabolicTransport
public import Theory.Representation.SmallDisplacementParabolics.PairedNatural

/-!
# The paired-natural branch of the partner-core contradiction

The plane parabolic in each binary three-space gives a moving parabolic in
the full factor-exchanging action. Its Sylow containment, minimality and
literal two-residual movement are constructed by the model theorem. The
quotient transport applies these conclusions to the actual KcT/O₂(KcT).

The marked faithful chief action and its nonzero projected plane vector
remain inputs of this conditional branch. Their construction and the final
partner-core assembly belong to qt-e-152-critical-pair. No moving-parabolic
or residual-movement premise remains.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119 (PDF p.1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
open Representation.SmallDisplacementParabolics
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The paired natural module gives the contradiction on the original partner quotient. -/
theorem source_chosen_false_of_paired_partner_core_quotient
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let S := (T.subtype (show (T : Subgroup G) ≤ L from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 L))
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W) (w : W), w ≠ 0 →
      (∃ e : (L ⧸ pCore 2 L) ≃* PairedActor,
        ∃ E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
          ∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i))) →
      (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w) →
      (∀ g ∈ (S : Subgroup (L ⧸ pCore 2 L)), ρ g w = w) → False := by
  dsimp only
  intro ρ w hw hmodel hfix hSylow
  obtain ⟨e, E, hE⟩ := hmodel
  obtain ⟨d⟩ := PairedNatural.exists_of_equiv ρ e E hE _ w hw hSylow
  exact source_chosen_false_of_partner_core_quotient h hg hMc hplane ρ w hfix d

end CFSG.Quasithin.Chapter15.Section02
