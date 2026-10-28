module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ParabolicTransport
public import Theory.Representation.SmallDisplacementParabolics.OrthogonalEight

/-!
# The orthogonal branch of the partner-core contradiction

The concrete eight-point calculation constructs the moving parabolic from
an actual group isomorphism, intertwining map and nonzero Sylow-fixed vector.
The existing quotient transport then applies to the literal
L = KcT and L/O₂(L), giving the source contradiction.

Only this orthogonal branch is discharged here. Chief-model recognition,
the natural-plus-dual exclusion, and the paired-natural parabolic remain
separate source obligations; no parabolic or movement premise is retained
in this consumer.

Source: Aschbacher--Smith, original15.2.27(2), printed p.1119 (PDF p.1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
open Representation.SmallDisplacementParabolics
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual eight-point module gives the contradiction on the original partner quotient. -/
theorem source_chosen_false_of_orthogonal_partner_core_quotient
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
      (∃ e : (L ⧸ pCore 2 L) ≃* Equiv.Perm (Fin 8),
        Nonempty (ρ.Equiv ((BinaryPermutation.naturalRepresentation (Fin 8)).comp e.toMonoidHom))) →
      (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w) →
      (∀ g ∈ (S : Subgroup (L ⧸ pCore 2 L)), ρ g w = w) → False := by
  dsimp only
  intro ρ w hw hmodel hfix hSylow
  obtain ⟨e, ⟨f⟩⟩ := hmodel
  obtain ⟨d⟩ := OrthogonalEight.exists_of_equiv ρ e f _ w hw hSylow
  exact source_chosen_false_of_partner_core_quotient h hg hMc hplane ρ w hfix d

end CFSG.Quasithin.Chapter15.Section02
