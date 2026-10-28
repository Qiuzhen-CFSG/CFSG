module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentRows
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalPointDeletedModel
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedSection

/-!
# Natural four-space coordinates for the actual center constituent

The original returning center has elementary image of order four in the
unchanged hatted quotient, while it fixes an index-four subgroup of every
chosen constituent in Z(U). The deleted-eight central-quotient row descends
through that same hatted projection and contradicts the orthogonal fixed-
codimension bound. The genuine seven module rows therefore give full natural
four-space coordinates on the original constituent.

This replaces only the internal use of 12.6.34 at printed p.860. It does not
construct the initial natural-four marking required to enter Section12.9.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V I : Subgroup G}

/-- The deleted-eight alternative is impossible for the actual original
chosen constituent in the full center. -/
theorem nonabelian_caseFive_chosen_not_deleted
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (c : ChosenModule T C.K1 I) (hiZ : I ≤ F.ZU) :
    letI := c.actionCentralizer_normal
    ¬ Nonempty (ActionEquiv c.faithfulCentralAction (alternatingNatural 8)) := by
  let := c.actionCentralizer_normal
  let := c.elementary
  rintro ⟨a⟩
  obtain ⟨hHI, ρ, e, E, hE, he⟩ := nonabelian_caseFive_deleted_point_model
    modules h preferred earlier F hne g hgP hgH B h5 C c hiZ a
  let D := conjugate F.ZU g
  have hg2 := F.P_le_G₂ (by decide : 2 ≤ 4) L h.chosen.normalizes hgP
  have hDH : D ≤ F.H := (F.conjugate_ZU_le_X g).trans (F.X_le_H g hg2)
  obtain ⟨_, _, _, hfour, hcard, _⟩ :=
    nonabelian_caseFive_center_four_geometry h (Or.inl rfl) earlier F hne g hgP hgH B h5
  let := hfour
  let q := e.toMonoidHom.comp (QuotientGroup.mk' F.terminalHatAction.ker)
  have hmap : (D.subgroupOf F.H).map q = (F.terminalDot D).map e.toMonoidHom :=
    (map_map _ _ _).symm
  have hcard' : Nat.card ((D.subgroupOf F.H).map q) = 4 := by
    rw [hmap, card_map_of_injective e.injective]
    exact hcard
  have hsq : ∀ x ∈ (D.subgroupOf F.H).map q, x ^ 2 = 1 := by
    rw [hmap]
    rintro x ⟨y, hy, rfl⟩
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot D)) (⟨y, hy⟩ : F.terminalDot D)
    have hh' : y ^ 2 = 1 := congrArg Subtype.val hh
    simpa only [map_pow, map_one] using congrArg e.toMonoidHom hh'
  exact deleted_eight_section_false_of_index_four hHI hDH ρ c.toCentralQuotient
    c.toCentralQuotient_surjective he q E hE hcard' hsq
    (nonabelian_caseFive_chosen_centralizer_index h earlier F hne g hgP hgH B h5 C c hiZ)

/-- The original selected center constituent is a full natural four-space,
using the actual module rows and returning-center action, with no independent
`NaturalReduction 4` hypothesis. -/
theorem nonabelian_caseFive_chosen_natural_of_original_rows
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (c : ChosenModule T C.K1 I) (hiZ : I ≤ F.ZU) :
    NaturalModule c 4 := by
  let := c.actionCentralizer_normal
  exact (nonabelian_caseFive_chosen_natural_or_deleted
    modules h preferred earlier F hne g hgP hgH B h5 C c).resolve_right
      (nonabelian_caseFive_chosen_not_deleted modules h preferred earlier F hne g hgP hgH B h5 C c hiZ)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
