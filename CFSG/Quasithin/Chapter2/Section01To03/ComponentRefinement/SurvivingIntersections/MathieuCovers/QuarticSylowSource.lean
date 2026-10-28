module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.SylowCentralizer
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.M22Reduction

/-!
# Excluding the quartic M₂₂ cover in the original source setup

The supplied inner action of the original z fixes the actual component Sylow.
Its implementer therefore centralizes that Sylow. For a quartic M₂₂ cover the
Sylow centralizer lies in the center, making the action trivial, contrary to
L not being contained in M and C_G(z) ≤ M.

The equality Z(L) = O₂(L) and cyclicity are derived for the supplied component.
The central quotient used below is the original quotient reindexed by that
equality: `mathieuTwentyTwo_centerQuotient_projection` identifies its projection
pointwise with `d.quotientIso` after the literal quotient by O₂(L).
The final application retains Γ₀, the original ambient Sylow and the earlier
structural 1.1.5 and local-C inputs. No ambient normalization premise is needed.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412, and 2.3.9(7),
printed pp.525–526. The argument uses the quartic radical's actual center;
it makes no corresponding claim about the binary cover.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original nontrivial inner action excludes a quartic M₂₂ component. -/
theorem LocalSetup.mathieuTwentyTwo_quartic_false
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 4) : False := by
  let := h.finite
  let := h.quasisimple
  let : IsCyclic (center L) := by
    rw [h.mathieuTwentyTwo_center_eq d.quotientIso]
    exact h.mathieuTwentyTwo_core_isCyclic d.quotientIso
  let eZ := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  have hZ : Nat.card (center L) = 4 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  obtain ⟨P, _hP, hfix⟩ := h.exists_fixed_component_sylow d.action d.conjugation
  obtain ⟨t, ht⟩ := d.inner
  have htc : t ∈ centralizer (P : Set L) := by
    intro r hr
    have he := hfix r hr
    rw [← ht] at he
    change t * r * t⁻¹ = r at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have htz : t ∈ center L :=
    M22Local.Quartic.centralizer_sylow_le_center eZ hZ P htc
  apply h.action_ne_one d.action d.conjugation
  rw [← ht]
  apply MulEquiv.ext
  intro x
  change t * x * t⁻¹ = x
  rw [← mem_center_iff.mp htz x, mul_inv_cancel_right]

/-- The quartic exclusion with the actual Γ₀ context and its earlier source inputs. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_quartic_false [Finite G]
    {C : GroupClass} (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE C G) (source115 : Structural115Input G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 4) : False :=
  (c.localSetup hG source115 sourceC).mathieuTwentyTwo_quartic_false d hc

end CFSG.Quasithin.Chapter2.ComponentRefinement
