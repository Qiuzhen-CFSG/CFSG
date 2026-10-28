module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions

/-!+# The actual omega actions in the two-core quotient

The image of a C-component under the quotient by the two-core is again a
C-component. Applying A.3.6 there, and then its proved action consequences,
gives the common Fitting kernel and irreducibility for conjugation on every
Ω₁(Oₚ(L̄))/Φ(Ω₁(Oₚ(L̄))). The action data also retain the quaternion subgroup
in each Sylow two-action image. They concern the actual image L̄ of the
specified component, with no identification of Ω₁(Oₚ(L̄)) with all of Oₚ(L̄).

This strengthens the earlier-result deduction without assuming the extra
center–Frattini equality printed in 1.2.1(4d). That separate source obligation
is unchanged. The only earlier-source input is the full universal A.3.6
classification; its instantiation remains with the Chapter 1 assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.6 and its
proof, printed pp.43–45, and Proposition 1.2.1, printed p.504.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open CenterFrattiniSource
universe u

/-- The complete earlier classification and its actual omega-action consequences
for the image of the specified component in the two-core quotient. -/
theorem proposition_1_2_1_four_earlier_with_actions
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X,
      K.IsCComponent → A36Conclusion K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {K : Subgroup G} (hK : K.IsCComponent) :
    A36Conclusion (K.map (QuotientGroup.mk' (pCore 2 G))) ∧
      (¬ IsQuasisimple (K.map (QuotientGroup.mk' (pCore 2 G))) →
        OmegaActionData (K.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  exact strengthened_omega_actions hQ (pCore_quotient_pCore_eq_bot 2)
    (hK.map_quotient _) (proposition_1_2_1_four_earlier_conclusion hA36 hQ hK)

end CFSG.Quasithin.Chapter1.Section02
