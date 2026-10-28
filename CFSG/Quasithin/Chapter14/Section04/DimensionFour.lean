module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.Configuration
public import Theory.GroupTheory.ElementarySixteenExtensionTransfer
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-!
# The dimension-four recognition branch: final local reduction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Theorem
14.4.3 and Lemmas 14.4.4–5, printed pp.1007–1008; recognition uses I.4.5,
printed p.417. The exported implication constructs the source I.4 local
configuration, then applies an explicitly supplied universal recognition
theorem. Its codomain is the actual split-octonion automorphism group over F₃.

The source setup does not yet discharge the local hypotheses of this
implication: in particular the nonsplit block and E₁₆ exclusions remain
separate obligations. No source-numbered theorem is asserted here.
-/

open Subgroup

universe u

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour

/-- Final recognition after the local hypotheses have been established.
The universal recognition implication is the exact separate I.4.5 obligation. -/
public theorem isomorphic_of_quaternion_local_data
    {G : Type u} [Group G] [Finite G]
    (recognize : ∀ (X : Type u) [Group X] [Finite X],
      Nonempty (G2ThreeConfiguration X) → Nonempty (X ≃* Atlas.G2.Model (ZMod 3)))
    (H M : Subgroup G) (Q : Subgroup H) [Q.Normal]
    (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set H) ≤ Q) (hindex : Q.index = 18)
    (s : H) (hgen : pResidual 2 H ⊔ zpowers s = ⊤)
    (hinv : ∀ k : pResidual 2 H,
      QuotientGroup.mk' Q (s * k * s⁻¹) = (QuotientGroup.mk' Q k)⁻¹)
    (hH : H = centralizer
      ((((center Q).map Q.subtype).map H.subtype : Subgroup G) : Set G))
    (V : Subgroup M) [V.Normal]
    (hVcore : V = pCore 2 M) (hVcentral : centralizer (V : Set M) ≤ V)
    (hVmodel : Nonempty (V ≃* Multiplicative (Fin 3 → ZMod 2)))
    (hMquotient : Nonempty ((M ⧸ V) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) :=
  recognize G (configuration_of_quaternion_inverting_quotient H M Q d
    hcentral hindex s hgen hinv hH V hVcore hVcentral hVmodel hMquotient)

end CFSG.Quasithin.Chapter14.Section04.DimensionFour
