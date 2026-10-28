module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Generated
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineObstruction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Action

/-!
# Compatible actions on the two literal endpoint sections

This interface records representations of the actual endpoint star group on
Uγ/A₁ and Vγ/Uγ. Each representation agrees on representatives with ambient
conjugation by the same endpoint element. It contains no nonidentity actor,
rank bound, model identification, permutation quotient or line conclusion.

The two consumers construct the marked source quotient and extract a common
actor from the center and axis obtained by the local geometry. Their results
are assembled in the owner of the line-containment deduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34(1), printed p.968.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
open CriticalGeometry CriticalGeometry.SectionActions
variable {G : Type*} [Group G] {L T H V : Subgroup G}

/-- Compatibility with conjugation on both source sections. The actor is
Hγ/O₂(Hγ), where Hγ is the actual endpoint vertex stabilizer. -/
structure EndpointActions (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (c.Ugamma V₃)] [IsElementaryAbelian 2 c.Vgamma]
    (hz : H ≤ normalizer (Z : Set G)) where
  onU : Representation (ZMod 2) (Source.Hstar (vertexGroup L T H c.gamma))
    (Additive (c.Ugamma V₃ ⧸ (c.Aone Z).subgroupOf (c.Ugamma V₃)))
  onV : Representation (ZMod 2) (Source.Hstar (vertexGroup L T H c.gamma))
    (Additive (c.Vgamma ⧸ (c.Ugamma V₃).subgroupOf c.Vgamma))
  onU_mk : ∀ j : vertexGroup L T H c.gamma,
    onU (QuotientGroup.mk' (pCore 2 (vertexGroup L T H c.gamma)) j) =
      (binaryLinear (quotientAction (vertexGroup L T H c.gamma) (c.Ugamma V₃)
        (c.Aone Z) (c.normalizes_Ugamma V₃)
        (SectionActions.CriticalPair.normalizes_Aone c Z hz) j)).toLinearMap
  onV_mk : ∀ j : vertexGroup L T H c.gamma,
    onV (QuotientGroup.mk' (pCore 2 (vertexGroup L T H c.gamma)) j) =
      (binaryLinear (quotientAction (vertexGroup L T H c.gamma) c.Vgamma
        (c.Ugamma V₃) (c.normalizes_Ugamma V) (c.normalizes_Ugamma V₃) j)).toLinearMap

/-- The F.9 identity Q_H=C_H(U_H/V₁) proves faithfulness of every
compatible representation on that literal quotient. -/
theorem faithful_of_conjugation_kernel (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G)) (hz : H ≤ normalizer (Z : Set G))
    (hk : Source.QH H = commutatorPreimage H U Z)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U)))
    (hact : ∀ h : H, ρ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (quotientAction H U Z hn hz h)).toLinearMap) :
    Function.Injective ρ := by
  obtain ⟨a, ha⟩ := SolvableExclusion.Five.exists_faithful_starAction H U Z hn hz hk
  have he (x : Source.Hstar H) : ρ x = (binaryLinear (a.action x)).toLinearMap := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    rw [hact]
    have hh : quotientAction H U Z hn hz h = a.action (QuotientGroup.mk' (pCore 2 H) h) := by
      ext w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
      rw [quotientAction_apply, a.conjugation]
    rw [hh]
  intro x y hxy
  apply ha
  apply MulEquiv.ext
  intro w
  have h := LinearMap.congr_fun hxy (Additive.ofMul w)
  rw [he, he] at h
  exact h

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
