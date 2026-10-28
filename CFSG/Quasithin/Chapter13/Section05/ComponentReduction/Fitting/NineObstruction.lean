module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Reduction
public import Theory.Representation.NormalNineCentralInvolution

/-!
# The binary obstruction in the elementary-nine branch of 13.5.20

The normal subgroup P is supplied by `normal_nine_of_fitting_failure` in
the actual H/O₂(H). The earlier actor facts are transported by `Actors`:
Y* is two-perfect with cubic two-core quotient, and it centralizes V*.
The normal-nine representation theorem forces fixed codimension at least
four, contradicting the source action's codimension two.

The faithful binary action and its codimension remain explicit here.
Their construction from F.9.5, and the discharge of the earlier local
inputs, belong to the Fitting-centralization assembly. This theorem adds
no split-group, model, character-multiplicity or obstruction premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.20, printed p.923 (PDF p.940).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
open Section08.Source
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]

/-- Apply the normal-nine obstruction to the literal P, Y* and V* of
13.5.20. The independent source-action construction supplies ρ and hcodim. -/
theorem false_of_fitting_failure_of_binary_action
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H)
    (hindex : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (Y : Subgroup G) (hYH : Y ≤ D.H) (hY : IsPPerfect 2 Y)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hYV : Y ≤ normalizer (D.V : Set G))
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hpairs : ∀ x : Hstar D.H,
      ¬ IsPGroup 2 (starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) →
      Nat.card (starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) = 6)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Hstar D.H) W) (hρ : Function.Injective ρ)
    (hcodim : fixedCodim ρ (starImage D.H D.V) = 2)
    (hfit : ¬ starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H))) : False := by
  obtain ⟨P, hPn, _, hPe, hPc, hPm, hPY⟩ := normal_nine_of_fitting_failure
    K D h hSQTK hindex hu Y hYH hY hYquot hYV himage hcore hpairs hfit
  let : P.Normal := hPn
  let : IsElementaryAbelian 3 P := hPe
  have hbound := Representation.NormalNineCentralInvolution.four_le_fixedCodim
    ρ hρ P (starImage D.H Y) (starImage D.H D.V) hPc
    (LocalGeometry.star_V_card_two h hindex hu)
    (star_twoPerfect D.H Y hYH hY) (star_cubic_quotient D.H Y hYH hYquot)
    (star_centralizes_V D h hindex hu Y hYV) hPY hPm
  omega

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
