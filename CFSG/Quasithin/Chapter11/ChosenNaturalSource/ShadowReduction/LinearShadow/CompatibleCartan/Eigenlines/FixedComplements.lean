module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Nonzero
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
/-!
# Fixed complements in the source Cartan argument

If an actor normalizes a complement and acts trivially modulo the other
summand, its commutator with the complement lies in their zero intersection.
In the actual source flag this proves that X₂ = X ∩ L₂ centralizes W₁
from the natural-action bound [V,L₂] ≤ V₂. The actual kernel of the
normalizer action on L₁/O₂(L₁) similarly fixes W₂, using its disjointness
from P ∩ R₁; no ambient normality of L₁ is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the proof
of 11.3.9, printed p.775. The natural-action bound belongs to the separate
marked-section geometry and remains explicit here.
-/

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
variable {G : Type*} [Group G] {V U W X : Subgroup G}
/-- Trivial action on a quotient is trivial on every invariant complement. -/
theorem centralizes_invariant_complement (hWU : Disjoint U W) (hWV : W ≤ V)
    (hXW : X ≤ normalizer (W : Set G)) (hVX : ⁅V, X⁆ ≤ U) :
    X ≤ centralizer (W : Set G) := by
  apply le_centralizer_iff.mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  exact (le_inf ((commutator_mono hWV le_rfl).trans hVX)
    (le_normalizer_iff_commutator_le_left.mp hXW)).trans hWU.le_bot

section Second
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
/-- The actual X ∩ L₂ fixes the source complement W₁ pointwise. -/
theorem source_second_cartan_centralizes (hdis : Disjoint (f.Vi 1) W) (hWV : W ≤ V)
    (hn : X ≤ normalizer (W : Set G)) (hmove : ⁅V, f.Li 1⁆ ≤ f.Vi 1) :
    X ⊓ f.Li 1 ≤ centralizer (W : Set G) :=
  centralizes_invariant_complement hdis hWV (inf_le_left.trans hn)
    ((commutator_mono le_rfl inf_le_right).trans hmove)
end Second

section First
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
variable (A : Subgroup G)
/-- The literal normalizer-action kernel centralizes A modulo its intrinsic two-core. -/
theorem commutator_coreQuotientCentralizer : ⁅A, coreQuotientCentralizer A⁆ ≤ A.pCoreIn 2 := by
  apply commutator_le.mpr
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hq : QuotientGroup.mk' (pCore 2 A) (A.normalizerMonoidHom y ⟨a, ha⟩) =
      QuotientGroup.mk' (pCore 2 A) ⟨a, ha⟩ := by
    have h := congrArg (fun e : MulAut (A ⧸ pCore 2 A) => e (QuotientGroup.mk' (pCore 2 A) ⟨a, ha⟩)) hy
    simpa only [coreQuotientAction_apply_mk, MulAut.one_apply] using h
  have hm : A.normalizerMonoidHom y ⟨a, ha⟩ * (⟨a, ha⟩ : A)⁻¹ ∈ pCore 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 A) _ = 1
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  have hcomm : ⁅(y : G), a⁆ ∈ A.pCoreIn 2 := ⟨_, hm, rfl⟩
  rw [← commutatorElement_inv]
  exact inv_mem hcomm
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable [Finite G] {T : Sylow 2 G} {L P : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
/-- X₁ = C_X(L₁/O₂(L₁)) fixes the actual complement W₂. -/
theorem source_first_cartan_centralizes (hWP : W ≤ P) (hWA : W ≤ f.Li 0)
    (hdis : Disjoint (P ⊓ f.Ri 0) W) (hn : X ≤ normalizer (W : Set G)) :
    X ⊓ coreQuotientCentralizer (f.Li 0) ≤ centralizer (W : Set G) := by
  have hcR : (f.Li 0).pCoreIn 2 ≤ f.Ri 0 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans le_sup_left)
      ((sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0)).trans
        (normalizer_le_normalizer_characteristic_image (f.Li 0) (pCore 2 (f.Li 0))))
  have hm : ⁅W, X ⊓ coreQuotientCentralizer (f.Li 0)⁆ ≤ f.Ri 0 :=
    (commutator_mono hWA inf_le_right).trans ((commutator_coreQuotientCentralizer (f.Li 0)).trans hcR)
  have hw : ⁅W, X ⊓ coreQuotientCentralizer (f.Li 0)⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hn)
  apply le_centralizer_iff.mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact bot_unique ((le_inf (le_inf (hw.trans hWP) hm) hw).trans hdis.le_bot)


end First

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
