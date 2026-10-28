module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SourceFields

/-!
# Nonvanishing of the actual complement commutator

If the complements W₁ and W₂ commute, W₂ centralizes all of V: the other
summand P ∩ V already centralizes P. The source identity C_P(V) = P ∩ V
then puts W₂ inside the proper hyperplane P ∩ R₁, contradicting its
complement property. This uses the literal flag and radical, without a
pairing or a nonzero-commutator premise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the
paragraph following 11.3.8, printed p.775. The preceding fixed-plane
identity and hyperplane geometry remain with their marked-section producer.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan

section Complements
variable {G : Type*} [Group G] {V P B W₁ W₂ : Subgroup G}

/-- The source fixed-plane identity forces the two complements to fail to commute. -/
theorem complement_commutator_ne_bot [IsMulCommutative P]
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (hVB : P ⊓ V ≤ B) (hB : B < P)
    (h₁ : P ⊓ V ⊔ W₁ = V) (h₂ : B ⊔ W₂ = P) : ⁅W₁, W₂⁆ ≠ ⊥ := by
  intro hc
  have hwP : W₂ ≤ P := h₂ ▸ le_sup_right
  have hwC : W₂ ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← h₁]
    exact sup_le
      ((inf_le_left : P ⊓ V ≤ P).trans ((Subgroup.le_centralizer P).trans
        (centralizer_le hwP)))
      (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hwB : W₂ ≤ B := (hfixed ▸ le_inf hwP hwC).trans hVB
  exact hB.not_ge (h₂ ▸ sup_le le_rfl hwB)

end Complements

open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {P Y X W₁ W₂ : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]

/-- On the original chosen seed, the actual source complements have a nonzero,
central, Cartan-invariant commutator inside the literal V₂. This discharges
nonvanishing in `false_of_cartan_commutator` from the earlier section geometry. -/
theorem source_complement_commutator
    (hPV : P ⊓ V = f.Vi 1)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (hproper : P ⊓ f.Ri 0 < P)
    (hP : P = (f.Li 1).pCoreIn 2) (hVY : V ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G))
    (hs₁ : f.Vi 1 ⊔ W₁ = V) (hs₂ : (P ⊓ f.Ri 0) ⊔ W₂ = P)
    (hn₁ : X ≤ normalizer (W₁ : Set G))
    (hn₂ : X ≤ normalizer (W₂ : Set G)) :
    ⁅W₁, W₂⁆ ≠ ⊥ ∧ ⁅W₁, W₂⁆ ≤ f.Vi 1 ∧
      ⁅W₁, W₂⁆ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) ∧
      X ≤ normalizer ((⁅W₁, W₂⁆ : Subgroup G) : Set G) := by
  have h₁ : W₁ ≤ V := hs₁ ▸ le_sup_right
  have h₂ : W₂ ≤ P := hs₂ ▸ le_sup_right
  have hc := source_commutator_central D S f P Y hP hVY hYP h₁ h₂
  refine ⟨complement_commutator_ne_bot hfixed
    (inf_le_inf_left P (f.seed_le_Ri S 0)) hproper (hPV ▸ hs₁) hs₂,
    ?_, hc.2, normalizes_commutator hn₁ hn₂⟩
  rw [← hPV, inf_comm]
  exact hc.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
