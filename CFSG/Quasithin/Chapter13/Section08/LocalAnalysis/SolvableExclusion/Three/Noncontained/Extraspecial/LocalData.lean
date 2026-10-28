module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction

/-!
# Local residual data for the extraspecial branch

The simple and covered local models generate L₁ by two-perfect residuals
with cubic two-core quotients. In the covered case the two marks L₁,+
and L₀ must be retained separately: the full L₁ quotient has order nine.
`CubicGeneration` records only these earlier local facts. Its construction
from the standing natural action is a separate obligation.

`ActionAlternative` is the intermediate output of the irreducibility
argument on the actual normal P*. It supplies either a moving cubic
residual or an original cubic actor outside P* with inner action on P*.
Neither alternative assumes an elementary rank-three subgroup.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2, pp.877–878;
the noncontained branch of 13.8.13, printed p.951 (PDF p.968).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial
variable {G : Type*} [Group G]

/-- Earlier local structure, independent of the selected odd normal subgroup.
Every generator is normal in L₁T; no ambient normality is required. -/
structure CubicGeneration (L₁ T : Subgroup G) where
  generators : Set (Subgroup G)
  generated : sSup generators = L₁
  normalizes : ∀ X ∈ generators, L₁ ⊔ T ≤ normalizer (X : Set G)
  perfect : ∀ X ∈ generators, IsPPerfect 2 X
  cubic : ∀ X ∈ generators, Nat.card (X ⧸ pCore 2 X) = 3
  elementary : IsElementaryAbelian 3 (L₁ ⧸ pCore 2 L₁)

/-- The original subgroup maps to H/O₂(H) by its inclusion in H. -/
noncomputable def starMap (H X : Subgroup G) (hXH : X ≤ H) : X →* Source.Hstar H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hXH)

/-- Conjugation on the actual selected star image. -/
noncomputable def starAction (H P X : Subgroup G)
    [(Source.starImage H P).Normal] (hXH : X ≤ H) :
    X →* MulAut (Source.starImage H P) :=
  (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H P)).comp
    (starMap H X hXH)

/-- The literal center-quotient action, equal to the Frattini action in the
extraspecial case. -/
noncomputable def centerAction (H P X : Subgroup G)
    [(Source.starImage H P).Normal] (hXH : X ≤ H) :
    X →* MulAut (Source.starImage H P ⧸ center (Source.starImage H P)) :=
  (quotientAut (center (Source.starImage H P))).comp (starAction H P X hXH)

/-- A branch-specific action conclusion to be constructed from the local
residual data and noncontainment, before the elementary subgroup is built. -/
def ActionAlternative {H L₁ T M Vα : Subgroup G}
    (r : ReducedOdd 3 H L₁ T M Vα) : Prop :=
  let _ := r.Pstar_normal
  (∃ (X : Subgroup G) (hXL : X ≤ L₁), IsPPerfect 2 X ∧
    Nat.card (X ⧸ pCore 2 X) = 3 ∧
    (pCore 2 X).map (starAction H r.P X
      (hXL.trans (le_sup_left.trans (r.generated ▸ le_sup_right)))) ≠ ⊥) ∨
  (∃ x ∈ Source.starImage H L₁, orderOf x = 3 ∧
    x ∉ Source.starImage H r.P ∧
    quotientAut (center (Source.starImage H r.P)) (MulAut.conjNormal x) = 1)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial
end
