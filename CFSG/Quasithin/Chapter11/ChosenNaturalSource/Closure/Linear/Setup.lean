module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure

/-!
# The original three conjugates in the linear closure argument

The G.2 seed is the original chosen V, its actor is L, and its overgroup
is N_G(V₁). Thus its U is exactly the closure W of the Chapter 11 geometry.
All conjugates use the right-conjugation convention of G.2. The two-residual
in G.2 is deliberately not identified with Chapter 11's solvable residual.

Once the genuine marked G.2 hypothesis has been constructed, its structural
theorem places the three-conjugate core in O₂(LT), hence in G₁. The equality
I=LU proves M₁-invariance without requiring the chosen frame to be fixed.
The construction of that marked hypothesis remains a separate source step.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782, and G.2.5.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- G.2 with the actual SL₃ seed and the full point normalizer. -/
def setup : ChapterG.Section02.Setup G where
  V := V
  V₁ := E.V₁
  L := L
  T := T
  H := E.G₁

def threeGroup (x y : G) : Subgroup G := ChapterG.Section02.LinearThree.I (setup E) x y
def threeCore (x y : G) : Subgroup G := ChapterG.Section02.LinearThree.S (setup E) x y
def triple (x y : G) : Subgroup G := ChapterG.Section02.LinearThree.S₂ (setup E) x y
def oppositePair (x y : G) : Subgroup G :=
  ChapterG.Section02.Setup.conjugate E.W x ⊓ ChapterG.Section02.Setup.conjugate E.W y

theorem setup_closure : (setup E).U = E.W := rfl
theorem setup_point_normalizer : (setup E).G₁ = E.G₁ := rfl

/-- The final quotient map is literally the Chapter 11 quotient map. -/
theorem setup_tilde (A : Subgroup G) : (setup E).tilde A = E.tilde A := rfl

theorem triple_le_closure (x y : G) : triple E x y ≤ E.W :=
  inf_le_left.trans inf_le_left

theorem triple_le_oppositePair (x y : G) : triple E x y ≤ oppositePair E x y :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem pointResidual_le_G₁ : E.L₁ ≤ E.G₁ :=
  (residualIn_le _).trans inf_le_right

theorem pointResidual_le_K : E.L₁ ≤ E.K := le_conjugateSpanBy _ _

/-- The point normalizer preserves the literal quotient centralizer Y. -/
theorem G₁_normalizes_Y : E.G₁ ≤ normalizer (E.Y : Set G) :=
  (le_inf (normalizer_le_normalizer_centralizer E.V₁)
    (E.G₁_normalizes_K.trans
      (normalizer_normalizes_coreQuotientCentralizer E.K))).trans
    inf_normalizer_le_normalizer_inf

variable {E} {x y : G}
  (d : ChapterG.Section02.LinearThree.Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

/-- Apply structural G.2.5 with the original three conjugates. -/
theorem threeGroup_eq_join (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    threeGroup E x y = L ⊔ E.W :=
  d.I_eq_LU hUT hf

theorem threeCore_le_LT_core (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    threeCore E x y ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  change ChapterG.Section02.LinearThree.S (setup E) x y ≤ (setup E).LT.pCoreIn 2
  rw [d.S_eq_star_kernel hUT hf]
  exact inf_le_right

/-- The original chosen module makes O₂(LT) centralize the marked point. -/
theorem threeCore_le_G₁ (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    threeCore E x y ≤ E.G₁ :=
  (threeCore_le_LT_core d hUT hf).trans
    ((D.core_centralizes.trans (centralizer_le E.V₁_le)).trans
      (centralizer_le_normalizer _))

/-- M₁ preserves I=LU, and therefore preserves its characteristic two-core. -/
theorem M₁_normalizes_threeCore (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    E.M₁ ≤ normalizer (threeCore E x y : Set G) := by
  have hI : E.M₁ ≤ normalizer (threeGroup E x y : Set G) := by
    rw [threeGroup_eq_join d hUT hf]
    exact (le_inf inf_le_left
      (inf_le_right.trans (le_normalizer_conjugateSpanBy V E.G₁))).trans
      (normalizer_inf_normalizer_le_normalizer_sup L E.W)
  exact hI.trans (normalizer_le_normalizer_characteristic_image
    (threeGroup E x y) (pCore 2 (threeGroup E x y)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
