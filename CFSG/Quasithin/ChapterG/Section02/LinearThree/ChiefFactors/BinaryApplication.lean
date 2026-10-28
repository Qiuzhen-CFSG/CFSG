module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.BinaryUpper

/-!
# Counting and series collapse on the original Section 12.8 flag

These substitutions retain the literal U, marked conjugators, and core of
their generated subgroup. The source natural/dual markings and the earlier
homogeneous cubic coordinates remain explicit. In particular, the hypotheses
of 12.8.5(1) must be used to construct the latter; normality of L₁ alone is
not substituted for that module theorem.

The collapse proves the two equalities actually used in the proof on p.852.
It does not assert that the whole dual three-dimensional layer is a sum of
two-dimensional modules after restriction to the cubic.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(8) and 12.8.8(4–5), printed pp.335,851–852.
-/

@[expose] public section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
open CFSG.Quasithin.Chapter12.Section08

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  (flag : InvariantFlag T V 3) (L : Subgroup G) (g h : G)
  (d : Hypothesis (binarySetup flag L) (ZMod 2) 1 g h)
  [((S₂ (binarySetup flag L) g h).subgroupOf (S₃ (binarySetup flag L) g h)).Normal]
  [((S₃ (binarySetup flag L) g h).subgroupOf (S (binarySetup flag L) g h)).Normal]

/-- The binary specialization of the proved order formula, on the original U. -/
theorem binary_flag_order (hUT : flag.U ≤ (T : Subgroup G))
    (hf : (frattini flag.U).map flag.U.subtype ≤ flag.Vi 1)
    (hLI : L ≤ I (binarySetup flag L) g h)
    (hcore : S (binarySetup flag L) g h =
      I (binarySetup flag L) g h ⊓ (binarySetup flag L).LT.pCoreIn 2)
    (radical : (binarySetup flag L).star flag.U ≃* Multiplicative (Fin 2 → ZMod 2))
    {r s : ℕ} (c : MarkedLayers d hLI r s) :
    Nat.card flag.U = 2 ^ (2 * s + r + 5) *
      V.relIndex ((flag.U ⊓ Setup.conjugate flag.U g) ⊓ Setup.conjugate flag.U h) := by
  have horder := order_formula d hUT hf hcore radical c
  change Nat.card flag.U = 2 ^ (1 * (2 * s + r + 5)) *
    V.relIndex ((flag.U ⊓ Setup.conjugate flag.U g) ⊓ Setup.conjugate flag.U h) at horder
  simpa only [one_mul] using horder

/-- The actual triple intersection and pair-product collapse of 12.8.8(5),
conditional only on the preceding marked layers and homogeneous cubic action. -/
theorem binary_flag_series_collapse (hUT : flag.U ≤ (T : Subgroup G))
    (hf : (frattini flag.U).map flag.U.subtype ≤ flag.Vi 1)
    (hLI : L ≤ I (binarySetup flag L) g h)
    {r s : ℕ} (c : MarkedLayers d hLI r s)
    (x : (binarySetup flag L).L₁) {t : ℕ} (b : CubicSpanCoordinates d x t) :
    let J := (flag.U ⊔ Setup.conjugate flag.U g) ⊔ Setup.conjugate flag.U h
    let W₀ := flag.U ⊓ J.pCoreIn 2
    ((flag.U ⊓ Setup.conjugate flag.U g) ⊓ Setup.conjugate flag.U h = V) ∧ r = 0 ∧
      (J.pCoreIn 2 : Set G) =
        ((W₀ ⊓ Setup.conjugate W₀ g : Subgroup G) : Set G) *
        ((W₀ ⊓ Setup.conjugate W₀ h : Subgroup G) : Set G) *
        ((Setup.conjugate W₀ g ⊓ Setup.conjugate W₀ h : Subgroup G) : Set G) := by
  have he := binary_intersection_eq_V d hUT hf hLI x b
  obtain ⟨hr, hs⟩ := binary_upper_collapse d hUT hf hLI c x b
  refine ⟨he, hr, ?_⟩
  have hp := d.S₃_product hUT hf hLI
  rw [hs] at hp
  exact hp

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
