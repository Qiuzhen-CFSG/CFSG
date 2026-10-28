module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Source
public import Theory.AlgebraicGroup.Cartan.Kernels

/-!
# Central elements of the six-coroot tori

In either higher E6 realization, a central value that lies in the torus on
its six simple coroots equals the explicit cubic central word. Conjugation
of each positive simple root at parameter one forces its root character to
be trivial: a distinguished matrix entry recovers that parameter. The
existing E6 multiplicative Cartan-kernel theorem then determines all six
coordinates as `(u,u²,1,1,u,u²)`, with `u³ = 1`.

This argument works over every field, including characteristic three. The
torus-containment premise is explicit: placement of arbitrary central
six-node values in this torus is a separate representation theorem. The
`CenterAction` consumer uses the result to calculate the cube and, given
preservation of relations by the diagram, its action.

Sources: GLS3 §§1.12.5–6 and 2.5–2.6, especially Table 1.12.6 and the
subsystem construction in 2.6.2 (`refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`). These calculations support the higher
exceptional embeddings used in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
open scoped BigOperators
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction
attribute [local instance] Classical.decEq

variable (F : Type*) [Field F]
section Generic
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The six simple-coroot parameters, extended by one to the ambient base. -/
def sixCorootParameter (j : Fin 6 → b.support) (t : Fin 6 → Fˣ) : b.support → Fˣ :=
  ∏ i, integralChevalleySimpleCorootParameter (j i) (t i)

/-- The actual ambient diagonal with the six specified coroot parameters. -/
def sixCorootMatrix (j : Fin 6 → b.support) (t : Fin 6 → Fˣ) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ :=
  integralChevalleyTorusElement (P := P) (sixCorootParameter F j t)

/-- The six-coroot diagonal acts on a root by the literal Cartan character. -/
theorem sixCorootParameter_scale (j : Fin 6 → b.support) (t : Fin 6 → Fˣ) (r : ι) :
    integralChevalleyRootScale (P := P) (sixCorootParameter F j t) r =
      ∏ i, t i ^ P.pairingIn ℤ r (j i) := by
  let h : (b.support → Fˣ) →* Fˣ :=
    ⟨⟨fun u => integralChevalleyRootScale (P := P) u r,
      integralChevalleyRootScale_one r⟩,
      fun u v => integralChevalleyRootScale_mul u v r⟩
  change h (∏ i, integralChevalleySimpleCorootParameter (j i) (t i)) = _
  rw [map_prod]
  simp only [h, MonoidHom.coe_mk, OneHom.coe_mk,
    integralChevalleyRootScale_simpleCorootParameter]

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι] in
private theorem sixCorootParameter_central (j : Fin 6 → b.support) (u : Fˣ) :
    sixCorootParameter F j ![u,u^2,1,1,u,u^2] = centralParameter F j u := by
  have h (i : b.support) : integralChevalleySimpleCorootParameter i (1 : Fˣ) = 1 := by
    funext k
    simp [integralChevalleySimpleCorootParameter]
  simp [sixCorootParameter, Fin.prod_univ_succ, h, centralParameter, mul_assoc]

private theorem scale_eq_one_of_commute (u : b.support → Fˣ) (i : b.support)
    (h : Commute (integralChevalleyTorusElement (P := P) u)
      (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i (1 : F))) :
    integralChevalleyRootScale (P := P) u i = 1 := by
  have hc := integralChevalleyRootCurve_torus_conjugation (P := P) u (i : ι) (1 : F)
  rw [mul_one] at hc
  have he : rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i
      (integralChevalleyRootScale (P := P) u i : F) =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i (1 : F) := by
    rw [← hc, mul_assoc, ← h.eq, inv_mul_cancel_left]
  apply Units.ext
  exact elementaryRoot_simple_injective i (Subtype.ext he)

private theorem torus_eq_centralMatrix (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (t : Fin 6 → Fˣ)
    (hc : ∀ i, Commute (sixCorootMatrix F j t)
      (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) (j i) (1 : F))) :
    ∃ u : Fˣ, u ^ 3 = 1 ∧ sixCorootMatrix F j t = centralMatrix F j u := by
  have he (i k : Fin 6) : typeE6CartanMatrix i k =
      Theory.AlgebraicGroup.dynkinCartanEntry ⟨.E6, 6⟩ k i := by
    fin_cases i <;> fin_cases k <;> decide
  have hr (i : Fin 6) :
      (∏ k, t k ^ Theory.AlgebraicGroup.dynkinCartanEntry ⟨.E6, 6⟩ k i) = 1 := by
    have hs := scale_eq_one_of_commute F (sixCorootParameter F j t) (j i) (hc i)
    simpa only [sixCorootParameter_scale, hj, he] using hs
  obtain ⟨u, hu, h0, h1, h2, h3, h4, h5⟩ :=
    Theory.AlgebraicGroup.dynkinCartanRelationKernel_E6 t hr
  have ht : t = ![u,u^2,1,1,u,u^2] := by
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]
  refine ⟨u, hu, ?_⟩
  rw [sixCorootMatrix, ht, sixCorootParameter_central]
  rfl

end Generic

local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- A central E7 six-node value in the six-coroot torus is an explicit cubic word. -/
theorem e7Six_eq_centralWord_of_torus (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) (t : Fin 6 → Fˣ)
    (ht : (e7Six F w).val = sixCorootMatrix F e7Node t) :
    ∃ u : Fˣ, u ^ 3 = 1 ∧ e7Six F w = e7Six F (centralWord F u) := by
  have hj (i k : Fin 6) :
      typeE7RootPairing.pairingIn ℤ (e7Node i) (e7Node k) = typeE6CartanMatrix i k := by
    exact (typeE7RootPairing_base_cartan_apply _ _).trans (e7_cartan_restrict i k)
  have hcomm (i : Fin 6) : Commute (sixCorootMatrix F e7Node t)
      (rootCurveUnit (integralChevalleyRootOperators (P := typeE7RootPairing)
        (b := typeE7RootPairing_base)) (e7Node i) (1 : F)) := by
    have hh := congrArg Subtype.val (hc (FreeGroup.of (true, i, (1 : F)))).eq
    change _ * _ = _ * _
    simpa only [Subgroup.coe_mul, ht, e7Six_of, e7Simple, signedSimple,
      Bool.true_eq, ↓reduceIte, ExceptionalSplit.elementaryRoot, e7Node] using hh
  obtain ⟨u, hu, he⟩ := torus_eq_centralMatrix F e7Node hj t hcomm
  refine ⟨u, hu, Subtype.ext ?_⟩
  rw [ht, he, e7Six_centralWord F u hu]

/-- A central E8 six-node value in the six-coroot torus is an explicit cubic word. -/
theorem e8Six_eq_centralWord_of_torus (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) (t : Fin 6 → Fˣ)
    (ht : (e8Six F w).val = sixCorootMatrix F e8Node t) :
    ∃ u : Fˣ, u ^ 3 = 1 ∧ e8Six F w = e8Six F (centralWord F u) := by
  have hj (i k : Fin 6) :
      typeE8RootPairing.pairingIn ℤ (e8Node i) (e8Node k) = typeE6CartanMatrix i k := by
    exact (typeE8RootPairing_base_cartan_apply _ _).trans (e8_cartan_restrict i k)
  have hcomm (i : Fin 6) : Commute (sixCorootMatrix F e8Node t)
      (rootCurveUnit (integralChevalleyRootOperators (P := typeE8RootPairing)
        (b := typeE8RootPairing_base)) (e8Node i) (1 : F)) := by
    have hh := congrArg Subtype.val (hc (FreeGroup.of (true, i, (1 : F)))).eq
    change _ * _ = _ * _
    simpa only [Subgroup.coe_mul, ht, e8Six_of, e8Simple, signedSimple,
      Bool.true_eq, ↓reduceIte, ExceptionalSplit.elementaryRoot, e8Node] using hh
  obtain ⟨u, hu, he⟩ := torus_eq_centralMatrix F e8Node hj t hcomm
  refine ⟨u, hu, Subtype.ext ?_⟩
  rw [ht, he, e8Six_centralWord F u hu]

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction
