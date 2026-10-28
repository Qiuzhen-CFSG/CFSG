module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.FixedSpace
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Transitivity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Flag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Selection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.CanonicalSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.ChosenIntersection

/-!
# Source component reduction on the original chosen flag

Source 11.4.1(1) follows from the earlier SL3 fixed-space result and the full
Proposition1132At implication. The natural-action transitivity is proved from
the actual marking and lifted to the original subgroup. The application to
11.5.2(1) then constructs a point-centralizing conjugator for each conjugate
containing z. The same source implication constructs an outside H-star in
C_G(z), and Kz has its literal relative normality.

The public application `Radical.ofFlag_refinement_and_bounds_of_preceding_sources`
supplies 11.4.1(2–3) on the same flag: it excludes both field-four triangle
orientations, gives the exact surviving refinement and proves
R₁ ≤ O∞(KT) and [R₁,X] ≤ O₂(KT). It retains the literal K, R₁, X and
quotient maps, and uses the local overgroup KR₁X without requiring X to
normalize T. The separate conditional Fitting-index APIs remain available;
that stronger intermediate bound is not needed for this application.

The component and natural-shadow assembly owners discharge the explicit
earlier inputs: the normal point-local component, point centralization,
seed containment, X-normalization of V₁ and R₁, central-omega placement,
the full 11.1.2 alternatives, source 3.2.5 and 7.0.1 recognition,
Proposition1132At and the G₂ weak-closure clauses of 11.2.2.
The later Kz=K, decompositions, n(H)=1 and outside R1-Sylow witness belong
to that assembly. The output record in Selection is a target for the witness,
not an existence assertion.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.4.1--11.5.2, printed pp.775--779.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Both clauses of source 11.4.1(1), without assuming fixed-space vanishing
or transitivity. The two explicit implications belong to earlier sources. -/
theorem fixed_and_transitive
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D S U₁ H → Proposition1132At D S U₁ H) :
    V ⊓ centralizer (L : Set G) = ⊥ ∧
      ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ l ∈ L, (MulAut.conj l) x = y := by
  have hf := fixed_trivial D S U₁ hlinear h1132
  exact ⟨hf, fun _ hx hx1 _ hy hy1 => vector_transitive D S hf hx hy hx1 hy1⟩

/-- The actual closure consumer 11.5.2(1), now with its transitivity premise
discharged by 11.4.1(1) on the same chosen module and source point. -/
theorem conjugate_through_source_point (E : Closure.Geometry D)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ E.input.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D E.input E.point H →
      Proposition1132At D E.input E.point H)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (g : G) (hg : E.z ∈ V.map (MulAut.conj g : G →* G)) :
    ∃ c ∈ centralizer ({E.z} : Set G),
      V.map (MulAut.conj c : G →* G) = V.map (MulAut.conj g : G →* G) :=
  E.conjugate_through_z hz hz1 (fixed_and_transitive D E.input E.point hlinear h1132).2 g hg

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
