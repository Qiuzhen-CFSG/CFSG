module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Mathlib.GroupTheory.Frattini

/-!
# Higher Thompson weak-closure constructions

These are the actual subgroup constructions in E.5.1–2, not certificates for
their conclusions. All Thompson groups use the rank-indexed families of B.2.2.
The core of a local subgroup is mapped into the common ambient group, whereas
the Frattini preimage and residual centralizer are computed intrinsically.
The small-index condition is the binary rank of `D/D₁`, expressed by the
relative index; it always includes the containment `D₁ ≤ D`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, E.5.1–2, printed pp.242–243.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Stellmacher ChapterB Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The subgroup `Ω₁(Z(J_k(P)))` occurring throughout E.5. -/
noncomputable def higherThompsonCenter (P : Subgroup G) (k : ℕ) : Subgroup G :=
  omegaOneCenterAmbient (thompsonJ P k)

/-- The subgroup `W = ⟨B ∈ A_k(P) : B ≤ O₂(K)⟩` of E.5.1. -/
noncomputable def higherThompsonCore (P K : Subgroup G) (k : ℕ) : Subgroup G :=
  sSup {B : Subgroup G | B ∈ thompsonFamily P k ∧ B ≤ (pCore 2 K).map K.subtype}

/-- `O_{2,Φ(F*)}(K)`: the preimage of the Frattini subgroup of
`F*(K/O₂(K))`, computed inside that generalized Fitting subgroup. -/
noncomputable def weakClosureOddRadical (K : Type*) [Group K] : Subgroup K :=
  let π := QuotientGroup.mk' (pCore 2 K)
  let F := generalizedFitting (K ⧸ pCore 2 K)
  ((frattini F).map F.subtype).comap π

/-- The additional centralizer assumption in E.5.1. The centralizer is
inside the two-residual `O²(K)`, and the two source branches use their own `R`. -/
def WeakClosureCentralizerBound (P A K : Subgroup G) : Prop :=
  (ECaseOdd A K ∧
    pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ weakClosureOddRadical K) ∨
  (ECaseComponent P A K ∧
    pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ solvableRadical K)

/-- The subgroups of `D` whose quotient has binary rank at most `k`. -/
noncomputable def smallIndexSubgroups (D : Subgroup G) (k : ℕ) : Set (Subgroup G) :=
  {D₁ | D₁ ≤ D ∧ Nat.log 2 (D₁.relIndex D) ≤ k}

/-- The subgroup asserted to be all of `G` in E.5.2. -/
noncomputable def thompsonCentralizerGenerators (P : Subgroup G) (i j : ℕ) :
    Subgroup G :=
  normalizer (thompsonJ P i : Set G) ⊔
    ⨆ D₁ : {D₁ : Subgroup G // D₁ ∈ smallIndexSubgroups
      (higherThompsonCenter P (i + j)) (i + j)},
      thompsonJ (centralizer (D₁.val : Set G)) i

end CFSG.Quasithin.ChapterE
