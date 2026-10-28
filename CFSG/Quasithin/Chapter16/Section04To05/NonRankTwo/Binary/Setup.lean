module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Models
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.Defs
public import Stellmacher.ElementaryAbelianMaxDefs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Interfaces for the binary cases of 16.5.12

`EarlierInputs` contains the indicated earlier conclusions of §§16.4–16.5,
specialized to the full binary components. It does not assert any of them
unconditionally. The standing hypothesis, exclusion of J₁, and actual
PSL₄(2)/PSL₅(2) identification are separate inputs to the elimination proof.

`ElementaryConfiguration` is an output of the first part of 16.5.12. Its
construction, including the exclusion of PSL₅(2), the four-group actor, and
the cyclic-four actor, remains an obligation. The final two branches may
use this output while its construction is developed independently.

All subgroups live in G. In particular `centralizerResidual` is O² of the
relative centralizer, whereas `elementaryGroup` uses O₂. Conjugation is
left conjugation. No field states binary exclusion or rank-two recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1183–1199 for the earlier inputs and pp.1200–1201 for the output.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup

variable {G : Type*} [Group G]

/-- The source L_r, with O² taken inside C_L(r). -/
def centralizerResidual (L : Subgroup G) (r : G) : Subgroup G :=
  (pResidual 2 (L ⊓ involutionCentralizer r : Subgroup G)).map
    (L ⊓ involutionCentralizer r).subtype

/-- The particular subgroup A in the second half of 16.5.12. -/
def elementaryGroup (T : Sylow 2 G) (L : Subgroup G) (u : G) : Subgroup G :=
  (L ⊓ involutionCentralizer u).pCoreIn 2 ⊔ commutingSylow T L

/-- The faithful conjugation image, canonically isomorphic to
N_G(A)/C_G(A), rather than an unrelated abstract actor. -/
def normalizerImage (A : Subgroup G) : Subgroup (MulAut A) :=
  A.normalizerMonoidHom.range

/-- Earlier source conclusions needed in the binary elimination. These are
explicit inputs, not advertised proofs of the numbered earlier results. -/
structure EarlierInputs [Finite G] (T : Sylow 2 G) (z : G)
    (L : Subgroup G) (g : G) (R X : Subgroup G) (u : G) : Prop
    extends IntersectionSetup T z L g R where
  /-- The genuine Δ₀ choice preceding 16.4.10. -/
  delta_zero : (centralizer (L : Set G)).conjBy g ∈ deltaZero L
  /-- Source 16.4.10. -/
  full_sylow : SylowIn R ((centralizer (L : Set G)).conjBy g)
  /-- The choice of conjugator in 16.4.2(4). -/
  transport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
    (T : Subgroup G).conjBy g
  /-- Source 16.4.2(1). -/
  faithful_actor : Disjoint R (centralizer (L : Set G))
  /-- Source 16.4.2(2). -/
  component_not_le_conjugate_normalizer :
    ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G)
  /-- Source 16.4.3(2). -/
  conjugate_generated : ⁅L.conjBy g, zpowers z⁆ = L.conjBy g
  /-- The Δ₀ symmetry in 16.4.11(2). -/
  symmetric_delta_zero : centralizer (L : Set G) ∈ deltaZero (L.conjBy g)
  /-- Source 16.4.11(1). -/
  commuting_actors : R ≤ centralizer (commutingSylow T L : Set G)
  /-- The chosen nonidentity involution in Ω₁(R). -/
  mem_actor : u ∈ R
  actor_involution : orderOf u = 2
  /-- The Δ₀ omega containment for this chosen R. -/
  omega_inner : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L
  /-- Source 16.4.4(2). -/
  cyclic_centralizer : IsCyclic (commutingSylow T L) →
    centralizer (L : Set G) ⊓ involutionCentralizer z = commutingSylow T L
  /-- Source 16.5.6(1), with no L₃ exception in these binary cases. -/
  residual_at_actor : ∀ r ∈ R, orderOf r = 2 → X = centralizerResidual L r
  /-- The other half of source 16.5.6(1). -/
  residual_at_commuting : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
    X = centralizerResidual (L.conjBy g) i
  /-- Source 16.5.5 and 16.5.6(2). -/
  residual_centralizes : X ≤ centralizer (R : Set G)
  /-- Source 16.5.6(3). -/
  conjugator_normalizes_residual : g ∈ normalizer (X : Set G)
  /-- Source 16.4.9(3), using the actual inner involution. -/
  detect : ∀ J : Subgroup G,
    (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
    ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L
  /-- The centerless specialization of 16.5.10(5), for every Δ₀ conjugate.
  Centerlessness remains a premise until supplied by the actual model. -/
  avoid_twoCentral : Disjoint L (centralizer (L : Set G)) →
    ∀ J ∈ deltaZero L, ∀ i k v : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      v ∈ L → i = k * v → ¬ IsTwoCentralIn L v

/-- The intermediate output to construct before splitting on A ≤ L'K'.
These are conclusions of 16.5.12, never acceptable as its final premises. -/
structure ElementaryConfiguration [Finite G] (T : Sylow 2 G) (z u g : G)
    (L R : Subgroup G) : Prop where
  four_dimensional : ClassicalGroup.IsPSL L 4 2
  centerless : Disjoint L (centralizer (L : Set G))
  normalizer_product : normalizer (L : Set G) =
    (L ⊔ centralizer (L : Set G)) ⊔ (T : Subgroup G)
  actor_eq : R = zpowers u
  actor_card : Nat.card R = 2
  commuting_eq : commutingSylow T L = zpowers z
  commuting_card : Nat.card (commutingSylow T L) = 2
  centralizer_eq : involutionCentralizer z = L ⊔ (T : Subgroup G)
  elementary : IsElementaryAbelian 2 (elementaryGroup T L u)
  elementary_card : Nat.card (elementaryGroup T L u) = 32
  elementary_le_sylow : elementaryGroup T L u ≤ (T : Subgroup G)
  elementary_le_conjugate : elementaryGroup T L u ≤ (T : Subgroup G).conjBy g
  thompson_centralizer : elementaryGroup T L u =
    Stellmacher.elementaryAbelianMaxJ
      ((componentSylow T L ⊔ commutingSylow T L) ⊓ involutionCentralizer u)
  symmetric_product : Nonempty
    ((L ⊔ (T : Subgroup G) : Subgroup G) ≃*
      (Equiv.Perm (Fin 8) × Multiplicative (ZMod 2)))
  centralizer_core_model : Nonempty
    (((L ⊔ (T : Subgroup G)) ⊓ involutionCentralizer u).pCoreIn 2 ≃*
      (DihedralGroup 4 × (Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
  thompson_core :
    Stellmacher.elementaryAbelianMaxJ
      (((L ⊔ (T : Subgroup G)) ⊓ involutionCentralizer u).pCoreIn 2) =
    ((L ⊔ (T : Subgroup G)) ⊓ involutionCentralizer u).pCoreIn 2
  conjugate_involution : MulAut.conj g z = u
  actor_mem_elementary : u ∈ elementaryGroup T L u
  central_mem_elementary : z ∈ elementaryGroup T L u
  actor_ne_central : u ≠ z

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary
