module

public import CFSG.Quasithin.ChapterF.Section01
public import CFSG.Quasithin.Chapter14.Section01
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Construction

/-!
# The solvable amalgam reduction in §14.2

The original `Setup` and its elementary consequences are retained for API
compatibility. They are conditional reductions, not a proof of Lemma 14.2.21:
`hHmax` together with `hHleMc` already forces the difficult rigidity conclusion,
and `hMleYT` already supplies the difficult direction of the factorization.
Neither is a genuine input in Hypothesis 14.2.1. The quotient tag also carries
no quotient isomorphism. Constructing this setup from the source remains open.

The imported `Construction` module avoids these assumptions when proving
generation and faithfulness inside `G₀`, and records the final centralizer
argument conditional on rigidity. The actual intersection, rank-one local
structure, F.1.12 recognition, and the overgroup rigidity on pp. 988–989 still
require source-faithful proofs. In particular recognition precedes rigidity
in the source; it is not merely a final step after the existing `reduction`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §14.2.2, printed pp. 987--989.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam

open scoped Pointwise
open CFSG.Quasithin.ChapterF

universe u

variable {G : Type u} [Group G] [Finite G]

/-! The three quotient cases used in Theorem 14.2.20.  Keeping this tag in the
setup makes the correspondence available to the later recognition theorem
without identifying an abstract quotient with a concrete model prematurely. -/

public inductive QuotientKind
  | dihedral
  | suzuki
  | linear
  deriving DecidableEq, Repr

/-! Legacy conditional inputs, retained without changing their public types.
`hHmax` is stronger than the source's initial information about `H`; using it
does not discharge the local rigidity argument. `hGenerate` assumes generation
of the ambient group, whereas the source initially works inside `G₀`. -/

public structure Setup (G : Type u) [Group G] [Finite G] where
  H : Subgroup G
  Y : Subgroup G
  T : Subgroup G
  M : Subgroup G
  Mc : Subgroup G
  quotientKind : QuotientKind
  hTleH : T ≤ H
  hYleM : Y ≤ M
  hTleM : T ≤ M
  hMleYT : M ≤ Y ⊔ T
  hHleMc : H ≤ Mc
  hHmax : IsMaximalTwoLocal H
  hMcmax : IsMaximalTwoLocal Mc
  hMcInterYT : Mc ⊓ (Y ⊔ T) = T
  hUniqueYT : ∀ K : Subgroup G, IsMaximalTwoLocal K → Y ⊔ T ≤ K → K = M
  hHnotleM : ¬ H ≤ M
  hGenerate : Subgroup.closure ((H : Set G) ∪ ((Y ⊔ T : Subgroup G) : Set G)) = ⊤
  hFaithful : ∀ N : Subgroup G,
    (N.subgroupOf (H ⊔ (Y ⊔ T : Subgroup G))).Normal →
      N ≤ T → N = ⊥

public theorem twoCore_eq_bot (s : Setup G) :
    pCore 2 (s.H ⊔ (s.Y ⊔ s.T) : Subgroup G) = ⊥ := by
  rw [sup_comm s.H]
  apply Theory.GroupTheory.twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    (s.Y ⊔ s.T) s.H s.M ?_ s.hHnotleM
  intro K hK hYT
  exact s.hUniqueYT K hK hYT

public theorem h_eq_mc (s : Setup G) : s.H = s.Mc := by
  exact s.hHmax.eq_of_le s.hMcmax.1 s.hHleMc

public theorem m_eq_yt (s : Setup G) : s.M = s.Y ⊔ s.T := by
  apply le_antisymm s.hMleYT
  exact sup_le s.hYleM s.hTleM

public theorem intersection_eq_t (s : Setup G) :
    s.H ⊓ (s.Y ⊔ s.T : Subgroup G) = s.T := by
  rw [h_eq_mc s]
  exact s.hMcInterYT

/-! Consequences of the legacy conditional setup. -/

public theorem weak_bn_pair (s : Setup G) :
    WeakBNPair G s.H s.T (s.Y ⊔ s.T : Subgroup G) := by
  apply proposition_F_1_9 s.hGenerate (intersection_eq_t s)
  exact s.hFaithful

public structure Reduction (s : Setup G) where
  hcore : pCore 2 (s.H ⊔ (s.Y ⊔ s.T) : Subgroup G) = ⊥
  hHMc : s.H = s.Mc
  hMYT : s.M = s.Y ⊔ s.T
  hintersection : s.H ⊓ (s.Y ⊔ s.T : Subgroup G) = s.T
  weak : WeakBNPair G s.H s.T (s.Y ⊔ s.T : Subgroup G)

public theorem reduction (s : Setup G) : Reduction s :=
  ⟨twoCore_eq_bot s, h_eq_mc s, m_eq_yt s, intersection_eq_t s, weak_bn_pair s⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
