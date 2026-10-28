module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs
public import Theory.GroupTheory.ConjugateSubgroupClosure
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Local interfaces for the opposite-involution argument

The cyclic TI input is the first paragraph of 14.3.22, taken explicitly by
this conditional branch. Its closure uses whole conjugate subgroups in T.
The second interface records the local calculations needed before recognizing
the actual global centralizer. It is an obligation, not a source theorem:
its construction must supply the three factors, local actions and Sylow
arrangement on the original T.

Source: Aschbacher--Smith, 14.3.22, printed pp.998--999.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- The original centralizing supplement D=C_Q(U). -/
abbrev supplement (F : InvariantFlag T V 2) : Subgroup G :=
  F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)

/-- The span of the whole ambient conjugates of D contained in the supplied T. -/
abbrev span (F : InvariantFlag T V 2) : Subgroup G :=
  conjugateSubgroupClosure (supplement F) (T : Subgroup G)

/-- The original two-residual, embedded in G; this is O²(H), not O₂(H). -/
abbrev localResidual (F : InvariantFlag T V 2) : Subgroup G :=
  (pResidual 2 F.H).map F.H.subtype

/-- The exact cyclic/TI branch input. No centralizer recognition or opposite
involution is included among these premises. -/
structure CyclicTIInput (F : InvariantFlag T V 2) (L : Subgroup G) : Prop where
  strict : F.Vi 1 < supplement F
  cyclic : IsCyclic (supplement F)
  card : Nat.card (supplement F) = 4
  ti : ∀ a : G, supplement F ⊓ conjugate (supplement F) a = ⊥ ∨
    conjugate (supplement F) a = supplement F
  abelian : IsMulCommutative (span F)
  seed_le : V ≤ span F
  weakly_closed : ∀ a : G, conjugate (span F) a ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
    conjugate (span F) a = span F
  normalized : L ⊔ (T : Subgroup G) ≤ normalizer (span F : Set G)
  conjugates : {A : Subgroup G | ∃ a : G,
      conjugate (supplement F) a = A ∧ A ≤ (T : Subgroup G)} =
    {A : Subgroup G | ∃ a ∈ L, conjugate (supplement F) a = A}
  three : {A : Subgroup G | ∃ a ∈ L, conjugate (supplement F) a = A}.ncard = 3

/-- Local conclusions to be constructed from the three cyclic factors and
the marked six-letter action. These are explicit hypotheses for the separate
global recognition step; this record asserts no existence. -/
structure LocalGeometry (F : InvariantFlag T V 2) (L : Subgroup G) (z w : G) : Prop where
  point : F.Vi 1 = zpowers z
  triple : ∃ d ∈ supplement F, ∃ a ∈ L,
    zpowers d = supplement F ∧ d ^ 2 = z ∧
    w = d * (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d
  mem_sylow : w ∈ (T : Subgroup G)
  involution : orderOf w = 2
  nonfusion : ¬ IsConj z w
  product_fusion : IsConj w (w * z)
  omega_center : omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({w} : Set G)) =
    closure ({z, w} : Set G)
  local_sylow : ∃ S : Sylow 2 (F.H ⊓ centralizer ({w} : Set G) : Subgroup G),
    (S : Subgroup _).map (F.H ⊓ centralizer ({w} : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer ({w} : Set G)
  span_model : Nonempty (span F ≃*
    ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 2)))
  span_core_omega : omegaOneAmbient (span F ⊓ F.U) = V
  core_commutator : ⁅(F.I₂ L).pCoreIn 2, zpowers w⁆ = V
  core_centralizer : (F.I₂ L).pCoreIn 2 ⊓ centralizer ({w} : Set G) =
    span F ⊓ (F.I₂ L).pCoreIn 2
  core_centralizer_model : Nonempty
    (((F.I₂ L).pCoreIn 2 ⊓ centralizer ({w} : Set G) : Subgroup G) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
  parabolic_frattini : F.I₂ L = (F.I₂ L).pCoreIn 2 ⊔
    (F.I₂ L ⊓ centralizer ({w} : Set G))
  parabolic_quotient : ∃ q : (F.I₂ L ⊓ centralizer ({w} : Set G) : Subgroup G) →*
      Equiv.Perm (Fin 3), Function.Surjective q ∧
    q.ker = ((F.I₂ L).pCoreIn 2).subgroupOf (F.I₂ L ⊓ centralizer ({w} : Set G))
  residual_centralizer : ∃ E B : Subgroup G,
    Nonempty (E ≃* Multiplicative (ZMod 4)) ∧
    Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    E ≤ centralizer (B : Set G) ∧ E ⊓ B = F.Vi 1 ∧
    E ⊔ B = localResidual F ⊓ centralizer ({w} : Set G)
  plane_centralizes : V ≤ centralizer ({w} : Set G)
  plane_moved : ⁅V, F.I₂ L ⊓ centralizer ({w} : Set G)⁆ = V
  quotient_normal : ((localResidual F ⊔ (F.I₂ L).pCoreIn 2).subgroupOf F.H).Normal
  quotient_index : ((localResidual F ⊔ (F.I₂ L).pCoreIn 2).subgroupOf F.H).index = 4
  outside_residual : w ∉ localResidual F ⊔ (F.I₂ L).pCoreIn 2

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
