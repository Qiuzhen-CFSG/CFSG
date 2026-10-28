module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The source setup for lower bounds on weak closure

Hypothesis E.6.1 of Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.244–245 (PDF pp.255–256).
Maximality is among two-local subgroups. Normality of `V` is inside `T`;
the TI condition only concerns conjugation by `M`.

The obstruction family is Definition E.6.4. Its residual is `O^{2'}`,
the intersection of normal subgroups of odd index, computed inside `C_M(U)`
and then mapped to the ambient group. It is neither `O₂` nor `O²`.
The class `K` is explicit, as in the shared QTKE interface; source classification
results must instantiate it with the full known-simple catalogue.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06

open Subgroup

universe u
variable {G : Type u} [Group G]

/-- The source subgroup `M_V = N_M(V)`. -/
def localNormalizer (M V : Subgroup G) : Subgroup G :=
  M ⊓ normalizer (V : Set G)

/-- The source subgroup `Q = C_T(V)`. -/
def sylowCentralizer (T V : Subgroup G) : Subgroup G :=
  T ⊓ centralizer (V : Set G)

/-- The source subgroup `Z = C_V(T)`. -/
def sylowFixedSpace (T V : Subgroup G) : Subgroup G :=
  V ⊓ centralizer (T : Set G)

/-- Exactly the three clauses of Hypothesis E.6.1. No centralizer bound or
classification conclusion is included among these inputs. -/
structure HypothesisE61 [Finite G] (K : GroupClass.{u})
    (T : Sylow 2 G) (M V : Subgroup G) : Prop where
  simpleQTKE : IsSimpleQTKE K G
  maximalTwoLocal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  nontrivial : V ≠ ⊥
  elementary : IsElementaryAbelian 2 V
  le_sylow : V ≤ T
  normal_in_sylow : (V.subgroupOf (T : Subgroup G)).Normal
  ti : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
    V.map (MulAut.conj g).toMonoidHom = V
  unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
    localNormalizer M V ⊓ normalizer (sylowCentralizer (T : Subgroup G) V : Set G) ≤ N →
      N = M

/-- The local residual condition in Definition E.6.4. -/
def oddCentralizerCondition (M V U : Subgroup G) : Prop :=
  (primeToResidual 2 ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype ≤ M ⊓ centralizer (V : Set G)

/-- Definition E.6.4: nonidentity subspaces with an escaping centralizer
and odd induced centralizer on `V`. -/
def obstructionFamily (M V : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ V ∧ U ≠ ⊥ ∧ ¬ centralizer (U : Set G) ≤ M ∧
    oddCentralizerCondition M V U}

end CFSG.Quasithin.ChapterE.Section06
