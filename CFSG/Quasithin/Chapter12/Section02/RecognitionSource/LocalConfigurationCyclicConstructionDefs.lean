module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicDefs

/-!
# The pair input to the construction in 12.2.21--22

This boundary records the odd Sylow supplement and the actual two-conjugate
pair produced before the invariant-Sylow selection. It does not assume that
an inverter normalizes P, that P has prime order, or that the pair core U
is normal in H. The quotient map is the literal H → H/O₂(H).

The construction module proves U ≤ O₂(H) and builds the elementary H-orbit
of U ∩ V from these inputs. Existence of this seed and the later invariant
Sylow selection remain separate source obligations.
Source: Aschbacher--Smith, 12.2.20--22, printed pp.802--803.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The odd supplement and TI pair before the invariant-Sylow selection.
The element g is not yet asserted to have prime order. -/
structure CyclicConstructionSeed (T : Sylow 2 G) (L V : Subgroup G)
    (d p : ℕ) (H P U : Subgroup G) (g : G) : Prop where
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))
  prime : p.Prime
  odd_prime : Odd p
  pgroup : IsPGroup p P
  sylow : ∃ S : Sylow p H, (S : Subgroup H).map H.subtype = P
  escapes : ¬ P ≤ normalizer (L : Set G)
  overgroup : H = P ⊔ (T : Subgroup G)
  factorization : ∀ x ∈ H, ∃ a ∈ P, ∃ t ∈ (T : Subgroup G), x = a * t
  quotient_core : (P.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
    pCore p (H ⧸ pCore 2 H)
  quotient_two : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H))
  frattini_intersection : (frattini P).map P.subtype = P ⊓ normalizer (L : Set G)
  generator_mem : g ∈ P
  pair_core : (cyclicPairJoin (zpowers g) U V).pCoreIn 2 = U
  pair_generated : cyclicPairJoin (zpowers g) U V =
    V ⊔ V.map (MulAut.conj g).toMonoidHom
  pair_disjoint : Disjoint V (V.map (MulAut.conj g).toMonoidHom)
  core_generated : U = (U ⊓ V) ⊔ (U ⊓ V).map (MulAut.conj g).toMonoidHom
  pair_fixed : U ⊓ centralizer (zpowers g : Set G) = ⊥
  core_moved : ⁅U, zpowers g⁆ = U
  transvections : ⁅U, V⁆ = U ⊓ V
  action_kernel : U ⊓ centralizer (V : Set G) = U ⊓ V
  hyperplane_index : (U ⊓ V).relIndex V = 2
  hyperplane : Nat.card (U ⊓ V : Subgroup G) = 2 ^ (d - 1)

/-- The remaining conclusions of the invariant-Sylow selection. This is
an output to be constructed, never a hypothesis of the original theorem. -/
structure CyclicInvariantSelection (T : Sylow 2 G) (L V : Subgroup G)
    (d p : ℕ) (H P U : Subgroup G) (g v : G) : Prop
    extends CyclicConstructionSeed T L V d p H P U g where
  alternatives : Nat.card P = p ∨
    (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
    (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p)
  generator_order : orderOf g = p
  inverter_mem : v ∈ V
  inverter_outside : v ∉ U
  inverts_generator : v * g * v⁻¹ = g⁻¹
  inverter_normalizes : v ∈ normalizer (P : Set G)
  inverts_frattini_quotient : ∀ x ∈ P,
    v * x * v⁻¹ * x ∈ (frattini P).map P.subtype
  frattini_normalizes : (frattini P).map P.subtype ≤ normalizer (V : Set G)
  residual : (pResidual 2 H).map H.subtype =
    P ⊔ componentOrbit (H.pCoreIn 2 ⊓ V) H

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
