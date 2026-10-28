module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationDefs
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Frattini

/-!
# The invariant odd-subgroup boundary in 12.2.21--22

Before proving cyclicity, the source has an odd p-group P, a selected element
g of order p inverted by v, the pair I = ⟨V,Vᵍ⟩, its two-core U, and the
larger elementary group W = ⟨Uᴾ⟩. In particular U and W must not be identified
before 12.2.23. The pair join at this stage uses ⟨g⟩, not all of P.

This record is an intermediate conclusion, whose existence remains a source
obligation. It permits independent proofs of the noncyclic exclusion and of
the subsequent block argument. All groups and maps stay in the original G.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004, pp.802--804.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The selected odd subgroup and its invariant elementary module, before
the elementary-square and extraspecial possibilities have been excluded. -/
structure InvariantOddLocalAnalysis (T : Sylow 2 G) (L V : Subgroup G)
    (d p : ℕ) (H P U W : Subgroup G) (g v : G) : Prop where
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))
  prime : p.Prime
  odd_prime : Odd p
  pgroup : IsPGroup p P
  alternatives : Nat.card P = p ∨
    (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
    (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p)
  escapes : ¬ P ≤ normalizer (L : Set G)
  overgroup : H = P ⊔ (T : Subgroup G)
  elementary : IsElementaryAbelian 2 W
  in_core : W ≤ H.pCoreIn 2
  normalizes : H ≤ normalizer (W : Set G)
  generated : W = componentOrbit U P
  residual : (pResidual 2 H).map H.subtype = P ⊔ W
  moved : ⁅W, P⁆ = W
  intersection : W ⊓ V = U ⊓ V
  transvections : ⁅W, V⁆ = U ⊓ V
  action_kernel : U ⊓ centralizer (V : Set G) = U ⊓ V
  hyperplane : Nat.card (U ⊓ V : Subgroup G) = 2 ^ (d - 1)
  frattini_normalizes : (frattini P).map P.subtype ≤ normalizer (V : Set G)
  frattini_intersection :
    (frattini P).map P.subtype = P ⊓ normalizer (L : Set G)
  generator_mem : g ∈ P
  generator_order : orderOf g = p
  inverter_mem : v ∈ V
  inverter_outside : v ∉ U
  inverts_generator : v * g * v⁻¹ = g⁻¹
  inverter_normalizes : v ∈ normalizer (P : Set G)
  inverts_frattini_quotient : ∀ x ∈ P,
    v * x * v⁻¹ * x ∈ (frattini P).map P.subtype
  pair_core : (cyclicPairJoin (zpowers g) U V).pCoreIn 2 = U
  pair_generated : cyclicPairJoin (zpowers g) U V =
    V ⊔ V.map (MulAut.conj g).toMonoidHom
  pair_disjoint : Disjoint V (V.map (MulAut.conj g).toMonoidHom)
  core_generated : U = (U ⊓ V) ⊔ (U ⊓ V).map (MulAut.conj g).toMonoidHom
  pair_fixed : U ⊓ centralizer (zpowers g : Set G) = ⊥

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
