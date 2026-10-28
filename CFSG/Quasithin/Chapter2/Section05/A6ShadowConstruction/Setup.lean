module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Incoming hypotheses for the terminal A₆ construction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.554–558 and 567–570, Notation 2.5.4 and Lemmas 2.5.5, 2.5.11–13,
2.5.23, 2.5.25, and 2.5.27.

This record collects the source inputs owned by the preceding shadow argument.
Its action is an actual surjective conjugation action on `alternatingGroup
(Fin 6)` with the specified kernel. Its normality assertions are relative to
`H` or `S`. The final elementary-sixteen subgroup, its normalizer, the embedding
of `S_C` in `C₂ × D₈`, and all final order computations are deliberately absent.

Concrete finite-model identities, needed in addition to this setup, belong to
the Aut(A₆) model development; the construction's conditional theorems must
state exactly which such identities they use.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction

open Subgroup

/-- Genuine incoming data for the construction following Lemma 2.5.27.
`largestPairs` is the forward direction of the actual correspondence in
2.5.23, including global maximality among the chapter's local bases.
`normalizerSylow` retains the Sylow assertion in that same lemma. -/
public structure Setup (G : Type*) [Group G] where
  H : Subgroup G
  K : Subgroup G
  S : Subgroup G
  T : Subgroup G
  M : Subgroup G
  generated : H = K ⊔ S
  normalK : (K.subgroupOf H).Normal
  modelK : K ≃* alternatingGroup (Fin 6)
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H).map H.subtype = S
  twoT : IsPGroup 2 T
  s_le_t : S ≤ T
  x : G
  x_mem : x ∈ T
  x_normalizes : x ∈ normalizer (S : Set G)
  x_outside : x ∉ S
  square_mem : x ^ 2 ∈ S
  core_eq : S ⊓ centralizer (K : Set G) = twoCore H
  core_disjoint : Disjoint (S ⊓ centralizer (K : Set G))
    ((S ⊓ centralizer (K : Set G)).map (MulAut.conj x⁻¹).toMonoidHom)
  core_commutes : S ⊓ centralizer (K : Set G) ≤ centralizer
    (((S ⊓ centralizer (K : Set G)).map (MulAut.conj x⁻¹).toMonoidHom) : Set G)
  t : G
  zK : G
  z : G
  t_mem : t ∈ S ⊓ centralizer (K : Set G)
  t_ne_one : t ≠ 1
  t_square : t ^ 2 = 1
  center_s : (center S).map S.subtype = zpowers t ⊔ zpowers zK
  center_sk : (center (S ⊓ K : Subgroup G)).map (S ⊓ K).subtype = zpowers zK
  t_conjugate : x⁻¹ * t * x = zK
  z_eq : z = t * zK
  action : H →* MulAut (alternatingGroup (Fin 6))
  action_surjective : Function.Surjective action
  action_compatible : ∀ (h : H) (k : K),
    (modelK.symm (action h (modelK k)) : G) = (h : G) * k * (h : G)⁻¹
  action_kernel : action.ker = (S ⊓ centralizer (K : Set G)).subgroupOf H
  alternatives :
    Nonempty ((S ⊓ centralizer (K : Set G) : Subgroup G) ≃* Multiplicative (ZMod 4)) ∨
    Nonempty ((S ⊓ centralizer (K : Set G) : Subgroup G) ≃* Multiplicative (ZMod 8)) ∨
    Nonempty ((S ⊓ centralizer (K : Set G) : Subgroup G) ≃* QuaternionGroup 2)
  largestPairs : ∀ (E : Subgroup G), E ≤ S ⊓ K → IsKleinFour E →
    (S ⊓ normalizer (E : Set G), H ⊓ normalizer (E : Set G)) ∈
        localPairs (Chapter1.He G) M ∧
      ∀ W ∈ localBases (Chapter1.He G) M,
        Nat.card W ≤ Nat.card (S ⊓ normalizer (E : Set G) : Subgroup G)
  normalizerSylow : ∀ (E : Subgroup G), E ≤ S ⊓ K → IsKleinFour E →
    ∃ P : Sylow 2 (H ⊓ normalizer (E : Set G) : Subgroup G),
      (P : Subgroup (H ⊓ normalizer (E : Set G) : Subgroup G)).map
        (H ⊓ normalizer (E : Set G)).subtype = S ⊓ normalizer (E : Set G)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
