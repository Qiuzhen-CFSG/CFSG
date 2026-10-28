module

public import Theory.Representation.BinaryConjugationSection.NaturalExtension

/-!
# Canonical natural extensions and original triple commutators

Two natural factors V/Z and Q/V, together with an elementary abelian
middle section Q/Z, control the original triple commutator without a
separately supplied representation on Q/Z. The representation and its
coordinates are constructed from literal quotient conjugation, descended
through the given actor map with kernel Q. A subgroup of relative order
sixteen centralized modulo Z gives the fixed-space bound needed by the
natural-extension theorem.

The ambient version keeps the original epimorphism and Sylow subgroup;
its image Sylow subgroup is constructed by the surjective-image theorem.
This is the terminal two-natural-factor step in Niles, “Pushing-up in
finite groups”, Theorem 7.7, printed p.58, using Lemma 3.4, pp.37–39.
-/

public section
noncomputable section

open Subgroup
open scoped IsMulCommutative

namespace Representation.BinaryConjugationSection

open SL2FourNatural

variable {G : Type*} [Group G]

/-- The original marked natural factors determine the middle quotient
action and its triple-commutator bound. -/
theorem triple_commutator_le_of_canonical_natural_factors_modulo
    (H Q V Z : Subgroup G) [Finite Q] [Q.Normal]
    (hQH : Q ≤ H) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (hNQ : H ≤ normalizer (Q : Set G))
    (hNZ : H ≤ normalizer (Z : Set G))
    [(Z.subgroupOf Q).Normal] [IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q)]
    (q : H →* SL) (hq : Function.Surjective q) (hk : q.ker = Q.subgroupOf H)
    (cV : BinaryConjugationSection H V Z (naturalRepresentation.comp q))
    (cQ : BinaryConjugationSection H Q V (naturalRepresentation.comp q))
    (S D : Subgroup G) (hSH : S ≤ H) (hDQ : D ≤ Q) (hSD : ⁅S,D⁆ ≤ Z)
    (hi : Z.relIndex D = 16) (P : Sylow 2 SL)
    (hP : (S.subgroupOf H).map q = (P : Subgroup SL)) : ⁅⁅Q,S⁆,S⁆ ≤ Z := by
  obtain ⟨ρ, c, _⟩ := exists_canonical H Q Z hQH (hZV.trans hVQ) hNQ hNZ q hq hk
  exact triple_commutator_le_of_natural_factors_modulo
    (W := Additive (Q ⧸ Z.subgroupOf Q)) H Q V Z hVQ hZV q hq
    ρ c cV cQ S D hSH hDQ hSD hi P hP

/-- For an ambient epimorphism with kernel Q, both the middle quotient
representation and the image Sylow subgroup are canonical. -/
theorem triple_commutator_le_of_natural_factors_epimorphism_modulo
    [Finite G] (Q V Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hVQ : V ≤ Q) (hZV : Z ≤ V)
    [IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q)]
    (q : G →* SL) (hq : Function.Surjective q) (hk : q.ker = Q)
    (cV : BinaryConjugationSection ⊤ V Z
      (naturalRepresentation.comp (q.comp (⊤ : Subgroup G).subtype)))
    (cQ : BinaryConjugationSection ⊤ Q V
      (naturalRepresentation.comp (q.comp (⊤ : Subgroup G).subtype)))
    (S : Sylow 2 G) (D : Subgroup G) (hDQ : D ≤ Q)
    (hSD : ⁅(S : Subgroup G),D⁆ ≤ Z) (hi : Z.relIndex D = 16) :
    ⁅⁅Q,(S : Subgroup G)⁆,(S : Subgroup G)⁆ ≤ Z := by
  let qtop : (⊤ : Subgroup G) →* SL := q.comp (⊤ : Subgroup G).subtype
  have hqtop : Function.Surjective qtop := by
    intro g
    obtain ⟨x, rfl⟩ := hq g
    exact ⟨⟨x, mem_top x⟩, rfl⟩
  have hktop : qtop.ker = Q.subgroupOf ⊤ := by
    ext x
    change q (x : G) = 1 ↔ (x : G) ∈ Q
    rw [← hk]
    rfl
  have hP : ((S : Subgroup G).subgroupOf ⊤).map qtop =
      (S.mapSurjective hq : Subgroup SL) := by
    change ((S : Subgroup G).subgroupOf ⊤).map
      (q.comp (⊤ : Subgroup G).subtype) = (S : Subgroup G).map q
    rw [← map_map, subgroupOf_map_subtype, inf_top_eq]
  exact triple_commutator_le_of_canonical_natural_factors_modulo
    ⊤ Q V Z le_top hVQ hZV (by rw [normalizer_eq_top]) (by rw [normalizer_eq_top])
    qtop hqtop hktop cV cQ S D le_top hDQ hSD hi (S.mapSurjective hq) hP

end Representation.BinaryConjugationSection
