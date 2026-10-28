module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryComplement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.RadicalModels

/-!
# The conditional linear-three branch endgame

For the linear-three branch in Aschbacher--Smith, original 15.2.23
(printed pp. 1116--1117), the nonbinary descent reduces to the binary
block. The binary complement gives the second cubic factor centralizing
that block modulo its two-core. Its commutator with the actual
three-prime residual contradicts the corrected conjugate-pair form of
15.2.22. Both possible labels for the distinguished factors are handled.

This module preserves the general conditional consumers. `RadicalModels`
discharges the radical alternative from the literal 15.2.12 models;
`FactorRecognition` and `SourceExclusion` discharge factor recognition
using the original wreath action and assemble the source branch exclusion.
The faithful action, preliminary outside-`Mc` reduction, partner containment,
and seed-family commutator retain their earlier source owners, named in
`SourceExclusion`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private def swapSplit (hI : PlaneEscapes Mc ZS I)
    (s : SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H)) :
    SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H) where
  H₁ := s.H₂
  H₂ := s.H₁
  K₁ := s.K₂
  K₂ := s.K₁
  t := s.t
  t_mem := s.t_mem
  t_not_mem := s.t_not_mem
  K_sup_S := s.K_sup_S.trans (sup_comm _ _)
  K₁_sup_K₂ := (sup_comm _ _).trans s.K₁_sup_K₂
  K₁_le := s.K₂_le
  K₂_le := s.K₁_le
  K₁_conj := by
    have ht2 : s.t ^ 2 ∈ planeSylow T ZS :=
      ((planeSylow T ZS).subgroupOf (T : Subgroup G)).sq_mem_of_index_two
        (d.escape_index hI).2 ⟨s.t,s.t_mem⟩
    rw [← s.K₁_conj]
    change (s.K₁.conjBy s.t).conjBy s.t = s.K₁
    rw [conjBy_conjBy,← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (s.S_normalizes_K₁ ht2)
  S_normalizes_K₁ := s.S_normalizes_K₂
  S_normalizes_K₂ := s.S_normalizes_K₁

include d in
/-- The literal binary contradiction using the corrected conjugate-pair
15.2.22 reduction. Both possible distinguished-factor labels are handled;
the local complement, action quotient and commutator are constructed here. -/
theorem Branch.binary_false_of_conjugate_pair
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (s : SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H))
    (hclassify : ∀ E : Subgroup G, E ≤ smallActionK H → IsPPerfect 2 E →
      Nat.card (E ⧸ pCore 2 E) = 3 → planeSylow T ZS ≤ normalizer (E : Set G) →
      E = s.K₁ ∨ E = s.K₂)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj s.t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj s.t).toMonoidHom)
    (hKK : ⁅s.K₁,s.K₂⁆ ≤ s.K₁ ⊓ s.K₂) : False := by
  let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
  obtain ⟨hYNI,hpY,hSY,hqY,_⟩ := b.binary_source_residual_data d hI hout f hker hC
  have seed : SmallActionsSource.Seed M I (planeSylow T ZS) Y := ⟨hYNI,hpY,hSY,hqY⟩
  obtain ⟨hLK,hpL,hcL,hSL,_,_⟩ := b.binary_factor_data_of_action d hI hout f hker
  rcases hclassify _ hLK hpL hcL hSL with hfirst | hfirst
  · exact SmallActionsSource.commutator_exclusion_of_pair d hI hfit s seed hC hYY hKK
      (b.binary_distinguished_commutator d hI hout f hker hC s hfirst.symm hclassify).2
  · let s' := swapSplit d hI s
    have hclassify' : ∀ E : Subgroup G, E ≤ smallActionK H → IsPPerfect 2 E →
        Nat.card (E ⧸ pCore 2 E) = 3 → planeSylow T ZS ≤ normalizer (E : Set G) →
        E = s'.K₁ ∨ E = s'.K₂ := by
      intro E hEK hp hc hS
      exact (hclassify E hEK hp hc hS).symm
    have hKK' : ⁅s'.K₁,s'.K₂⁆ ≤ s'.K₁ ⊓ s'.K₂ := by
      change ⁅s.K₂,s.K₁⁆ ≤ s.K₂ ⊓ s.K₁
      rwa [commutator_comm,inf_comm]
    exact SmallActionsSource.commutator_exclusion_of_pair d hI hfit s' seed hC hYY hKK'
      (b.binary_distinguished_commutator d hI hout f hker hC s' hfirst.symm hclassify').2


include d in
/-- The all-degree literal branch consumer. Parity descent, binary normality,
the complementary factor, the intrinsic S₃ quotient and the final commutator
are all supplied by this branch. The displayed source and local geometry
premises retain the owners described in the module overview and are not
asserted by this conditional theorem. -/
theorem Branch.false_of_local_source_data
    {n : ℕ} {F : Type} [Field F] [Finite F] (b : Branch M I X n F)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hcases : smallActionKc H Mc = smallActionK H ∨
      IsPGroup 2 (solvableRadical (smallActionKc H Mc)))
    (s : SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H))
    (hclassify : ∀ E : Subgroup G, E ≤ smallActionK H → IsPPerfect 2 E →
      Nat.card (E ⧸ pCore 2 E) = 3 → planeSylow T ZS ≤ normalizer (E : Set G) →
      E = s.K₁ ∨ E = s.K₂)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj s.t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj s.t).toMonoidHom)
    (hKK : ⁅s.K₁,s.K₂⁆ ≤ s.K₁ ⊓ s.K₂) : False := by
  have he := b.degree_eq_one d hI
  subst n
  have hc := b.binary_centralizer_threePrime_of_radical_alternative d hI (hout rfl)
    f hker hKcI hcases
  exact b.binary_false_of_conjugate_pair d hI hfit (hout rfl) f hker hc s hclassify hYY hKK

include d in
/-- The literal earlier component alternatives discharge the radical premise
in the all-degree source consumer. Factor recognition remains explicit. -/
theorem Branch.false_of_source_alternatives
    {n : ℕ} {F : Type} [Field F] [Finite F] (b : Branch M I X n F)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc)
    (s : SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H))
    (hclassify : ∀ E : Subgroup G, E ≤ smallActionK H → IsPPerfect 2 E →
      Nat.card (E ⧸ pCore 2 E) = 3 → planeSylow T ZS ≤ normalizer (E : Set G) →
      E = s.K₁ ∨ E = s.K₂)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj s.t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj s.t).toMonoidHom)
    (hKK : ⁅s.K₁,s.K₂⁆ ≤ s.K₁ ⊓ s.K₂) : False :=
  b.false_of_local_source_data d hI hfit hout f hker hKcI
    (partner_radical_alternative d hc) s hclassify hYY hKK

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
