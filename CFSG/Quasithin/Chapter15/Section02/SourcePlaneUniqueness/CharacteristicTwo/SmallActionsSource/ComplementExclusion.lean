module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MarkedPair
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryComplement

/-!
# Excluding the original linear-three component without a factor recognition premise

The canonical seed Y = O^{3′}(NI) cannot mutually normalize any S-invariant
normal cubic residual E of K. Start the conjugate pair with E, reverse that
pair using t⁻¹, and apply the already proved canonical-seed normalizer argument.
This uses the literal quotient and Omega action throughout.

For the binary linear-three component, BinaryComplement constructs such an E
from the kernel of the action on X/O₂(X), with [X,E] ≤ O₂(X). MarkedPair proves
K = Kc from the normality of O²(K ∩ X) in MI, so 15.2.21(2) supplies the
three-prime centralizer. The original parabolic quotient and residual identity
then give [Y,E] ≤ Y ∩ E, the required contradiction. The all-degree consumer
first applies the existing nonbinary descent.

The earlier component-orbit alternative and Omega action remain source inputs
of qt-e-152-plane-geometry and qt-e-152-small-parabolic. The outside-Mc
preliminary reduction belongs to qt-e-152-char2-block-exclusion. Final discharge
remains with qt-e-152-plane-uniqueness. This closes the linear-three branch from
these inputs; it does not identify the marked H₁,H₂ or establish the L₄(2)
exclusion and arbitrary-seed version of 15.2.22.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.2.21--23,
printed pp.1114--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G]

/-- Reverse the actual conjugate pair, retaining the inverse conjugator. -/
def ResidualPair.reverse {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    ResidualPair A S K t⁻¹ where
  K₁ := p.K₂
  K₂ := p.K₁
  t_mem := A.inv_mem p.t_mem
  t_not_mem := by simpa only [inv_mem_iff] using p.t_not_mem
  first := p.second
  second := p.first
  span := sup_comm _ _ |>.trans p.span
  conjugate := by
    rw [← p.conjugate, map_map]
    have he : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [he,map_id]
  normalized := p.second_normalized hSA hi

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d
open ChapterD.UniqueFactor

/-- Every S-invariant normal cubic factor is excluded by the canonical seed. -/
theorem canonical_seed_exclusion_any_factor
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      Nonempty (((Y ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    {E : Subgroup G} (hE : E ∈ normalCubicResiduals (smallActionK H))
    (hSE : smallActionS T ZS ≤ normalizer (E : Set G)) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ¬ ⁅Y,E⁆ ≤ Y ⊓ E := by
  have hST : smallActionS T ZS < (T : Subgroup G) := lt_of_le_of_ne inf_le_left (by
    intro he
    have hi := (d.escape_index hI).2
    change (smallActionS T ZS).relIndex (T : Subgroup G) = 2 at hi
    rw [he,relIndex_self] at hi
    omega)
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt hST
  obtain ⟨p,hp⟩ := residualPair_with_first d hI hE hSE t ht htS
  have hh := canonical_seed_commutator_exclusion d hI hfit e hC hquot
    (p.reverse inf_le_left (d.escape_index hI).2)
  change ¬ ⁅(primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype,p.K₁⁆ ≤
    (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ⊓ p.K₁ at hh
  rwa [hp] at hh


/-- The actual binary component is impossible. The action kernel constructs
an S-invariant normal cubic complement. The canonical-seed normalizer argument
excludes that complement directly, without a marked-factor classification premise. -/
theorem binary_component_false_from_preceding
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) : False := by
  have hST : smallActionS T ZS < (T : Subgroup G) := lt_of_le_of_ne inf_le_left (by
    intro he
    have hi := (d.escape_index hI).2
    change (smallActionS T ZS).relIndex (T : Subgroup G) = 2 at hi
    rw [he,relIndex_self] at hi
    omega)
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt hST
  obtain ⟨_,_,hK⟩ := binary_pair_and_orbit_eq d horbit hI b hout f hker t ht htS
  have hC := source_15_2_21_2_from_preceding d hK
  obtain ⟨E,hEK,hp,hc,hS,hKE,_,hcomm⟩ := b.binary_complementary_factor d hI hout
    (b.binary_normal_of_action d hI hout f hker)
  have hE : E ∈ normalCubicResiduals (smallActionK H) :=
    ⟨hEK,(normal_subgroupOf_iff_le_normalizer hEK).mpr hKE,hp,hc⟩
  exact canonical_seed_exclusion_any_factor d hI hfit e hC
    (b.binary_source_residual_quotient d hI hout f hker hC) hE hS
    (b.binary_commutator_of_action d hI hout f hker hC hS hp hcomm)

/-- Apply the nonbinary descent and the completed binary contradiction to
the original linear-three branch. Only earlier source inputs and the
preliminary no-block outside-Mc reduction remain explicit. -/
theorem linear_three_component_false_from_preceding
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X n F)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) : False := by
  have hn := b.degree_eq_one d hI
  subst n
  exact binary_component_false_from_preceding d horbit hI hfit e b (hout rfl) f hker

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
