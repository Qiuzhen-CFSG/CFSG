module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.CoreQuotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.NaturalGeometry
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.BinaryPermutation.TransvectionCoreMap

/-!
# Recognition in the local transvection branch

The complete critical-line sieve leaves transvections on one of the two
faithful sections. Intrinsic S₈ involution geometry identifies each of these
as a transposition. Sign then proves rank one, and the quadratic-family bound
gives fixed codimension one on both sections, as in 13.8.23(1).

The centers of the transpositions construct an equivariant augmentation map
whose image is exactly [W,K]. Its kernel is zero or the constant line, giving
the augmentation or natural module with its actual inclusion in W. Finally
one coordinate change simultaneously marks the actor, alternating component,
natural quotient and commutator submodule. No constituent classification,
extension splitting or specialized section-model hypothesis is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.22–25,
printed pp.957–960, especially p.960 (PDF p.977); the augmentation core is B.3.1.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open Representation.BinaryOffender Subgroup BinaryPermutation
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- An elementary actor consisting of transvections in a faithful S₈-module
has rank one: every nonidentity element is a swap and sign is injective. -/
theorem rank_one_of_faithful_transvections
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (eH : H ≃* Perm) {A : Subgroup H} (hA : IsElementaryTwo A)
    (ht : ∀ a ∈ A, a ≠ 1 → fixedCodim ρ (zpowers a) = 1) : rank A = 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  apply rank_one_of_nonidentity_odd eH.toMonoidHom hA
  intro a ha hn
  exact (Representation.SymmetricEightTransvections.isSwap_of_fixedCodim_eq_one
    ρ hρ eH a hn (elemPow_eq_one_of_isElementaryAbelian a ha) (ht a ha hn)).sign_eq

/-- The two local strong-offender exclusions force rank one in either
critical-line position. The quadratic-family bound then gives the fixed
codimensions and fixed-vector lifting of 13.8.23(1). -/
theorem rank_one_and_fixed_sections
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    {A : Subgroup H} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D : Submodule (ZMod 2) U)
    (hcritical : D ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) U,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hnoW : ¬ ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hnoQ : ¬ ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B) :
    rank A = 1 ∧ fixedCodim W.toRepresentation A = 1 ∧
      fixedCodim W.quotientRepresentation A = 1 ∧ fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A := by
  obtain ⟨_, _, _, hline⟩ :=
    local_transvection_alternatives ρ W D hW hQ hA hcritical hdim hnoW hnoQ
  have hr : rank A = 1 := by
    rcases hline with h | h
    · exact rank_one_of_faithful_transvections W.toRepresentation hW eH hA h.2.2.2.2
    · exact rank_one_of_faithful_transvections W.quotientRepresentation hQ eH hA h.2.2.2.2
  obtain ⟨hw, hq, hu⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA.1 (by omega)
  exact ⟨hr, hw, hq, hu,
    fixedSpace_quotient_eq_map_of_fixedCodim_eq ρ W A (by omega)⟩

private theorem exists_core_map_of_rank_one
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (eH : H ≃* Perm) (K A : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hA : IsElementaryTwo A) (hr : rank A = 1) (hc : fixedCodim ρ A = 1) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] U,
      (∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v)) ∧
      LinearMap.range f = subspaceCommutator ρ ⊤ K := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, hn⟩ := A.nontrivial_iff_exists_ne_one.mp (A.nontrivial_iff_ne_bot.mpr hA.1)
  have hp : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hz : zpowers a = A := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr ha)
    rw [Nat.card_zpowers, orderOf_eq_prime hp hn, hA.card_eq_two_pow_rank, hr, pow_one]
  have hca : fixedCodim ρ (zpowers a) = 1 := by rwa [hz]
  have hs := Representation.SymmetricEightTransvections.isSwap_of_fixedCodim_eq_one
    ρ hρ eH a hn hp hca
  exact TransvectionCoreMap.exists_core_map_of_transposition ρ hρ eH K hK a hs hca

/-- Complete section recognition under the two local exclusions. The natural
quotient is the earlier chosen witness; the submodule model, rank one and
common transposition marking are all constructed here. -/
theorem compatible_sections_of_local_exclusions
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (K : Subgroup H) (eH : H ≃* Perm)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hmodelQ : IsEightNatural W.quotientRepresentation eH)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    {A : Subgroup H} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D : Submodule (ZMod 2) U)
    (hcritical : D ≤ fixedSpace ρ A ∨ ∃ S : Submodule (ZMod 2) U,
      IsAtom S ∧ ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hnoW : ¬ ∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hnoQ : ¬ ∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B) :
    rank A = 1 ∧ fixedCodim W.toRepresentation A = 1 ∧
      fixedCodim W.quotientRepresentation A = 1 ∧ fixedCodim ρ A = 2 ∧
      (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A ∧
      ∃ g : Perm, ∃ J : Subrepresentation W.toRepresentation,
        A.map (conjugateMarking eH g).toMonoidHom = transpositionGroup ∧
        K.map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) ∧
        IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
        J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ K ∧
        IsEightNaturalOrCover J.toRepresentation (conjugateMarking eH g) := by
  obtain ⟨hr, hw, hq, hu, hfix⟩ :=
    rank_one_and_fixed_sections ρ W eH hW hQ hA hbound D hcritical hdim hnoW hnoQ
  obtain ⟨f, heq, hrange⟩ := exists_core_map_of_rank_one
    W.toRepresentation hW eH K A hK hA hr hw
  have hJ := commutator_model_of_core_map W.toRepresentation K eH f heq hrange hKW
  obtain ⟨_, g, hg, _⟩ :=
    codim_one_actor_marking W.quotientRepresentation eH (Or.inl hmodelQ) A hA hq
  obtain ⟨J, hJcomm, hJmodel⟩ := commutator_model_conjugate W.toRepresentation K eH hJ g
  exact ⟨hr, hw, hq, hu, hfix, g, J, hg, alternating_marking_conjugate eH K hK g,
    IsEightNatural.conjugate W.quotientRepresentation eH hmodelQ g, hJcomm, hJmodel⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
