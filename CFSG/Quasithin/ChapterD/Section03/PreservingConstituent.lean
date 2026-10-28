module
public import CFSG.Quasithin.ChapterD.Section03.ConstituentDrop
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.TwoCopies
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryIrreducibleCentralizer

/-!
# Constituent descent for a pair inside its ambient actor

An irreducible commuting pair makes each factor restriction isotypic. This
remains true when the pair sits in a larger group containing outer actors:
we first prove isotypy inside the pair, then transport the actual constituent
through the subgroup equivalence. The existing odd-copy selection and strict
ratio descent apply to the original elementary actor.

A nontrivial elementary actor moves at least one factor by binary Schur's
lemma. The odd-prime square exclusion is the consumer.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, using A.1.42 and D.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Strict constituent descent remains valid when the irreducible commuting
pair lies in a larger actor group. In particular, outer actors are retained. -/
theorem exists_constituent_drop_of_irreducible_pair
    (ρ : Representation (ZMod 2) G V) (L K : Subgroup G) [L.Normal]
    [IsQuasisimple L] [Group.IsPerfect K] [Nontrivial K]
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype)) (hf : Function.Injective ρ)
    (hK : K ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hmove : ¬ A ≤ centralizer (L : Set G)) :
    ∃ U : Subrepresentation (ρ.comp L.subtype), U.toRepresentation.IsIrreducible ∧
      A ≤ subspaceStabilizer ρ U.toSubmodule ∧
      restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
      actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
        (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ := by
  let N := L ⊔ K
  let J := L.subgroupOf N
  let C := K.subgroupOf N
  let e : L ≃* J := (subgroupOfEquivOfLe (show L ≤ N from le_sup_left)).symm
  let σ : Representation (ZMod 2) N V := ρ.comp N.subtype
  let : σ.IsIrreducible := hi
  let : IsIrreducible ρ := irreducible_of_subgroup_restriction ρ N hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  let := NormalConstituentDisplacement.restriction_semisimple σ hi J
  have hc : C ≤ centralizer (J : Set N) := by
    intro k hk j hj
    exact Subtype.ext (hK hk j.val hj)
  have hs : J ⊔ centralizer (J : Set N) = ⊤ := by
    apply top_unique
    rw [←(codisjoint_subgroupOf_sup L K).eq_top]
    exact sup_le_sup_left hc J
  let τ : Representation (ZMod 2) J V := σ.comp J.subtype
  let : Nontrivial τ.asModule := τ.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨S,hS⟩ := IsSemisimpleModule.exists_simple_submodule (ZMod 2)[J] τ.asModule
  let I := Subrepresentation.ofSubmodule' S
  have hI : I.toRepresentation.IsIrreducible := by
    rw [Subrepresentation.irreducible_iff_isAtom]
    exact Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff I |>.mp
      (isSimpleModule_iff_isAtom.mp hS)
  have ht : (normalTypeAction σ J).inertia I = ⊤ := by
    apply top_unique
    rw [←hs]
    exact sup_le (normal_le_typeInertia σ J I) (centralizer_le_typeInertia σ J I)
  have htype := isotypic_comp_equiv τ e I
    (restriction_isotypic_of_typeInertia_top σ J I hI ht)
  let := NormalConstituentDisplacement.restriction_semisimple ρ inferInstance L
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hLn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  have hgen : ⁅L,A⁆ = L :=
    IsComponent.commutator_eq_self_of_normalizes
      (show IsComponent G L from ⟨(inferInstance : L.Normal).isSubnormal,inferInstance⟩)
      (by rw [normalizer_eq_top]; exact le_top) (by
        intro he
        exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
  exact exists_constituent_ratio_strict_drop ρ L htype
    (not_irreducible_of_faithful_commuting_perfect ρ hf L K hK)
    (subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf inferInstance L hLn)
    (fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance L hLn)
    A hA hgen
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A nontrivial elementary actor moves at least one member of an irreducible
commuting pair, even when it induces outer automorphisms. -/
theorem pair_actor_moves_factor
    (ρ : Representation (ZMod 2) G V) (L K : Subgroup G)
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype)) (hf : Function.Injective ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    ¬ A ≤ centralizer (L : Set G) ∨ ¬ A ≤ centralizer (K : Set G) := by
  let := hi
  let : IsElementaryAbelian 2 A := hA.2
  by_contra! hn
  apply hA.1
  apply bot_unique
  intro a ha
  apply mem_bot.mpr
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ (L ⊔ K) hf
    (elemPow_eq_one_of_isElementaryAbelian a ha)
  exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hn.1)
    (le_centralizer_iff.mp hn.2)) ha
end CFSG.Quasithin.ChapterD
