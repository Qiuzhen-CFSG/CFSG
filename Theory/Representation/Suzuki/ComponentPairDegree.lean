module
public import Theory.Representation.BinaryOffender.FaithfulComponentPair
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction

/-!
# Degree bounds for fully moving Suzuki component pairs

Every nonzero submodule of a fully moving centerless pair is faithful. Its
Suzuki restriction is semisimple, and the commuting perfect factor prevents
that restriction from being irreducible. An irreducible summand and its
nonzero invariant complement are both faithful for the simple Suzuki factor.
The proved minimum binary degree therefore gives twice that minimum on every
nonzero pair submodule, with no assumption on the exchanger's action on an
individual constituent.

The exchanged-pair theorem derives all fixed-space, center and semisimplicity
hypotheses from the literal component and its normalizer of index two.
Source: Aschbacher--Smith D.3.7, printed pp.197--198; the minimum Suzuki degree
uses the primitive-prime argument in `Suzuki.BinaryDegree`.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.Suzuki
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every nonzero module in a fully moving centerless component pair has at
least twice the minimum faithful degree of its Suzuki factor. -/
theorem pair_subrepresentation_finrank_ge
    (ρ : Representation (ZMod 2) G V)
    (J K : Subgroup G) (hJ : IsComponent G J) (hK : IsComponent G K)
    (hne : J ≠ K) (hZJ : center J = ⊥) (hZK : center K = ⊥)
    (hfixJ : fixedSpace ρ J = ⊥) (hfixK : fixedSpace ρ K = ⊥)
    [IsSemisimpleModule (ZMod 2)[J] (Representation.asModule (ρ.comp J.subtype))]
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (U : Subrepresentation (ρ.comp (J ⊔ K).subtype)) (hU : U ≠ ⊥) :
    8 * (2*r+1) ≤ Module.finrank (ZMod 2) U.toSubmodule := by
  let X := J ⊔ K
  let P := J.subgroupOf X
  let Q := K.subgroupOf X
  let eP : P ≃* J := subgroupOfEquivOfLe (show J ≤ X from le_sup_left)
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup P := (eP.trans e).isSimpleGroup
  let : IsQuasisimple Q := (hK.subgroupOf (show K ≤ X from le_sup_right)).2
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h => hU (Subrepresentation.toSubmodule_injective h))
  let τ : Representation (ZMod 2) X V := ρ.comp X.subtype
  let : IsSemisimpleModule (ZMod 2)[P] (Representation.asModule (τ.comp P.subtype)) :=
    comp_semisimple_of_surjective (ρ.comp J.subtype) eP.toMonoidHom eP.surjective
  let f : IntertwiningMap (U.toRepresentation.comp P.subtype) (τ.comp P.subtype) := {
    toLinearMap := U.toSubmodule.subtype
    isIntertwining' _ := rfl }
  let : IsSemisimpleModule (ZMod 2)[P]
      (Representation.asModule (U.toRepresentation.comp P.subtype)) :=
    IsSemisimpleModule.of_injective (IntertwiningMap.equivLinearMapAsModule _ _ f)
      Subtype.val_injective
  have hfix : invariants (U.toRepresentation.comp P.subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    apply hfixJ.le
    intro j
    exact congrArg Subtype.val (hv (eP.symm j))
  have hc : Q ≤ centralizer (P : Set X) := by
    intro k hk j hj
    exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp
      (hK.commutator_eq_bot_of_ne hJ hne.symm) hk j.val hj)
  have hf := pair_subrepresentation_faithful ρ J K hJ hK hne hZJ hZK hfixJ hfixK U hU
  have hb := two_mul_le_finrank_of_commuting_perfect U.toRepresentation hf P Q hc
    (4*(2*r+1)) (fun S hS => finrank_ge (by omega : 1 ≤ r)
      (S.toRepresentation.comp (eP.trans e).symm.toMonoidHom)
      ((simple_subrepresentation_faithful_of_fixed_eq_bot _ hfix S hS).comp
        (eP.trans e).symm.injective))
  omega

/-- Full movement by an exchanged Suzuki component gives the degree bound on
 every nonzero invariant submodule of its literal pair. -/
theorem exchanged_pair_subrepresentation_finrank_ge
    (ρ : Representation (ZMod 2) G V) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G))
    (hm : subspaceCommutator ρ ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (U : Subrepresentation (ρ.comp (J ⊔ J.map (MulAut.conj a).toMonoidHom).subtype))
    (hU : U ≠ ⊥) : 8 * (2*r+1) ≤ Module.finrank (ZMod 2) U.toSubmodule := by
  let K := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ K
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hindex a han
  have hK : IsComponent G K := hJ.map_conj a
  have hne : J ≠ K := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : K ≤ centralizer (J : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hJ hne.symm)
  let : IsSemisimpleModule (ZMod 2)[J] (Representation.asModule (ρ.comp J.subtype)) :=
    irreducible_restriction_semisimple_of_normal_chain ρ hi J X le_sup_left
      (sup_le J.le_normalizer (hc.trans (centralizer_le_normalizer _)))
  have hfixJ := full_component_pair_fixed_eq_bot ρ hi J hJ hindex a han hm
  have hfixK : fixedSpace ρ K = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [←(fixedSpaceConjEquiv ρ J a).finrank_eq,hfixJ,finrank_bot]
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup J := e.isSimpleGroup
  let : IsQuasisimple J := hJ.2
  let : IsSimpleGroup K := (((MulAut.conj a).subgroupMap J).symm.trans e).isSimpleGroup
  let : IsQuasisimple K := hK.2
  have hZJ : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h))
  have hZK : center K = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h))
  exact pair_subrepresentation_finrank_ge ρ J K hJ hK hne hZJ hZK hfixJ hfixK r hr e U hU
end Representation.Suzuki
