module
public import Theory.Representation.Suzuki.ExchangedDisplacement
public import Theory.Representation.BinaryOffender.RestrictedConstituent
public import Theory.Representation.BinaryOffender.RatioInheritance

/-!
# Stable constituents of the exchanged Suzuki fixed-space action

Put X = J J^a and C = C_A(X). The nonzero C-fixed space is X-invariant.
Every nonzero X-submodule is faithful and has binary degree at least
8(2r+1). A reduced actor of codimension at most 4r+4 therefore preserves
every irreducible X-constituent inside this fixed space: a distinct translate
would already exceed that entire displacement budget.

Choose such a constituent. Faithfulness of X identifies the pointwise actor
kernel with C, on both the constituent and the original fixed space.
The two actual actor images consequently have the same rank; restriction
can only decrease their action ratio. No constituent is assumed to be fixed
by the exchanger. The literal Chapter 10 application constructs all inputs
from the original natural Hall context.
Source: Aschbacher--Smith D.2.7, D.3.7--9, printed pp.179--180,197--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.Suzuki
open scoped MonoidAlgebra
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual centralizer fixed space contains a faithful irreducible pair
constituent preserved by every actor, with exactly the same actor kernel,
rank, and no greater action ratio. -/
theorem exchanged_fixedSpace_constituent
    (ρ : Representation (ZMod 2) G V) (hi : ρ.IsIrreducible)
    (J : Subgroup G) (hJ : IsComponent G J)
    (hindex : (normalizer (J : Set G)).index = 2)
    (a : G) (han : a ∉ normalizer (J : Set G))
    (hm : subspaceCommutator ρ ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hXA : ⁅J ⊔ J.map (MulAut.conj a).toMonoidHom, A⁆ =
      J ⊔ J.map (MulAut.conj a).toMonoidHom)
    (hsmall :
      let C := A ⊓ centralizer ((J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G)
      fixedCodim (subspaceImageRepresentation ρ (fixedSpace ρ C))
        (restrictedSubgroup ρ (fixedSpace ρ C) A) ≤ 2 * (2*r+2)) :
    let X := J ⊔ J.map (MulAut.conj a).toMonoidHom
    let C := A ⊓ centralizer (X : Set G)
    ∃ U : Subrepresentation (ρ.comp X.subtype),
      U.toRepresentation.IsIrreducible ∧
      U.toSubmodule ≤ fixedSpace ρ C ∧
      A ≤ subspaceStabilizer ρ U.toSubmodule ∧
      Function.Injective U.toRepresentation ∧
      subspaceKernel ρ U.toSubmodule A = C ∧
      subspaceKernel ρ (fixedSpace ρ C) A = C ∧
      rank (restrictedSubgroup ρ U.toSubmodule A) =
        rank (restrictedSubgroup ρ (fixedSpace ρ C) A) ∧
      actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
          (restrictedSubgroup ρ U.toSubmodule A) ≤
        actionRatio (subspaceImageRepresentation ρ (fixedSpace ρ C))
          (restrictedSubgroup ρ (fixedSpace ρ C) A) ∧
      8 * (2*r+1) ≤ Module.finrank (ZMod 2) U.toSubmodule := by
  let K := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ K
  let C := A ⊓ centralizer (X : Set G)
  let W := fixedSpace ρ C
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hindex a han
  let : ρ.IsIrreducible := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ A from inf_le_left)) (inclusion_injective _)
  have hfixJ := full_component_pair_fixed_eq_bot ρ hi J hJ hindex a han hm
  have hfixK : fixedSpace ρ K = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [← (fixedSpaceConjEquiv ρ J a).finrank_eq, hfixJ, finrank_bot]
  have hfixX : fixedSpace ρ X = ⊥ := bot_unique
    ((fixedSpace_antitone ρ (show J ≤ X from le_sup_left)).trans hfixJ.le)
  have hXC : X ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (show C ≤ centralizer (X : Set G) from inf_le_right)
  have hXW := centralizer_le_fixedSpace_stabilizer ρ C X hXC
  have hAW : A ≤ subspaceStabilizer ρ W := fixedSpace_subactor_stabilized ρ hA inf_le_left
  have hmove := fixedSpace_moved_of_commutator_eq ρ X A C
    (IsElementaryAbelian.isPGroup 2 C) hXC hfixX hXA
  let R := invariantSubspace ρ X W hXW
  have hRb : R ≠ ⊥ := by
    intro he
    have hz : W = ⊥ := congrArg Subrepresentation.toSubmodule he
    exact hmove ((subspaceCommutator_eq_bot_iff ρ W A).mpr (hz ▸ bot_le))
  obtain ⟨U, hUa, hUR⟩ := (eq_bot_or_exists_atom_le R).resolve_left hRb
  have hU := (Subrepresentation.irreducible_iff_isAtom U).mpr hUa
  have hUW : U.toSubmodule ≤ W := hUR
  have hdeg := exchanged_pair_subrepresentation_finrank_ge ρ hi J hJ hindex a han hm r hr e U hUa.ne_bot
  have hsmall' : fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) <
      Module.finrank (ZMod 2) U.toSubmodule := by
    change fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ≤ 2 * (2*r+2) at hsmall
    omega
  have hUA : A ≤ subspaceStabilizer ρ U.toSubmodule := by
    apply le_subspaceStabilizer
    intro b hb v hv
    rw [← map_constituent_eq_self_of_restricted_codim_lt ρ X A W hAW U hU hUW hsmall' b hb]
    exact Submodule.mem_map_of_mem hv
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup J := e.isSimpleGroup
  let : IsQuasisimple J := hJ.2
  let : IsSimpleGroup K := (((MulAut.conj a).subgroupMap J).symm.trans e).isSimpleGroup
  let : IsQuasisimple K := (hJ.map_conj a).2
  have hZJ : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h))
  have hZK : center K = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h))
  have hne : J ≠ K := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hf := pair_subrepresentation_faithful ρ J K hJ (hJ.map_conj a) hne
    hZJ hZK hfixJ hfixK U hUa.ne_bot
  have hXU : X ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun x hx v hv => U.apply_mem_toSubmodule ⟨x,hx⟩ hv)
  have hKU : subspaceKernel ρ U.toSubmodule A = C := by
    apply le_antisymm
    · exact subspaceKernel_le_centralizer_of_faithful ρ X A U.toSubmodule hXU hf
    · intro b hb
      exact ⟨hb.1, fun v hv => hUW hv ⟨b,hb⟩⟩
  have hKW : subspaceKernel ρ W A = C := by
    apply le_antisymm
    · intro b hb
      exact hKU ▸ (show b ∈ subspaceKernel ρ U.toSubmodule A from
        ⟨hb.1, fun v hv => hb.2 v (hUW hv)⟩)
    · intro b hb
      exact ⟨hb.1, fun v hv => hv ⟨b,hb⟩⟩
  have hru := rank_subspaceKernel_add_image ρ U.toSubmodule A hUA
    (IsElementaryAbelian.isPGroup 2 A)
  have hrw := rank_subspaceKernel_add_image ρ W A hAW
    (IsElementaryAbelian.isPGroup 2 A)
  rw [hKU] at hru
  rw [hKW] at hrw
  have hrank : rank (restrictedSubgroup ρ U.toSubmodule A) = rank (restrictedSubgroup ρ W A) := by omega
  have hcodim : fixedCodim (subspaceImageRepresentation ρ U.toSubmodule)
      (restrictedSubgroup ρ U.toSubmodule A) ≤
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
    rw [fixedCodim_restrictedSubgroup ρ U.toSubmodule A hUA,
      fixedCodim_restrictedSubgroup ρ W A hAW]
    have hu := U.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
    have hw := W.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
    have hle := Submodule.finrank_mono (sup_le_sup_right hUW (fixedSpace ρ A))
    omega
  refine ⟨U,hU,hUW,hUA,hf,hKU,hKW,hrank,?_,hdeg⟩
  simp only [actionRatio, hrank]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcodim) _

end Representation.Suzuki
