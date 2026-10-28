module

public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.CentralSectionAction


/-!
# Identifying a non-strong offender section with the full moved space

If W is L-invariant and A-invariant, V=W+C_V(A), and [L,A]=L, then A
acts trivially on V/W and so does L. For W in Irr+(L,V), this identifies
W with [V,L]. Minimal-best-offender restriction supplies the fixed-space
sum when its actual image on W is not strong. The resulting moved space
is invariant under the full normalizer of L, and its original central
quotient extends to that normalizer with the literal inclusion map.

Source: Aschbacher–Smith, B.1.5 and the ratio-one branches of B.6.9,
printed pp.69–70 and116–117 (1 March 2004). The non-strong premise must
come from the relevant representation family; it is not asserted for
natural SL3 modules, whose quadratic ratio is one half.
-/

public section

open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem subspaceCommutator_le_of_fixed_span
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hgen : ⁅L,A⁆ = L) (hW : L ≤ subspaceStabilizer ρ W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hs : W ⊔ fixedSpace ρ A = ⊤) :
    subspaceCommutator ρ ⊤ L ≤ W := by
  let H := L ⊔ A
  let I := invariantSubspace ρ H W (sup_le hW hAW)
  let σ := I.quotientRepresentation
  have hs' : I.toSubmodule ⊔ fixedSpace (ρ.comp H.subtype) (A.subgroupOf H) = ⊤ := by
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right)]
    exact hs
  have hAk : A.subgroupOf H ≤ σ.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    exact quotient_trivial_of_sup_fixedSpace (ρ.comp H.subtype) I _ hs' a ha v
  have hg : ⁅L.subgroupOf H, A.subgroupOf H⁆ = L.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),
      map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left), hgen]
  have hLk : L.subgroupOf H ≤ σ.ker := by
    rw [← hg]
    exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ _)
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hl,v,_,rfl⟩
  exact (Submodule.Quotient.eq W).mp
    (LinearMap.congr_fun (hLk (show (⟨l,(show L ≤ H from le_sup_left) hl⟩ : H) ∈ L.subgroupOf H from hl)) (W.mkQ v))

theorem IsIrrPlus.eq_moved_of_fixed_span
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hW : IsIrrPlus ρ L W) (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hs : W ⊔ fixedSpace ρ A = ⊤) : W = subspaceCommutator ρ ⊤ L := by
  apply le_antisymm
  · exact hW.choose_spec.1.ge.trans (subspaceCommutator_mono_left ρ le_top L)
  · exact subspaceCommutator_le_of_fixed_span ρ hgen hW.choose hAW hs

variable [Finite G] [FiniteDimensional (ZMod 2) V]

theorem IsMinimalBestOffender.irrPlus_eq_moved_of_non_strong
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    W = subspaceCommutator ρ ⊤ L := by
  have hn : ¬ W ≤ fixedSpace ρ A := by
    intro hf
    have hh := le_fixedSpace_commutator_of_invariant ρ hW.choose hf
    rw [hgen] at hh
    exact hW.not_le_fixedSpace ρ hh
  have hs := (hA.faithful_span_of_not_strong ρ W hAW hn hns).2
  exact hW.eq_moved_of_fixed_span ρ hAW hgen hs

theorem IsMinimalBestOffender.irrPlus_normalizer_stable_of_non_strong
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    normalizer (L : Set G) ≤ subspaceStabilizer ρ W := by
  rw [hA.irrPlus_eq_moved_of_non_strong ρ hW hAW hgen hns]
  exact subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_rfl

/-- The actual central quotient carries the normalizer action extending its original L-action. -/
theorem IsMinimalBestOffender.irrPlus_normalizer_extension_of_non_strong
    {L A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hA : IsMinimalBestOffender ρ A) (hW : IsIrrPlus ρ L W)
    (hAW : A ≤ subspaceStabilizer ρ W) (hgen : ⁅L,A⁆ = L)
    (hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    ∃ hN : normalizer (L : Set G) ≤ subspaceStabilizer ρ W,
      (centralSectionRepresentation ρ L (normalizer (L : Set G)) W hN le_rfl).comp
        (inclusion L.le_normalizer) = centralQuotientRepresentation ρ L W hW.choose := by
  refine ⟨hA.irrPlus_normalizer_stable_of_non_strong ρ hW hAW hgen hns, ?_⟩
  rfl

end Representation.BinaryOffender
