module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.CentralFactors
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# The additive fixed-codimension inequality in B.5.9

For elementary A, the subgroup B=C_A(L) centralizes LA and lies in its
literal two-core. Hence the original seed U=[C_V(O₂(LA)),L] lies in C_V(B).
Dimension additivity for U+C_V(A) inside C_V(B) proves the middle inequality
of (!!), retaining the actual LA-action on U and the original fixed spaces.
No splitting of the module or equality U=C_V(B) is used.

This establishes only the additive inequality. The numerical bounds 3m and
m on its two summands still require the representation estimates.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, inequality (!!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem centralizer_le_localTwoCore {A L : Subgroup G} (hA : IsElementaryAbelian 2 A) :
    A ⊓ centralizer (L : Set G) ≤ localTwoCore L A := by
  let : IsElementaryAbelian 2 A := hA
  apply le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left)
    (inf_le_left.trans le_sup_right)
  apply le_trans _ (centralizer_le_normalizer _)
  apply sup_le
  · exact le_centralizer_iff.mp inf_le_right
  · exact (Subgroup.le_centralizer (H := A)).trans (centralizer_le inf_le_left)

theorem seed_le_centralizerFixed {A L : Subgroup G} (seed : NaturalSeed ρ A L)
    (hA : IsElementaryAbelian 2 A) :
    seed.space.toSubmodule ≤ fixedSpace ρ (A ⊓ centralizer (L : Set G)) := by
  rw [seed.space_eq]
  apply le_trans _ (fixedSpace_antitone ρ (centralizer_le_localTwoCore hA))
  apply subspaceCommutator_le_of_invariant ρ
  apply le_subspaceStabilizer
  intro l hl v hv
  exact (coreFixedSpace ρ A L).apply_mem_toSubmodule ⟨l, hl⟩ hv

private theorem fixedCodim_add_subspace_le [Module.Finite (ZMod 2) V]
    (U : Subrepresentation ρ) {A B : Subgroup G} (hBA : B ≤ A)
    (hU : U.toSubmodule ≤ fixedSpace ρ B) :
    fixedCodim ρ B + fixedCodim U.toRepresentation A ≤ fixedCodim ρ A := by
  have hs : U.toSubmodule ⊔ fixedSpace ρ A ≤ fixedSpace ρ B :=
    sup_le hU (fixedSpace_antitone ρ hBA)
  have hdim := Submodule.finrank_mono hs
  have hsum := U.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  have hfix := (subrepresentationFixedEquiv ρ U A).finrank_eq
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  have hUdim := fixedCodim_add_finrank U.toRepresentation A
  omega

theorem seed_additive_bound [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (seed : NaturalSeed ρ A L) (hA : IsElementaryAbelian 2 A) :
    fixedCodim ρ (A ⊓ centralizer (L : Set G)) +
      fixedCodim seed.space.toRepresentation (A.subgroupOf (L ⊔ A)) ≤ fixedCodim ρ A := by
  have h := fixedCodim_add_subspace_le (ρ.comp (L ⊔ A).subtype) seed.space
    (A := A.subgroupOf (L ⊔ A))
    (B := (A ⊓ centralizer (L : Set G)).subgroupOf (L ⊔ A))
    (Subgroup.subgroupOf_mono _ inf_le_left) (by
      rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_right)]
      exact seed_le_centralizerFixed ρ seed hA)
  rwa [fixedCodim_subgroupOf ρ (inf_le_left.trans le_sup_right),
    fixedCodim_subgroupOf ρ le_sup_right] at h

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
