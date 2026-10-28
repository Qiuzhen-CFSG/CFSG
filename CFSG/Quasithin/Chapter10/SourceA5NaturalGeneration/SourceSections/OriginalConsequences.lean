module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalSelection
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CommonBaumann
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceMovement.OriginalSetup
/-!
# Original natural-source consequences with Thompson movement discharged

The actual HStar noncentral omega commutator supplies Thompson movement.
The selected original paired linear source then gives the original seed
containment, local class, and common Baumann embedding, without independent
classification, marking, movement, or exchange premises.
Source: Aschbacher–Smith 10.2.2(1) and 10.2.3(4), pp.744 and 746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_hstar_local_thompson_moves_of_omega_commutator
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  intro hc
  apply source_hstar_thompson_moves_of_omega_commutator D hH hZH
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le le_sup_right)
  rw [← hjmap]
  rintro g ⟨j,hj,rfl⟩ z hz
  exact congrArg X.subtype (hc hj
    ⟨z,(D.module_le_core.trans (pCoreIn_le 2 X)) hz⟩ hz)

variable {F : Type*} [Field F] [CharP F 2]
local instance originalConsequencesFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

include e hn hH hZH hF f n

theorem source_original_paired_linear_of_hstar_natural_four : SourceOriginalPairedLinear D :=
  source_original_paired_linear_of_natural_four D e hn
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) hF f n

theorem source_original_seed_le_moved_sup_central_alpha_of_hstar_natural_four :
    omegaOneCenterAmbient (T : Subgroup G) ≤
      ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)) := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  exact source_original_seed_le_moved_sup_central_alpha_of_paired_linear D e hn
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) d K c hexchange

theorem source_original_component_localClass_of_hstar_natural_four :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    let A := L.subgroupOf X
    let B := baumann (S : Subgroup X)
    U ≤ normalizer (A : Set X) ∧ B ≤ normalizer (A : Set X) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ A ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ A ⊔ B from le_sup_right))).map
        (A ⊔ B).subtype = ⁅U,A⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (A : Set X)) := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  exact source_original_component_localClass_of_paired_linear D e hn
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) d K c hexchange

theorem source_original_common_baumann_embedding_of_hstar_natural_four :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let N := L.subgroupOf X ⊔ baumann (S : Subgroup X)
    ∃ b : baumann (T : Subgroup G) →* N,
      ChapterC.GlaubermanNiles.InLocalClass b ∧
      (X.subtype.comp N.subtype).comp b = (baumann (T : Subgroup G)).subtype := by
  obtain ⟨d,K,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  exact source_original_common_baumann_embedding_of_paired_linear D e hn
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH) d K c hexchange
end CFSG.Quasithin.Chapter10
