module
public import CFSG.Quasithin.Chapter10.SourceA5PairedBaumann
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumannDisplacement

/-!
# The original A5 Baumann-center displacement geometry

The original Fundamental Setup, its actual A5 quotient and the escaping
Baumann normalizer produce the marked paired-five action. Applying the
paired displacement theorem to this same local module gives the two actual
residual factors and their center lines on E = Omega1(Z(Baum(T))). Every
original factor actor has displacement in its specified line. An actor
outside Baum(T) realizes the nonzero center.

This is the fixed-plane step of Aschbacher–Smith 10.2.1, printed p.743,
using E.2.3(3). Selection of the factor actors and identification of these
residual factors with the original component pair are separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The exact two residual-factor lines on the original local Baumann center. -/
@[expose] def SourcePairedBaumannDisplacement : Prop :=
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let E := omegaOneCenterAmbient (ChapterB.baumann (S : Subgroup H))
  letI := offenderSubgroup_normal α
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ _c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
      ∃ v₁ v₂ : H,
        v₁ ∈ ⁅U,factorResidual q Y d.first⁆ ∧ v₁ ≠ 1 ∧
        v₂ ∈ ⁅U,factorResidual q Y d.second⁆ ∧ v₂ ≠ 1 ∧
        (∀ g ∈ (S : Subgroup H) ⊓ factorResidual q Y d.first,
          ∀ x ∈ E, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₁) ∧
        (∀ g ∈ (S : Subgroup H) ⊓ factorResidual q Y d.second,
          ∀ x ∈ E, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₂) ∧
        (∀ g ∈ (S : Subgroup H) ⊓ factorResidual q Y d.first,
          g ∉ ChapterB.baumann (S : Subgroup H) → ∃ x∈E, ⁅g,x⁆=v₁) ∧
        (∀ g ∈ (S : Subgroup H) ⊓ factorResidual q Y d.second,
          g ∉ ChapterB.baumann (S : Subgroup H) → ∃ x∈E, ⁅g,x⁆=v₂)

omit [Finite G] in
/-- The local elementary group is exactly the original ambient Baumann center. -/
theorem source_local_baumann_center_map :
    (omegaOneCenterAmbient (ChapterB.baumann
      ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) :
        Subgroup (localJoin T L)))).map (localJoin T L).subtype =
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) := by
  rw [←omegaOneCenterAmbient_map_injective _ (localJoin T L).subtype_injective]
  have hb := Stellmacher.baumann_map_injective (localJoin T L).subtype
    (localJoin T L).subtype_injective
    ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) :
      Subgroup (localJoin T L))
  change (ChapterB.baumann _).map _ = ChapterB.baumann _ at hb
  rw [hb]
  exact congrArg (fun S => omegaOneCenterAmbient (ChapterB.baumann S))
    (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ localJoin T L from le_sup_right))

/-- No action or coordinate hypotheses are added to the original A5 input. -/
theorem source_a5_baumann_center_displacement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourcePairedBaumannDisplacement D := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  obtain ⟨d,t,ht₁,ht₂,⟨c⟩⟩ := source_a5_paired_five_action D e hn hout
  obtain ⟨v₁,v₂,hv₁,hv₁ne,hv₂,hv₂ne,h₁,h₂⟩ :=
    paired_symmetric_baumann_center_displacement S (source_a5_minimal_parabolic D e hn)
      U hU (source_local_thompson_not_centralizes D hout) q hq hk d c ⟨t,ht₁,ht₂⟩
  refine ⟨d,c,⟨t,ht₁,ht₂⟩,v₁,v₂,hv₁,hv₁ne,hv₂,hv₂ne,h₁,h₂,?_,?_⟩
  · intro g hg hgout
    obtain ⟨x,hx,hgx⟩ := exists_baumann_center_commutator_ne_one (S : Subgroup H) hg.1 hgout
    exact ⟨x,hx,(h₁ g hg x hx).resolve_left hgx⟩
  · intro g hg hgout
    obtain ⟨x,hx,hgx⟩ := exists_baumann_center_commutator_ne_one (S : Subgroup H) hg.1 hgout
    exact ⟨x,hx,(h₂ g hg x hx).resolve_left hgx⟩

end CFSG.Quasithin.Chapter10
