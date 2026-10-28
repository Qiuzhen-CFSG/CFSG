module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Projections
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.SubspaceQuotient

/-!
# Nontrivial component action on V/C_V(C_A(L))

The actual projections place B=C_A(L) inside the second component M.
If B is nontrivial, centerlessness and component normality imply [M,B]=M.
A subspace preserved by M and fixed by B is fixed by [M,B], so the given
mixed action [[V,L],M] is also nonzero with B in place of M. Consequently
the original L-action on the literal quotient V/C_V(B) is nontrivial.

The final application obtains B≠1 from the first strict rank comparison;
that rank comparison remains an explicit input to be supplied by the chief
factor estimates. No quotient dimension or factor count is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the deductions between (!) and (!!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem SecondComponent.commutator_centralizer_eq {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L)
    [d.second.Normal] (hb : A ⊓ centralizer (L : Set G) ≠ ⊥) :
    ⁅d.second, A ⊓ centralizer (L : Set G)⁆ = d.second := by
  let B := A ⊓ centralizer (L : Set G)
  have hBM : B ≤ d.second :=
    ((d.projections ρ sL hL).centralizer_le_rightImage
      (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))
      (seed_center_eq_bot ρ sL)).trans (d.projections ρ sL hL).rightImage_le
  rcases d.isComponent.commutator_dichotomy B with hz | he
  · exfalso
    apply hb
    apply bot_unique
    intro b hb'
    have hc : B ≤ centralizer (d.second : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hcenter : (⟨b, hBM hb'⟩ : d.second) ∈ center d.second := by
      apply mem_center_iff.mpr
      intro m
      exact Subtype.ext (hc hb' m m.property)
    have heq : (⟨b, hBM hb'⟩ : d.second) = 1 := by
      simpa only [seed_center_eq_bot ρ d.seed, mem_bot] using hcenter
    exact congrArg Subtype.val heq
  · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq,
      iSup_const] using he

theorem SecondComponent.cross_centralizer_ne_bot {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L)
    [d.second.Normal] (hb : A ⊓ centralizer (L : Set G) ≠ ⊥) :
    subspaceCommutator ρ (moved ρ L) (A ⊓ centralizer (L : Set G)) ≠ ⊥ := by
  intro hz
  apply d.cross_action
  apply (subspaceCommutator_eq_bot_iff ρ _ _).mpr
  rw [← d.commutator_centralizer_eq ρ sL hL hb]
  apply le_fixedSpace_commutator_of_invariant ρ
  · apply subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
    exact (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))).trans (centralizer_le_normalizer _)
  · exact (subspaceCommutator_eq_bot_iff ρ _ _).mp hz

/-- The literal B-fixed space, invariant for L since L centralizes B. -/
noncomputable def offenderCentralizerFixed (A L : Subgroup G) :
    Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := fixedSpace ρ (A ⊓ centralizer (L : Set G))
  apply_mem_toSubmodule l v hv := by
    have hn : L ≤ normalizer (A ⊓ centralizer (L : Set G) : Set G) :=
      (le_centralizer_iff.mp (show A ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G)
        from inf_le_right)).trans (centralizer_le_normalizer _)
    exact (fixedSpace_invariant_normalizer ρ hn l.property v).2 hv

theorem SecondComponent.centralizerQuotient_nontrivial {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L)
    [d.second.Normal] (hb : A ⊓ centralizer (L : Set G) ≠ ⊥) :
    (offenderCentralizerFixed ρ A L).quotientRepresentation ≠ 1 := by
  intro htriv
  apply d.cross_centralizer_ne_bot ρ sL hL hb
  apply (subspaceCommutator_eq_bot_iff ρ _ _).mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, _, rfl⟩
  let C := offenderCentralizerFixed ρ A L
  apply (Submodule.Quotient.mk_eq_zero C.toSubmodule).mp
  change C.toSubmodule.mkQ (ρ l v - v) = 0
  rw [map_sub]
  have he := DFunLike.congr_fun (DFunLike.congr_fun htriv (⟨l, hl⟩ : L))
    (C.toSubmodule.mkQ v)
  change C.toSubmodule.mkQ (ρ l v) = C.toSubmodule.mkQ v at he
  exact sub_eq_zero.mpr he

theorem SecondComponent.centralizerQuotient_nontrivial_of_rank_gt [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L)
    (hgt : 2 * sL.field.degree < rank A) :
    (offenderCentralizerFixed ρ A L).quotientRepresentation ≠ 1 := by
  let : d.second.Normal := setup.component_normal d.second d.isComponent
  exact d.centralizerQuotient_nontrivial ρ sL hL
    (d.centralizer_ne_bot_of_rank_gt ρ sL hL setup.minimal.1.1 hgt)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
