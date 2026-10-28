module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.GroupTheory.Gaschutz

/-!
# From the source parabolic complement to the actual split linear block

The complement in N_L(U) constructed on p.806 need only be local. Because
this parabolic contains the original Sylow T, its index in L is odd. Transport the
identity V=O₂(L) through L's inclusion and apply Gaschütz to the elementary
normal two-core. The result is a subgroup complement inside L itself.

The parabolic complement and the conclusions of 12.2.25 remain explicit
inputs. This file proves the final splitting implication, not their source
construction and not the unconditional local configuration theorem.
Source: Aschbacher--Smith, 12.2.26 and A.1.39, printed pp.806 and31.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The complement constructed in the actual parabolic N_L(U), before
Gaschütz promotes it to L. The original T is contained in that parabolic. -/
@[expose] def ParabolicSplitting (T : Sylow 2 G) (L V U : Subgroup G) : Prop :=
  ∃ hTL : (T : Subgroup G) ≤ L,
    (T.subtype hTL : Subgroup L) ≤ (normalizer (U : Set G)).subgroupOf L ∧
    ∃ S : Subgroup ((normalizer (U : Set G)).subgroupOf L),
      ((V.subgroupOf L).subgroupOf
        ((normalizer (U : Set G)).subgroupOf L)).IsComplement' S

theorem component_core_split_of_parabolic_split (D : ChosenModule T L V)
    {U : Subgroup G} (hcore : L.pCoreIn 2 = V)
    (hsplit : ParabolicSplitting T L V U) :
    ∃ S : Subgroup L, IsComplement' (pCore 2 L) S := by
  let := D.elementary
  have he : V.subgroupOf L = pCore 2 L := by
    rw [← hcore]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  let : IsElementaryAbelian 2 (V.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf D.le_component
  let : IsElementaryAbelian 2 (pCore 2 L) := he ▸ inferInstance
  obtain ⟨hTL, hTJ, S, hS⟩ := hsplit
  let P : Sylow 2 L := T.subtype hTL
  have hVP : pCore 2 L ≤ (P : Subgroup L) := pCore_isPGroup.le_sylow_of_normal P
  have hcop : (Nat.card (pCore 2 L)).Coprime
      ((normalizer (U : Set G)).subgroupOf L).index :=
    (P.card_coprime_index.coprime_dvd_left (card_dvd_of_le hVP)).coprime_dvd_right
      (index_dvd_of_le hTJ)
  exact exists_complement_of_coprime_overgroup (pCore 2 L)
    ((normalizer (U : Set G)).subgroupOf L) (hVP.trans hTJ) hcop ⟨S, he ▸ hS⟩

theorem splitLinearConfiguration_of_parabolic_split (D : ChosenModule T L V)
    {d : ℕ} {U : Subgroup G}
    (hrank : d = 3 ∨ d = 4) (hblock : ChapterC.IsLinearTwoBlock L d)
    (hnatural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d))
    (hself : normalizer (L : Set G) = L) (hcore : L.pCoreIn 2 = V)
    (hsplit : ParabolicSplitting T L V U) : SplitLinearConfiguration L V d :=
  ⟨hrank, hblock, hnatural, hself, hcore,
    component_core_split_of_parabolic_split D hcore hsplit⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
