module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.Models
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore

/-!
# The five-point obstruction and its literal local core

The S₅ branch retains the marked offender family. Generation supplies the
whole S₅ marking, and the core of the actual local subgroup maps into the
core of its image. A commuting-transposition offender cannot lie in A₅.
The intrinsic five-point core calculation excludes this row whenever the
local subgroup contains a Sylow two-subgroup and a cubic element.

Source: Aschbacher–Smith, B.4.2(5), printed p.86, and the proof of 15.3.49,
printed p.1144 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection

/-- A commuting-transposition offender has an odd element. -/
theorem caseA_not_even {A : Subgroup (Equiv.Perm (Fin 5))}
    (hA : ChapterB.Offenders.CaseAFamily 5 A) : ¬ A ≤ alternatingGroup (Fin 5) := by
  obtain ⟨m, hm, _, g, rfl⟩ := hA
  intro h
  have hx := h (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (ChapterB.Offenders.pairSwap_mem (n := 5) (m := m) ⟨0, by decide⟩ (by change 0 < m; omega)))
  have hs := Equiv.Perm.mem_alternatingGroup.mp hx
  simp [MulAut.conj_apply, ChapterB.Offenders.pairSwap] at hs

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}

/-- Once the section is offender-generated, its marked S₅ model gives a
whole-actor equivalence without identifying the component with that actor. -/
noncomputable def fiveEquiv (hgen : offenderSubgroup ρ = ⊤)
    (mark : MarkedActionEquiv ρ (offenderSubgroup ρ) J
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    D ≃* Equiv.Perm (Fin 5) :=
  Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hgen.symm).trans mark.action.groupEquiv)

/-- The literal local core is incompatible with the five-point offender family. -/
theorem not_five_of_local_core [Finite D]
    (hgen : offenderSubgroup ρ = ⊤)
    {A B : Subgroup D} (hA : IsBestOffender ρ A) (hAB : A ≤ B.pCoreIn 2)
    (S : Sylow 2 D) (hSB : (S : Subgroup D) ≤ B) (hthree : 3 ∣ Nat.card B) :
    ¬ FiveCase ρ J := by
  rintro ⟨mark, ho, _⟩
  let e := fiveEquiv hgen mark
  have hmap : A.map e.toMonoidHom =
      (A.subgroupOf (offenderSubgroup ρ)).map mark.action.groupEquiv.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hgen.symm ▸ mem_top a⟩, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.val, ha, rfl⟩
  apply caseA_not_even (hmap.symm ▸ ho A hA)
  have hC := Theory.SpecificGroups.SymmetricFive.LocalTwoCore.core_le_alternating (B.map e.toMonoidHom) (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (by change (S : Subgroup D).map e.toMonoidHom ≤ B.map e.toMonoidHom
        exact map_mono hSB)
    (by rwa [← Nat.card_congr (B.equivMapOfInjective e.toMonoidHom e.injective).toEquiv])
  exact (map_mono hAB).trans
    ((Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le e.toMonoidHom B).trans hC)

/-- Intersection with a subgroup retains containment in the corresponding
relative two-core. No normality of the intersected subgroup is needed. -/
theorem core_restrict (B P : Subgroup D) :
    (B.pCoreIn 2).subgroupOf P ≤ (B.subgroupOf P).pCoreIn 2 := by
  have hn : B ≤ normalizer (B.pCoreIn 2 : Set D) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B).comap_subtype
    (comap_mono (pCoreIn_le 2 B))
  intro b hb x
  exact hn hb x.val

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection
