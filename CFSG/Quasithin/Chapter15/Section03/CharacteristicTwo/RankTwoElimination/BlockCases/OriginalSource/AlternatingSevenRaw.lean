module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Ordinary A₇ offenders on the literal B.5 moved section

The offender inequality passes to an invariant subquotient. On a moved
section identified with the natural A₇ action, an offender contained in
the component would therefore be an even permutation-module offender.
The odd-degree classification excludes this. Applying the argument to the
actual offender-generated star actor forces R* outside L*, without a
short-block reconstruction or a separate section-faithfulness premise.

Source: Aschbacher–Smith B.3.2, B.5.1, C.2.7(1–2), pp.83,99–103,145–146;
consumer: original15.3.21, p.1127.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

theorem MovedSection.alternatingSeven_offender_not_le {L A : Subgroup D}
    (s : MovedSection ρ L) (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 7))
    (hA : IsOffender ρ A) : ¬ A ≤ L := by
  intro hAL
  have hs := (hA.on_subquotient ρ s.space s.central).subgroupOf s.action hAL
  let f := (alternatingGroup (Fin 7)).subtype.comp e.groupEquiv.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.groupEquiv.injective
  have hact (g : L) (v : s.space.toSubmodule ⧸ s.central.toSubmodule) :
      e.linearEquiv ((s.action.comp L.subtype) g v) =
        BinaryPermutation.naturalRepresentation (Fin 7) (f g) (e.linearEquiv v) :=
    e.intertwines g v
  have hoff := hs.map_equivariant (s.action.comp L.subtype)
    (BinaryPermutation.naturalRepresentation (Fin 7)) f hf e.linearEquiv hact
  have hcore : IsOffender (BinaryPermutation.coreRepresentation (Fin 7))
      ((A.subgroupOf L).map f) := by
    refine ⟨hoff.1,?_⟩
    rw [BinaryPermutation.fixedCodim_core_eq_full_odd _ (by decide),
      ←BinaryPermutation.fixedCodim_natural_eq_full_odd _ (by decide)]
    exact hoff.2
  exact ChapterB.Offenders.core_offender_not_le_alternating (Or.inr rfl) hcore (by
    rintro _ ⟨x,hx,rfl⟩
    exact (e.groupEquiv x).property)
end CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

/-- Literal B.5 component-row consumer on the offender-generated star actor. -/
theorem alternatingSeven_raw_radical_not_le_component
    (h : Input κ H R M K)
    :
    let C := starImage K R K
    let J := offenderSubgroup (starRepresentation K R)
    ∀ (s : MovedSection ((starRepresentation K R).comp J.subtype) (C.subgroupOf J)),
      ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 7) →
      ¬ starImage K R R ≤ C := by
  intro C J s e hRK
  obtain ⟨A,hAR,hA⟩ := (ChapterC.C27Source.kernel_offender_from_source h).2.best
  let ρ := starRepresentation K R
  have hAJ : A ≤ J := hA.le_offenderSubgroup ρ
  have hoff := (hA.subgroupOf ρ hAJ).isOffender (ρ.comp J.subtype)
  exact s.alternatingSeven_offender_not_le (ρ.comp J.subtype) e hoff (comap_mono (hAR.trans hRK))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
