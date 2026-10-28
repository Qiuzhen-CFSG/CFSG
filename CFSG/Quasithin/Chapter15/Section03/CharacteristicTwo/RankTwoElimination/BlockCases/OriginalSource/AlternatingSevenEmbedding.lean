module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSevenOffender
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension

/-!
# The source A₇ star actor in seven-letter coordinates

Conjugation on the actual component identifies the reduced star actor with
an injective permutation subgroup of S₇. Its restriction maps the literal
component onto A₇. The kernel is a two-group and hence trivial by C.2.7(1).
No full symmetric extension or module compatibility is assumed.

Source: Aschbacher–Smith C.2.7 and15.3.21, pp.145–147 and1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

/-- The actual reduced star actor embeds in S7, carrying its component onto A7. -/
theorem alternatingSeven_star_embedding
    (h : Input κ H R M K) (eq : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ f : StarQuotient K R →* Equiv.Perm (Fin 7), Function.Injective f ∧
      (starImage K R K).map f = alternatingGroup (Fin 7) := by
  obtain ⟨hk,ho⟩ := C27Source.kernel_offender_from_source h
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : eq x ∈ center (alternatingGroup (Fin 7)) := (centerCongr eq ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact eq.map_eq_one_iff.mp he
  have hne := starImage_ne_bot_of_bound h.normalizes h.quasisimple hk.upper
  let a := coreStarEquivOfCenterEqBot h.normalizes h.quasisimple hne hz
  let eK : starImage K R K ≃* alternatingGroup (Fin 7) := a.symm.trans eq
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let D := starImage K R K
  let : D.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hcore : pCore 2 D = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : D.Normal).isSubnormal,hk.reduced.2.2,
      MonoidHom.comap_bot,Subgroup.ker_subtype]
  let e : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans eK
  obtain ⟨f,hf⟩ := alternatingGroup.SevenComponent.exists_extension D e
  have hfK (k : D) : f k = (eK k).val := hf k
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hquot : IsPGroup 2 (StarQuotient K R ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D (starImage K R R)
      (hR.comap_subtype.map _) (starImage_sup_eq_top K R)
  have hfi : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
    ((alternatingGroup.SevenComponent.extension_kernel_eq_twoCore D e hquot f hf).trans hk.reduced.2.2)
  refine ⟨f,hfi,le_antisymm ?_ ?_⟩
  · rintro _ ⟨k,hk,rfl⟩
    rw [hfK ⟨k,hk⟩]
    exact (eK ⟨k,hk⟩).property
  · intro k hk
    obtain ⟨x,hx⟩ := eK.surjective ⟨k,hk⟩
    exact ⟨x,x.property,(hfK x).trans (congrArg Subtype.val hx)⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
