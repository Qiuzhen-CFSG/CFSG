module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Singleton highest support from a small quadratic actor

The actual quadratic actor embeds in the full linear normalizer without
changing rank or fixed codimension. The binary SL₄ automorphism rank bound
bounds its rank by four. The proved multiple-support displacement estimate
therefore excludes support of size at least two. Faithfulness excludes empty
support, leaving a singleton for the natural/dual/exterior recognition.

Source: Aschbacher--Smith B.4.2(9--10), B.4.5, and their application in
13.8.25, printed pp.960--961. This is the support reduction, not an assumed
module catalogue or degree bound.
-/

public section
namespace CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
open Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open ChapterK.Linear.Recognition.BinaryCubicSieve
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem actor_rank_le : primeRank 2 Group ≤ 4 := by
  have h := primeRank_le_of_injective 2 (MulAut.conj : Group →* MulAut Group)
    (conj_injective_of_center_eq_bot (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 4)))
  rw [primeRank_equiv 2 (MulAut.congr Atlas.Order20160A8.sl4TwoEquivPSL)] at h
  exact h.trans BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le

/-- The actual small quadratic actor excludes every multiple-root support.
Only the fixed SL₄ action is used, with no degree or model hypothesis. -/
theorem exists_singleton_highest (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) [IsIrreducible σ] (hq : quadraticRatio σ ≤ 2) :
    ∃ (i : Fin 3) (v : V), v ≠ 0 ∧ LocalHighestVector σ {i} v := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨A, hA, hquad, hbound⟩ := (quadraticRatio_le_two_iff σ).mp hq
  have hcard := (primeRank_le_iff_elementary_card_le Group).mp actor_rank_le A hA.2
  have hr : rank A ≤ 4 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  let f : Group →* linearNormalizer σ := σ.asGroupHom.codRestrict _
    (fun g => (actionImage σ).le_normalizer ⟨g, rfl⟩)
  have hfi : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg (fun z : linearNormalizer σ => z.val.val) h
  obtain ⟨he, hc, hb⟩ := ChapterK.Exceptional.cubic_actor_map_equivariant σ
    (normalizerRepresentation σ) f hfi (LinearEquiv.refl _ _)
    (fun _ _ => rfl) hA (isCubic_of_isQuadratic hquad) hbound
  have hr' : rank (A.map f) ≤ 4 := by rwa [rank_map_injective f hfi]
  obtain ⟨J, v, hv, hJ⟩ := exists_localHighestVector σ
  have hpos := Finset.card_pos.mpr (hJ.nonempty_of_faithful hf hv)
  have hone : J.card = 1 := by
    by_contra hn
    exact (not_lt_of_ge hb) ((FourDisplacement.multiple_support_displacement σ hf inferInstance)
      J v hv hJ (by omega) (A.map f) he hc hr')
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
  exact ⟨i, v, hv, hJ⟩
end CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
