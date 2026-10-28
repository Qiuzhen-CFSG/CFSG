module
public import CFSG.Quasithin.ChapterC.Section03.A5.TrialityParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.SpecificGroups.Triality.TwoLocalCover.InvariantParabolic

/-!
# An invariant characteristic-two escape for triality deleted-five blocks

The original block normalizes its nonzero elementary layer. The colored
fixed-tree center places that normalizer in one root parabolic which every
automorphism preserving the same layer also preserves. The parabolic is
self-centralizing at its two-core, and the full-Sylow local-component
obstruction is transported along the literal conjugate-parabolic equivalence.
Thus the original block, rather than an unrelated five-letter subgroup,
provides the characteristic-two overgroup required by the terminal argument.
Source: Aschbacher--Smith 2.4.25, printed p.543, the triality row.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]

/-- Transport the intrinsic root-parabolic obstruction to the same original
block in a specified subgroup of the ambient carrier. -/
theorem triality_parabolic_obstruction_of_equiv (P : Parameters) (hp : P.prime = 2)
    (a : Node) (A N : Subgroup G) (hA : IsShort A) (hAN : A ≤ N)
    (e : N ≃* parabolic P a) :
    N ∈ Chapter1.He G ∧
      ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents (Q : Subgroup N) := by
  refine ⟨Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      (Chapter1.mem_He_iff.mp (triality_parabolic_mem_He P hp a))), ?_⟩
  intro Q hl
  let B := (A.subgroupOf N).map e.toMonoidHom
  have hB : IsShort B := RankOne.Solvable.isShort_of_equiv
    ((subgroupOfEquivOfLe hAN).symm.trans (e.subgroupMap (A.subgroupOf N))) hA
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  have hm : B ∈ ChapterA.Section03.localCComponents ((Q : Subgroup N).map e.toMonoidHom) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom
  have hbad := triality_parabolic_not_local_short P hp a B hB (Q.mapSurjective hes)
  rw [Sylow.coe_mapSurjective] at hbad
  exact hbad hm

/-- The actual deleted-five block has an intrinsic characteristic-two escape
which every automorphism preserving its original layer also preserves. -/
theorem native_triality_invariant_escape (f : ℕ) (hf : 0 < f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (A : Subgroup (BinaryCarrier f hf)) (hA : IsAlternatingBlock A 5) :
    let U := (blockU A).map A.subtype
    ∃ N : Subgroup (BinaryCarrier f hf),
      N ∈ Chapter1.He (BinaryCarrier f hf) ∧ A ≤ N ∧
      (∀ a : MulAut (BinaryCarrier f hf), U.map a.toMonoidHom = U →
        N.map a.toMonoidHom = N) ∧
      ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents (Q : Subgroup N) := by
  let U := (blockU A).map A.subtype
  have hU : U ≠ ⊥ := by
    intro he
    apply hA.2.1.blockU_ne_bot
    apply map_injective A.subtype_injective
    simpa only [Subgroup.map_bot] using he
  have hp : IsPGroup 2 U := (pCore_isPGroup.to_le blockU_le_core).map A.subtype
  obtain ⟨g, i, hN, hinv⟩ := TwoLocalCover.invariant_normalizer_parabolic f hf U hU hp
  let N := (parabolic (binaryParameters f hf) i).map (MulAut.conj g).toMonoidHom
  have hAN : A ≤ N := (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))).trans hN
  let e : N ≃* parabolic (binaryParameters f hf) i :=
    ((parabolic (binaryParameters f hf) i).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  obtain ⟨he, hbad⟩ := triality_parabolic_obstruction_of_equiv
    (binaryParameters f hf) rfl i A N hA.2.1 hAN e
  exact ⟨N, he, hAN, hinv, hbad⟩

end CFSG.Quasithin.ChapterC
