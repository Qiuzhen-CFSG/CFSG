module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
public import Theory.SpecificGroups.G2Even.TwoRank.SourceBound
public import Theory.Representation.Quotient

/-!
# The G₂ obstruction at sharp constituent degree

For a single actual component, the proved automorphism two-rank is at most
3n. The nonbinary irreducible module degree formula, within the G.9 window,
forces degree 6n. Thus the sharper bound dim V ≤ m+2 is impossible for n≥2.
The proof keeps the actual derived-group isomorphism and faithful action.

Source: Aschbacher–Smith G.9.3(10), G.11.8, printed pp.354,368–369.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
variable {D V K : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field K] [Finite K] [CharP K 2]
attribute [local instance] ZMod.algebra

/-- Nonbinary G₂ cannot occur with the original actor and sharp degree. -/
theorem not_nonbinary_of_sharp_degree
    {C : GroupClass} {ρ : Representation (ZMod 2) D V} {L A : Subgroup D} {m : ℕ}
    (h : ComponentHypothesis C ρ A L L m)
    (hd : Module.finrank (ZMod 2) V ≤ m + 2)
    (e : L ≃* commutator (Atlas.G2.Model K))
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n) : False := by
  have hq : 2 < Nat.card K := by
    rw [hK]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let : Group.IsPerfect (Atlas.G2.Model K) := Atlas.G2.isPerfect hq
  let E : L ≃* Atlas.G2.Model K :=
    e.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv)
  let σ := (ρ.comp L.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ :=
    h.faithful.comp (L.subtype_injective.comp E.symm.injective)
  have hw := actor_bound_of_model_rank h E
    (Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le K hn hK)
  obtain ⟨_,t,l,ht,_,hnt,hdim,hne,hbasic⟩ :=
    Nonbinary.exists_basic_parameters σ hn hK hf
  have hp := small_basic_block_parameters l hbasic hne (by omega) ht hnt hdim hw.2
  omega
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
