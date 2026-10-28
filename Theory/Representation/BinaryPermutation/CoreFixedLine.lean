module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# Fixed vectors in an alternating augmentation core

Transitivity on coordinates forces every fixed vector to be constant.
In even degree the constant line lies in the augmentation core; consequently
its multiplicative fixed subgroup has order two. This calculation retains
both the original core and the literal coordinate-permutation action.

Source: Aschbacher–Smith, B.3.1, printed p.83; used in13.4.1–2, pp.896–897.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinaryPermutation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem core_fixed_iff_constant (hn : 3 ≤ Nat.card Ω) (v : core Ω) :
    (∀ a : alternatingGroup Ω, coreRepresentation Ω a.val v = v) ↔
      v.val ∈ constants Ω := by
  constructor
  · intro h
    let :=  alternatingGroup.isPretransitive_of_three_le_card Ω hn
    have : Nonempty Ω := (Nat.card_pos_iff.mp (show 0 < Nat.card Ω by omega)).1
    let i : Ω := Classical.choice inferInstance
    apply (mem_constants_iff v.val).mpr
    refine ⟨v.val i, fun j => ?_⟩
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup Ω) i j
    have he := congrArg (fun w : core Ω => w.val j) (h a)
    change v.val (a.val.symm j) = v.val j at he
    have hi : a.val.symm j = i := a.val.symm_apply_eq.mpr ha.symm
    rw [hi] at he
    exact he.symm
  · intro h a
    obtain ⟨c, hc⟩ := (mem_constants_iff v.val).mp h
    apply Subtype.ext
    funext i
    exact (hc (a.val.symm i)).trans (hc i).symm

/-- The actual constant line inside the augmentation core. -/
def coreConstants : Submodule (ZMod 2) (core Ω) :=
  (constants Ω).comap (core Ω).subtype

omit [DecidableEq Ω] in
/-- In even degree the literal constant line has order two. -/
theorem card_coreConstants [Nonempty Ω] (he : Even (Fintype.card Ω)) :
    Nat.card (coreConstants (Ω := Ω)) = 2 := by
  change Nat.card ((constants Ω).comap (core Ω).subtype) = 2
  rw [Nat.card_congr (Submodule.comapSubtypeEquivOfLe
    ((constants_le_core_iff Ω).mpr he)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_constants, pow_one]

end BinaryPermutation
