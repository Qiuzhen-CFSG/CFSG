module

/-
Adapted from Atlas/Comparisons/Exceptional/TriplePartitions.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
set_option warningAsError false

@[expose] public section


/-!
# The ten complementary-triple partitions of six labels

The objects are actual unordered pairs `{s, sᶜ}` of three-subsets of `Fin 6`.
The symmetric group acts by relabeling, and this action restricts to the actual
alternating group. The marking lists every such object exactly once. Its order
is adapted to the affine coordinates `a + b ω` and infinity on a projective line
over a nine-element field, where `ω² = -1`.

The only finite residual checks enumerate the 64 subsets of six labels, the ten
marked partitions, and the actions of two disjoint three-cycles and a double
transposition. No permutation group enumeration or assumed recognition theorem
is used. Faithfulness follows from the existing simplicity theorem for A6 and
the exhibited nontrivial action.
-/

namespace Atlas.Comparisons.Exceptional.TriplePartitions

open scoped Pointwise
abbrev Ω := Fin 6
abbrev Sym := Equiv.Perm Ω

def pair (s : Finset Ω) : Finset (Finset Ω) := {s, sᶜ}

def partitions : SubMulAction Sym (Finset (Finset Ω)) where
  carrier := {p | ∃ s : Finset Ω, s.card = 3 ∧ p = pair s}
  smul_mem' g p hp := by
    obtain ⟨s, hs, rfl⟩ := hp
    refine ⟨g • s, Finset.card_smul_finset g s |>.trans hs, ?_⟩
    have hc : g • sᶜ = (g • s)ᶜ := by
      ext i
      simp only [Finset.mem_smul_finset, Finset.mem_compl]
      constructor
      · rintro ⟨j, hj, rfl⟩ ⟨k, hk, h⟩
        exact hj ((g.injective h) ▸ hk)
      · intro h
        refine ⟨g.symm i, ?_, g.apply_symm_apply i⟩
        intro hi
        exact h ⟨g.symm i, hi, g.apply_symm_apply i⟩
    simp only [pair, Finset.smul_finset_insert, Finset.smul_finset_singleton, hc]

abbrev Partition := partitions

def triple : Fin 10 → Finset Ω := ![
 {0,1,3}, {0,4,5}, {0,2,3}, {0,1,4}, {0,3,5},
 {0,2,4}, {0,1,5}, {0,3,4}, {0,2,5}, {0,1,2}]

def label (i : Fin 10) : Partition := ⟨pair (triple i), triple i, by
  have h : ∀ i : Fin 10, (triple i).card = 3 := by decide
  exact ⟨h i, rfl⟩⟩

theorem label_bijective : Function.Bijective label := by
  constructor
  · intro i j h
    have hh : ∀ i j : Fin 10, pair (triple i) = pair (triple j) → i = j := by decide
    exact hh i j (congrArg Subtype.val h)
  · intro p
    obtain ⟨s, hs, hp⟩ := p.property
    have hh : ∀ s : Finset Ω, s.card = 3 → ∃ i : Fin 10, pair (triple i) = pair s := by decide
    obtain ⟨i, hi⟩ := hh s hs
    exact ⟨i, Subtype.ext (hi.trans hp.symm)⟩

noncomputable def marking : Fin 10 ≃ Partition := Equiv.ofBijective label label_bijective

theorem partition_card : Nat.card Partition = 10 := by
  rw [← Nat.card_congr marking, Nat.card_fin]

noncomputable def symmetricAction : Sym →* Equiv.Perm (Fin 10) :=
  marking.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom Sym Partition)

noncomputable def action : alternatingGroup Ω →* Equiv.Perm (Fin 10) :=
 symmetricAction.comp (alternatingGroup Ω).subtype

theorem symmetricAction_eq (g : Sym) (i j : Fin 10)
    (h : g • pair (triple i) = pair (triple j)) : symmetricAction g i = j := by
  change marking.symm (g • label i) = j
  have hh : g • label i = label j := Subtype.ext h
  rw [hh]
  exact marking.symm_apply_apply j

/-- The two disjoint three-cycles and a double transposition in the actual A6. -/
def firstCyclePerm : Sym where
  toFun := ![1,2,0,3,4,5]
  invFun := ![2,0,1,3,4,5]
  left_inv := by decide
  right_inv := by decide

def secondCyclePerm : Sym where
  toFun := ![0,1,2,4,5,3]
  invFun := ![0,1,2,5,3,4]
  left_inv := by decide
  right_inv := by decide

def doubleSwapPerm : Sym where
  toFun := ![1,0,3,2,4,5]
  invFun := ![1,0,3,2,4,5]
  left_inv := by decide
  right_inv := by decide

def firstCycle : alternatingGroup Ω :=
  ⟨firstCyclePerm, by change Equiv.Perm.sign firstCyclePerm = 1; decide⟩
def secondCycle : alternatingGroup Ω :=
  ⟨secondCyclePerm, by change Equiv.Perm.sign secondCyclePerm = 1; decide⟩
def doubleSwap : alternatingGroup Ω :=
  ⟨doubleSwapPerm, by change Equiv.Perm.sign doubleSwapPerm = 1; decide⟩

def shiftOne : Equiv.Perm (Fin 10) where
  toFun := ![1,2,0,4,5,3,7,8,6,9]
  invFun := ![2,0,1,5,3,4,8,6,7,9]
  left_inv := by decide
  right_inv := by decide

def shiftOmega : Equiv.Perm (Fin 10) where
  toFun := ![3,4,5,6,7,8,0,1,2,9]
  invFun := ![6,7,8,0,1,2,3,4,5,9]
  left_inv := by decide
  right_inv := by decide

def invert : Equiv.Perm (Fin 10) where
  toFun := ![9,2,1,3,7,8,6,4,5,0]
  invFun := ![9,2,1,3,7,8,6,4,5,0]
  left_inv := by decide
  right_inv := by decide

theorem action_firstCycle : action firstCycle = shiftOne := by
  apply Equiv.ext
  intro i
  apply symmetricAction_eq
  have h : ∀ i : Fin 10, firstCyclePerm • pair (triple i) = pair (triple (shiftOne i)) := by decide
  exact h i

theorem action_secondCycle : action secondCycle = shiftOmega := by
  apply Equiv.ext
  intro i
  apply symmetricAction_eq
  have h : ∀ i : Fin 10,
      secondCyclePerm • pair (triple i) = pair (triple (shiftOmega i)) := by decide
  exact h i

theorem action_doubleSwap : action doubleSwap = invert := by
  apply Equiv.ext
  intro i
  apply symmetricAction_eq
  have h : ∀ i : Fin 10, doubleSwapPerm • pair (triple i) = pair (triple (invert i)) := by decide
  exact h i

theorem action_injective : Function.Injective action := by
  let : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup (by simp [Ω])
  apply action.ker_eq_bot_iff.mp
  rcases (inferInstance : action.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hm : firstCycle ∈ action.ker := by rw [h]; trivial
    have he : action firstCycle = 1 := hm
    rw [action_firstCycle] at he
    have hh := congrArg (fun p : Equiv.Perm (Fin 10) => p 0) he
    exact (by decide : (1 : Fin 10) ≠ 0) hh

end Atlas.Comparisons.Exceptional.TriplePartitions

