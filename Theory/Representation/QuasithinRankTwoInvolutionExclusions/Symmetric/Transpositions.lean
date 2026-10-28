module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.Faithful
public import Mathlib.Tactic

/-!
# Transposition rank on the actual binary natural section

A transposition displaces a permutation vector by a scalar multiple of its
weight-two pair vector. The same formula holds after restricting to the
augmentation core and passing to the quotient by constants. Thus its
natural-module displacement has rank at most one; faithfulness in degree
at least five makes the rank exactly one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric
open _root_.Equiv BinaryPermutation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private def pair (a b : Ω) : core Ω :=
  ⟨Pi.single a 1 + Pi.single b 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private theorem core_swap_displacement (a b : Ω) (hab : a ≠ b) (v : core Ω) :
    coreRepresentation Ω (swap a b) v - v = (v.val a + v.val b) • pair a b := by
  apply Subtype.ext
  funext i
  by_cases hi : i = a
  · subst i
    change v.val ((swap a b).symm a) - v.val a =
      (v.val a + v.val b) * ((Pi.single a 1 : Full Ω) a + (Pi.single b 1 : Full Ω) a)
    simp [hab, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  by_cases hj : i = b
  · subst i
    change v.val ((swap a b).symm b) - v.val b =
      (v.val a + v.val b) * ((Pi.single a 1 : Full Ω) b + (Pi.single b 1 : Full Ω) b)
    simp [hab.symm, sub_eq_add_neg, CharTwo.neg_eq]
  · change v.val ((swap a b).symm i) - v.val i =
      (v.val a + v.val b) * ((Pi.single a 1 : Full Ω) i + (Pi.single b 1 : Full Ω) i)
    simp [hi, hj, swap_apply_of_ne_of_ne]

theorem natural_swap_rank (hn : 5 ≤ Fintype.card Ω) (a b : Ω) (hab : a ≠ b) :
    Module.finrank (ZMod 2) (movedSpace (naturalRepresentation Ω) (swap a b)) = 1 := by
  classical
  let p := coreToNatural Ω (pair a b)
  have hle : movedSpace (naturalRepresentation Ω) (swap a b) ≤
      Submodule.span (ZMod 2) {p} := by
    rintro w ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := coreToNatural_surjective x
    change naturalRepresentation Ω (swap a b) (coreToNatural Ω u) -
      coreToNatural Ω u ∈ _
    rw [← coreToNatural_equivariant, ← map_sub, core_swap_displacement a b hab, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hd : Module.finrank (ZMod 2)
      (movedSpace (naturalRepresentation Ω) (swap a b)) ≤ 1 := by
    apply (Submodule.finrank_mono hle).trans
    simpa using (finrank_span_le_card ({p} : Set (natural Ω)))
  have hz : Module.finrank (ZMod 2)
      (movedSpace (naturalRepresentation Ω) (swap a b)) ≠ 0 := by
    intro he
    have h0 := Submodule.finrank_eq_zero.mp he
    have hm : naturalRepresentation Ω (swap a b) = 1 := by
      apply sub_eq_zero.mp
      exact LinearMap.range_eq_bot.mp h0
    have hs := naturalRepresentation_injective Ω hn
      (hm.trans (naturalRepresentation Ω).map_one.symm)
    exact hab (_root_.Equiv.swap_eq_one_iff.mp hs)
  omega

theorem natural_isSwap_rank (hn : 5 ≤ Fintype.card Ω) (v : Perm Ω) (hv : v.IsSwap) :
    Module.finrank (ZMod 2) (movedSpace (naturalRepresentation Ω) v) = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := hv
  exact natural_swap_rank hn a b hab

end Representation.RankTwo.Symmetric
