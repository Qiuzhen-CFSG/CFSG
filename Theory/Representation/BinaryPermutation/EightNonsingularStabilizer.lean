module

public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.IsPerfect

/-!
# Nonsingular point residuals in the binary A₈ natural module

Every nonsingular class has a weight-two representative. Its stabilizer
preserves the representative itself, since two pair words cannot differ
by the all-one word. Restriction to the two marked points kills the
two-residual, while the pointwise fixer is a perfect A₆. Hence that fixer
is exactly the embedded two-residual of the actual vector stabilizer.
The A₆ equivalence restricts the original permutations to the complement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the opening
of the proof of Theorem 12.6.2, printed pp.823–824. The half-weight model
and complement equivalence retain their ATLAS attribution in their imports.
The only finite check enumerates the 256 binary words, not permutations
or subgroups of A₈.
-/

@[expose] public section

open Subgroup
open BinaryPermutation
open BinaryPermutation.TerminalOrthogonal.Eight
namespace BinaryPermutation.EightNonsingular
abbrev A := alternatingGroup (Fin 8)
abbrev S := Equiv.Perm (Fin 8)
abbrev W := natural (Fin 8)
def pair (i j : Fin 8) : core (Fin 8) :=
  ⟨Pi.single i 1 + Pi.single j 1, by simp [mem_core, Finset.sum_add_distrib]⟩

theorem nonsingular_pair (w : W) (hw : form w ≠ 0) :
    ∃ i j : Fin 8, i ≠ j ∧ coreToNatural (Fin 8) (pair i j) = w := by
  obtain ⟨v, rfl⟩ := coreToNatural_surjective w
  have hb : form (coreToNatural (Fin 8) v) = 1 := by
    have h : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
    exact h _ hw
  have hv := (EightGeometry.nonsingular_core_iff v).mp hb
  have hwords : ∀ v : Full (Fin 8), hammingNorm v = 2 ∨ hammingNorm v = 6 →
      ∃ i j : Fin 8, (i ≠ j ∧ (pair i j).val = v) ∨
        (i ≠ j ∧ (pair i j).val + allOne (Fin 8) = v) := by
    decide +kernel
  obtain ⟨i,j,h⟩ := hwords v.val hv
  rcases h with ⟨hij,h⟩ | ⟨hij,h⟩
  · exact ⟨i,j,hij, congrArg (coreToNatural (Fin 8)) (Subtype.ext h)⟩
  · refine ⟨i,j,hij, ?_⟩
    apply sub_eq_zero.mp
    rw [← map_sub, EightGeometry.coreToNatural_eq_zero]
    right
    ext k
    have hh := congrFun h k
    change (pair i j).val k - v.val k = 1
    change (pair i j).val k + 1 = v.val k at hh
    rw [← hh]
    simp [CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero]



open BinaryNaturalDual.VectorStabilizers

def pointFixer (i j : Fin 8) : Subgroup A :=
  fixingSubgroup A ({i,j} : Set (Fin 8))

def stabilizer (w : W) : Subgroup A :=
  representationStabilizer (alternatingNaturalRepresentation (Fin 8)) w

noncomputable def pointFixerEquiv (i j : Fin 8) (hij : i ≠ j) :
    pointFixer i j ≃* alternatingGroup (Fin 6) := by
  classical
  have hs : pointFixer i j = fixingSubgroup A
      (({i,j} : Finset (Fin 8)) : Set (Fin 8)) := by
    simp only [pointFixer, Finset.coe_insert, Finset.coe_singleton]
  have hc : Fintype.card (↑(({i,j} : Finset (Fin 8))ᶜ)) = 6 := by
    rw [Fintype.card_coe, Finset.card_compl]
    simp [hij]
  exact (MulEquiv.subgroupCongr hs).trans
    ((Atlas.Families.Alternating.stabilizerComplementEquiv {i,j}).trans
      (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq hc)))

theorem pointFixer_twoPerfect (i j : Fin 8) (hij : i ≠ j) :
    IsPPerfect 2 (pointFixer i j) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (pointFixer i j) :=
    Group.IsPerfect.ofSurjective (f := (pointFixerEquiv i j hij).symm.toMonoidHom)
      (pointFixerEquiv i j hij).symm.surjective
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (pointFixer i j ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (pointFixer i j ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (pointFixer i j ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (pointFixer i j ⧸ N) inferInstance

theorem pair_action (g : S) (i j : Fin 8) :
    coreRepresentation (Fin 8) g (pair i j) = pair (g i) (g j) := by
  apply Subtype.ext
  ext k
  simp [pair, Pi.single_apply, Equiv.symm_apply_eq]

private theorem pair_difference (i j k l : Fin 8) :
    (pair i j).val - (pair k l).val ≠ allOne (Fin 8) := by
  have hc : ({i,j,k,l} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
    have hb := Finset.card_insert_le i ({j,k,l} : Finset (Fin 8))
    have hb' := Finset.card_insert_le j ({k,l} : Finset (Fin 8))
    have hb'' := Finset.card_le_two (a := k) (b := l)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  intro he
  have h := congrFun he a
  simp [pair, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, allOne] at h

theorem pair_fixed_iff (g : A) (i j : Fin 8) :
    g ∈ stabilizer (coreToNatural (Fin 8) (pair i j)) ↔
      coreRepresentation (Fin 8) g.val (pair i j) = pair i j := by
  change naturalRepresentation (Fin 8) g.val (coreToNatural (Fin 8) (pair i j)) = _ ↔ _
  rw [← coreToNatural_equivariant]
  constructor
  · intro h
    have hz : coreToNatural (Fin 8)
        (coreRepresentation (Fin 8) g.val (pair i j) - pair i j) = 0 := by
      rw [map_sub, h, sub_self]
    rcases (EightGeometry.coreToNatural_eq_zero _).mp hz with he | he
    · exact sub_eq_zero.mp (Subtype.ext he)
    · rw [pair_action] at he
      exact (pair_difference _ _ _ _ he).elim
  · exact congrArg (coreToNatural (Fin 8))

private theorem pair_value (i j k : Fin 8) (hij : i ≠ j) :
    (pair i j).val k = 1 ↔ k = i ∨ k = j := by
  by_cases hi : k = i
  · subst k; simp [pair,hij]
  by_cases hj : k = j
  · subst k; simp [pair,hij.symm]
  simp [pair,hi,hj]

theorem pair_preserved (i j : Fin 8) (hij : i ≠ j)
    (g : stabilizer (coreToNatural (Fin 8) (pair i j))) (k : Fin 8) :
    g.val.val k ∈ ({i,j} : Set (Fin 8)) ↔ k ∈ ({i,j} : Set (Fin 8)) := by
  have hh := congrArg (fun v : core (Fin 8) => v.val (g.val.val k))
    ((pair_fixed_iff g.val i j).mp g.property)
  change (pair i j).val (g.val.val.symm (g.val.val k)) = (pair i j).val (g.val.val k) at hh
  rw [Equiv.symm_apply_apply] at hh
  change (g.val.val k = i ∨ g.val.val k = j) ↔ (k = i ∨ k = j)
  rw [← pair_value i j _ hij, ← pair_value i j _ hij, hh]

noncomputable def pairRestriction (i j : Fin 8) (hij : i ≠ j) :
    stabilizer (coreToNatural (Fin 8) (pair i j)) →*
      Equiv.Perm ({i,j} : Set (Fin 8)) where
  toFun g := g.val.val.subtypePerm (pair_preserved i j hij g)
  map_one' := by ext k; rfl
  map_mul' _ _ := by ext k; rfl

theorem pointFixer_le_stabilizer (i j : Fin 8) :
    pointFixer i j ≤ stabilizer (coreToNatural (Fin 8) (pair i j)) := by
  intro g hg
  apply (pair_fixed_iff g i j).mpr
  rw [pair_action]
  have hi := hg ⟨i, Or.inl rfl⟩
  have hj := hg ⟨j, Or.inr rfl⟩
  change g.val i = i at hi
  change g.val j = j at hj
  rw [hi,hj]

theorem stabilizer_residual (i j : Fin 8) (hij : i ≠ j) :
    (pResidual 2 (stabilizer (coreToNatural (Fin 8) (pair i j)))).map
      (stabilizer (coreToNatural (Fin 8) (pair i j))).subtype = pointFixer i j := by
  classical
  let C := stabilizer (coreToNatural (Fin 8) (pair i j))
  have hp : IsPGroup 2 (Equiv.Perm ({i,j} : Set (Fin 8))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [hij]
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩ k
    have hr := pResidual_le_ker_of_isPGroup 2 (pairRestriction i j hij) hp hg
    exact congrArg Subtype.val (DFunLike.congr_fun hr k)
  · have e := subgroupOfEquivOfLe (pointFixer_le_stabilizer i j)
    have ht := le_pResidual_of_isPPerfect ((pointFixer i j).subgroupOf C)
      ((pointFixer_twoPerfect i j hij).of_surjective e.symm.toMonoidHom e.symm.surjective)
    intro g hg
    exact ⟨⟨g, pointFixer_le_stabilizer i j hg⟩, ht hg, rfl⟩
theorem core_fixed_of_nonsingular (g : A) (w : core (Fin 8))
    (hw : form (coreToNatural (Fin 8) w) ≠ 0)
    (hg : naturalRepresentation (Fin 8) g.val (coreToNatural (Fin 8) w) =
      coreToNatural (Fin 8) w) : coreRepresentation (Fin 8) g.val w = w := by
  obtain ⟨i,j,_,hp⟩ := nonsingular_pair _ hw
  have hpair : coreRepresentation (Fin 8) g.val (pair i j) = pair i j :=
    (pair_fixed_iff g i j).mp (by change naturalRepresentation (Fin 8) g.val _ = _; rwa [hp])
  have hzero : coreToNatural (Fin 8) (pair i j - w) = 0 := by
    rw [map_sub,hp,sub_self]
  have hfix : coreRepresentation (Fin 8) g.val (pair i j - w) = pair i j - w := by
    apply Subtype.ext
    change representation (Fin 8) g.val (pair i j - w).val = (pair i j - w).val
    rcases (EightGeometry.coreToNatural_eq_zero _).mp hzero with hz | hz
    · rw [hz,map_zero]
    · rw [hz,permute_allOne]
  rw [map_sub,hpair] at hfix
  exact sub_right_injective hfix


end BinaryPermutation.EightNonsingular
