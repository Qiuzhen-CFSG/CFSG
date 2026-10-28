module
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Geometry

/-!
# Fixed points of normal elementary subgroups of a native M23 Sylow group

Every normal elementary subgroup of the certified Sylow group is contained in
one of its two E16 subgroups: each exceptional involution fails to commute with
its conjugate by the tenth listed Sylow element. In the heptad E16, every
nonidentity element fixes exactly the same heptad. In the other E16, conjugation
by the first and eighth listed elements cuts the fixed set down to a triple
unless the subgroup also lies in the heptad E16. This treats every nontrivial
order, including the smaller elementary subgroups.

The normalizer preserves the complete fixed set. Its containment in the two
geometric stabilizers is the exhaustive step for the Sylow-containing locals
in GLS3 Table 5.3d and Aschbacher--Smith 15.3.41--42, printed p.1138. All finite
identities use the existing native permutation tables and are kernel checked.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals.Coverage
open FusionCertificate ElementarySylow
set_option maxRecDepth 100000
set_option Elab.async false

def fixedTriple : Finset (Fin 23) := {0, 6, 12}

private theorem exceptional_noncommuting (k : Fin 8) :
    perm (exceptionalIndex k) * (perm 10 * perm (exceptionalIndex k) * (perm 10)⁻¹) ≠
      (perm 10 * perm (exceptionalIndex k) * (perm 10)⁻¹) * perm (exceptionalIndex k) := by
  intro he
  have hh := Equiv.congr_fun he 1
  have hn : ∀ k : Fin 8,
      (perm (exceptionalIndex k) * (perm 10 * perm (exceptionalIndex k) * (perm 10)⁻¹)) 1 ≠
        ((perm 10 * perm (exceptionalIndex k) * (perm 10)⁻¹) * perm (exceptionalIndex k)) 1 := by
    decide +kernel
  exact hn k hh

private theorem second_fixes : ∀ (i : Fin 16) (a : Fin 23),
    a ∈ FourNormalizers.fixedSet → pointTable (candidateIndex 1 i) a = a := by
  decide +kernel

private theorem second_fixed : ∀ (i : Fin 16) (a : Fin 23),
    i ≠ 0 → pointTable (candidateIndex 1 i) a = a → a ∈ FourNormalizers.fixedSet := by
  decide +kernel

private theorem first_fixes : ∀ (i : Fin 16) (a : Fin 23),
    a ∈ fixedTriple → pointTable (candidateIndex 0 i) a = a := by
  decide +kernel

private theorem first_fixed : ∀ (i : Fin 16) (a : Fin 23),
    pointTable (candidateIndex 0 i) a = a →
    (perm 1 * perm (candidateIndex 0 i) * (perm 1)⁻¹) a = a →
    (perm 8 * perm (candidateIndex 0 i) * (perm 8)⁻¹) a = a →
    a ∈ fixedTriple ∨ ∃ j, candidateIndex 0 i = candidateIndex 1 j := by
  decide +kernel

private noncomputable def element (i : Fin 128) : M23 :=
  ⟨perm i, rawSubgroup_le (perm_mem i)⟩

private theorem element_mem (i : Fin 128) : element i ∈ subgroup := perm_mem i

private theorem elementary_le_candidates (A : Subgroup M23)
    (hAS : A ≤ subgroup) (hn : subgroup ≤ normalizer (A : Set M23))
    (he : IsElementaryAbelian 2 A) :
    A ≤ ElementarySylow.candidate 0 ∨ A ≤ ElementarySylow.candidate 1 := by
  apply SubgroupClass.subset_union.mp
  intro a ha
  obtain ⟨i, hi⟩ := exists_perm ⟨a.val, hAS ha⟩
  have hs : ∀ x, pointTable i (pointTable i x) = x := by
    have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p ⟨a, ha⟩
    have hh := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23))) hp
    rw [pow_two] at hh
    change a.val * a.val = 1 at hh
    rw [← hi] at hh
    exact fun x => Equiv.congr_fun hh x
  rcases square_cases i hs with ⟨b, j, rfl⟩ | ⟨k, rfl⟩
  · fin_cases b
    · exact Or.inl ⟨j, hi⟩
    · exact Or.inr ⟨j, hi⟩
  · have hc : element 10 * a * (element 10)⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (hn (element_mem 10)) a).mp ha
    have hh := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23)))
      (he.toIsMulCommutative.is_comm.comm ⟨a,ha⟩ ⟨_,hc⟩)
    change a.val * (perm 10 * a.val * (perm 10)⁻¹) =
      (perm 10 * a.val * (perm 10)⁻¹) * a.val at hh
    rw [← hi] at hh
    exact (exceptional_noncommuting k hh).elim

/-- The complete fixed set is the specified heptad or the specified triple. -/
theorem normal_elementary_fixed_points (A : Subgroup M23)
    (hAS : A ≤ subgroup) (hn : subgroup ≤ normalizer (A : Set M23))
    (hA : A ≠ ⊥) (he : IsElementaryAbelian 2 A) :
    (∀ a : Fin 23, a ∈ FourNormalizers.fixedSet ↔ ∀ u ∈ A, u • a = a) ∨
    (∀ a : Fin 23, a ∈ fixedTriple ↔ ∀ u ∈ A, u • a = a) := by
  classical
  by_cases hsecond : A ≤ ElementarySylow.candidate 1
  · left
    obtain ⟨⟨u, hu⟩, hune'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    have hune : u ≠ 1 := fun h => hune' (Subtype.ext h)
    obtain ⟨i, hi⟩ := (mem_candidate 1 u).mp (hsecond hu)
    have hi0 : i ≠ 0 := by
      intro h
      subst i
      exact hune (Subtype.ext (hi.symm.trans (by rw [candidate_initial, initial]; rfl)))
    intro a
    constructor
    · intro ha u hu
      obtain ⟨j,hj⟩ := (mem_candidate 1 u).mp (hsecond hu)
      change u.val a = a
      rw [← hj]
      exact second_fixes j a ha
    · intro ha
      apply second_fixed i a hi0
      have hh := ha u hu
      change u.val a = a at hh
      rwa [← hi] at hh
  · right
    have hfirst := (elementary_le_candidates A hAS hn he).resolve_right hsecond
    obtain ⟨u,hu,hun⟩ := Set.not_subset.mp hsecond
    obtain ⟨i,hi⟩ := (mem_candidate 0 u).mp (hfirst hu)
    intro a
    constructor
    · intro ha v hv
      obtain ⟨j,hj⟩ := (mem_candidate 0 v).mp (hfirst hv)
      change v.val a = a
      rw [← hj]
      exact first_fixes j a ha
    · intro ha
      have hu' : pointTable (candidateIndex 0 i) a = a := by
        have hh := ha u hu
        change u.val a = a at hh
        rwa [← hi] at hh
      have hc (j : Fin 128) : (perm j * perm (candidateIndex 0 i) * (perm j)⁻¹) a = a := by
        have hh := ha _ ((mem_normalizer_iff.mp (hn (element_mem j)) u).mp hu)
        change (perm j * u.val * (perm j)⁻¹) a = a at hh
        rwa [← hi] at hh
      rcases first_fixed i a hu' (hc 1) (hc 8) with hf | ⟨j,hj⟩
      · exact hf
      · exact (hun ⟨j, (congrArg perm hj).symm.trans hi⟩).elim

private theorem normalizer_le_fixed_stabilizer (A : Subgroup M23) (F : Finset (Fin 23))
    (hF : ∀ a, a ∈ F ↔ ∀ u ∈ A, u • a = a) :
    normalizer (A : Set M23) ≤ MulAction.stabilizer M23 F := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  apply (hF _).mpr
  intro u hu
  have hv := (mem_normalizer_iff.mp ((normalizer (A : Set M23)).inv_mem hg) u).mp hu
  have hf := (hF a).mp ha _ hv
  have hh := congrArg (fun b : Fin 23 => g • b) hf
  simpa only [inv_inv, mul_smul, smul_inv_smul] using hh

/-- Every nontrivial Sylow-normal elementary subgroup has its full normalizer
inside the stabilizer of the fixed heptad or the fixed triple. -/
theorem normal_elementary_normalizer_coverage (A : Subgroup M23)
    (hAS : A ≤ subgroup) (hn : subgroup ≤ normalizer (A : Set M23))
    (hA : A ≠ ⊥) (he : IsElementaryAbelian 2 A) :
    normalizer (A : Set M23) ≤ MulAction.stabilizer M23 FourNormalizers.fixedSet ∨
    normalizer (A : Set M23) ≤ MulAction.stabilizer M23 fixedTriple := by
  rcases normal_elementary_fixed_points A hAS hn hA he with hh | ht
  · exact Or.inl (normalizer_le_fixed_stabilizer A _ hh)
  · exact Or.inr (normalizer_le_fixed_stabilizer A _ ht)

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals.Coverage
