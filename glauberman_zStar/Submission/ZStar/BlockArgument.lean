import Submission.FeitThompson.Representation.Completeness
import Submission.ZStar.CharacterArgument
import Submission.ZStar.Constancy
import Submission.ZStar.SectionReplacement

/-!
# The principal-block contradiction in Glauberman's Z*-argument

This file packages Steps (V)--(VII) of Glauberman's proof against the
ordinary-character infrastructure already available in the repository.

The theorem below does not postulate a new notion of block.  It starts with
an existing complete family of irreducible ordinary characters and a finite
subset `B` of its indices.  The later modular layer only has to prove the
three specialized facts that characterize the principal `2`-block in this
argument:

* constancy on products of the relevant conjugacy classes (Step (V));
* exclusion of the positive degree value for nonprincipal characters;
* weak block orthogonality against the identity (Step (VII)).

Everything after those inputs is ordinary character theory and elementary
algebra.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace BlockArgument

open CharacterArgument

universe u v

attribute [local instance] Fintype.ofFinite

/-- Glauberman Steps (V)--(VII), expressed using the repository's complete
family of irreducible ordinary characters.

The two constancy hypotheses are Step (V), first for `(t,s)` and then for
`(t,t*s)`.  The normalized class-sum identities force the values at `s` and
`t*s` to be negatives for every nonprincipal character.  Weak block
orthogonality of these two involutions against the identity then gives the
final contradiction. -/
theorem false_of_principalBlock_character_relations
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (B : Finset I) (principal : I)
    (hprincipal_mem : principal ∈ B)
    (hprincipal : chi principal = ordinaryPrincipalCharacter G)
    (t s : G) (htI : IsInvolution t)
    (hconstantS : ∀ i ∈ B,
      ∀ x : G, x ∈ (ConjClasses.mk t).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk s).carrier →
        chi i (ConjClasses.mk (x * y)) =
          chi i (ConjClasses.mk (t * s)))
    (hconstantTS : ∀ i ∈ B,
      ∀ x : G, x ∈ (ConjClasses.mk t).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk (t * s)).carrier →
        chi i (ConjClasses.mk (x * y)) =
          chi i (ConjClasses.mk (t * (t * s))))
    (hpositive_excluded : ∀ i ∈ B, i ≠ principal →
      chi i (ConjClasses.mk t) ≠ chi i (ConjClasses.mk (1 : G)))
    (horthS : ∑ i ∈ B,
      chi i (ConjClasses.mk s) * chi i (ConjClasses.mk (1 : G)) = 0)
    (horthTS : ∑ i ∈ B,
      chi i (ConjClasses.mk (t * s)) * chi i (ConjClasses.mk (1 : G)) = 0) :
    False := by
  let valueS : I → ℂ := fun i => chi i (ConjClasses.mk s)
  let valueTS : I → ℂ := fun i => chi i (ConjClasses.mk (t * s))
  let degree : I → ℂ := fun i => chi i (ConjClasses.mk (1 : G))
  apply false_of_principalWeakSectionOrthogonality
    B principal valueS valueTS degree
  · exact hprincipal_mem
  · simp [valueS, hprincipal]
  · simp [valueTS, hprincipal]
  · simp [degree, hprincipal]
  · intro i hi hine
    have hirr : Representation.IsIrreducibleCharacter (chi i) := hchi.1 i
    have hdegree : degree i ≠ 0 := by
      exact irreducibleCharacter_degree_ne_zero (chi i) hirr
    have hratioS :=
      irreducibleCharacterRatio_mul_eq_of_classProducts_constant
        (chi i) hirr t s (hconstantS i hi)
    have hratioTS :=
      irreducibleCharacterRatio_mul_eq_of_classProducts_constant
        (chi i) hirr t (t * s) (hconstantTS i hi)
    have htt : t * t = 1 := by
      simpa [pow_two] using htI.2
    have ht_ts : t * (t * s) = s := by
      rw [← mul_assoc, htt, one_mul]
    rw [ht_ts] at hratioTS
    change chi i (ConjClasses.mk (1 : G)) ≠ 0 at hdegree
    by_cases his : chi i (ConjClasses.mk s) = 0
    · field_simp [hdegree] at hratioS
      change chi i (ConjClasses.mk (t * s)) =
        -chi i (ConjClasses.mk s)
      rw [his, neg_zero]
      apply (mul_left_cancel₀ hdegree)
      simpa [his] using hratioS.symm
    · rcases value_eq_degree_or_neg_degree_of_ratio_relations
          hdegree his hratioS hratioTS with hplus | hminus
      · exact (hpositive_excluded i hi hine hplus).elim
      · field_simp [hdegree] at hratioS
        change chi i (ConjClasses.mk (t * s)) =
          -chi i (ConjClasses.mk s)
        apply (mul_left_cancel₀ hdegree)
        calc
          chi i (ConjClasses.mk (1 : G)) *
              chi i (ConjClasses.mk (t * s)) =
              chi i (ConjClasses.mk t) * chi i (ConjClasses.mk s) := by
                exact hratioS.symm
          _ = (-chi i (ConjClasses.mk (1 : G))) *
              chi i (ConjClasses.mk s) := by rw [hminus]
          _ = chi i (ConjClasses.mk (1 : G)) *
              (-chi i (ConjClasses.mk s)) := by ring
  · simpa [valueS, degree] using horthS
  · simpa [valueTS, degree] using horthTS

/-- The source-faithful form of Steps (V)--(VII), with the positive sign in
Step (VI) discharged by the existing representation-kernel infrastructure.

The remaining hypotheses are precisely the proper-subgroup induction input,
Step (V) constancy, and weak block orthogonality for `s` and `t*s`. -/
theorem false_of_principalBlock_relations_of_properNormal_centrality
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (B : Finset I) (principal : I)
    (hprincipal_mem : principal ∈ B)
    (hprincipal : chi principal = ordinaryPrincipalCharacter G)
    (t s : G) (htI : IsInvolution t)
    (htNotCentral : t ∉ Subgroup.center G)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n)
    (hconstantS : ∀ i ∈ B,
      ∀ x : G, x ∈ (ConjClasses.mk t).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk s).carrier →
        chi i (ConjClasses.mk (x * y)) =
          chi i (ConjClasses.mk (t * s)))
    (hconstantTS : ∀ i ∈ B,
      ∀ x : G, x ∈ (ConjClasses.mk t).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk (t * s)).carrier →
        chi i (ConjClasses.mk (x * y)) =
          chi i (ConjClasses.mk (t * (t * s))))
    (horthS : ∑ i ∈ B,
      chi i (ConjClasses.mk s) * chi i (ConjClasses.mk (1 : G)) = 0)
    (horthTS : ∑ i ∈ B,
      chi i (ConjClasses.mk (t * s)) * chi i (ConjClasses.mk (1 : G)) = 0) :
    False := by
  apply false_of_principalBlock_character_relations
    chi hchi B principal hprincipal_mem hprincipal t s htI
    hconstantS hconstantTS
  · intro i hi hine
    have hnePrincipal : chi i ≠ ordinaryPrincipalCharacter G := by
      intro heq
      apply hine
      apply hchi.2.2
      exact heq.trans hprincipal.symm
    exact irreducibleCharacter_value_ne_degree_of_properNormal_centrality
      (chi i) (hchi.1 i) hnePrincipal t htI htNotCentral hodd hproperCentral
  · exact horthS
  · exact horthTS

/-- Steps (V)--(VII) with Feit XII.8.8 as the only constancy input.

`hreplaceS` and `hreplaceTS` are the two applications of XII.8.8.  The
group-theoretic upgrade to constancy on all class products is supplied by
`Constancy.classProducts_constant_of_commuting_replacements`. -/
theorem false_of_principalBlock_replacements_of_properNormal_centrality
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (B : Finset I) (principal : I)
    (hprincipal_mem : principal ∈ B)
    (hprincipal : chi principal = ordinaryPrincipalCharacter G)
    (t s : G) (htI : IsInvolution t)
    (htNotCentral : t ∉ Subgroup.center G)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n)
    (hreplaceS : ∀ i ∈ B, ∀ r : G,
      r ∈ (ConjClasses.mk s).carrier →
      ∃ r0 : G, r0 ∈ (ConjClasses.mk s).carrier ∧ Commute t r0 ∧
        chi i (ConjClasses.mk (t * r)) =
          chi i (ConjClasses.mk (t * r0)))
    (hreplaceTS : ∀ i ∈ B, ∀ r : G,
      r ∈ (ConjClasses.mk (t * s)).carrier →
      ∃ r0 : G, r0 ∈ (ConjClasses.mk (t * s)).carrier ∧ Commute t r0 ∧
        chi i (ConjClasses.mk (t * r)) =
          chi i (ConjClasses.mk (t * r0)))
    (horthS : ∑ i ∈ B,
      chi i (ConjClasses.mk s) * chi i (ConjClasses.mk (1 : G)) = 0)
    (horthTS : ∑ i ∈ B,
      chi i (ConjClasses.mk (t * s)) * chi i (ConjClasses.mk (1 : G)) = 0) :
    False := by
  have ht_inv : t⁻¹ = t :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  have hoddProduct : ∀ g : G, Odd (orderOf ((g * t * g⁻¹) * t)) := by
    intro g
    simpa [mul_assoc, ht_inv] using hodd g
  apply false_of_principalBlock_relations_of_properNormal_centrality
    chi hchi B principal hprincipal_mem hprincipal t s htI htNotCentral hodd
    hproperCentral
  · intro i hi
    exact Constancy.classProducts_constant_of_commuting_replacements
      (chi i) t s htI hoddProduct (hreplaceS i hi)
  · intro i hi
    exact Constancy.classProducts_constant_of_commuting_replacements
      (chi i) t (t * s) htI hoddProduct (hreplaceTS i hi)
  · exact horthS
  · exact horthTS

/-- The complete non-modular reduction of Glauberman Steps (V)--(VII).

At this interface, the only block-theoretic inputs are:

* `hsection`, the generalized-decomposition/odd-core value identity at an
  involution centralizer (Glauberman Lemmas 4 and 5; Feit IV.4.12);
* `horthOne`, weak block orthogonality between any involution and the identity
  (the much weaker Feit IV.6.2 input).

All conjugacy, dihedral, class-sum, kernel, and final-orthogonality arguments
are discharged below by existing repository infrastructure. -/
theorem false_of_principalBlock_section_invariance
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → Representation.ClassFunction G)
    (hchi : Representation.IsCompleteIrreducibleCharacterFamily chi)
    (B : Finset I) (principal : I)
    (hprincipal_mem : principal ∈ B)
    (hprincipal : chi principal = ordinaryPrincipalCharacter G)
    (S : Sylow 2 G) (t s : G)
    (htI : IsInvolution t) (hsI : IsInvolution s)
    (htS : t ∈ (S : Subgroup G)) (hsS : s ∈ (S : Subgroup G))
    (hst : s ≠ t)
    (htCentral : ∀ x : G, x ∈ (S : Subgroup G) → x * t = t * x)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (htNotCentral : t ∉ Subgroup.center G)
    (hcentralizerProper : ∀ z : G, IsInvolution z →
      Subgroup.centralizer ({z} : Set G) ≠ ⊤)
    (hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n)
    (hproperCoreCentral : ∀ (H : Subgroup G), H ≠ ⊤ → t ∈ H →
      ∀ h : G, h ∈ H →
        h * t * h⁻¹ * t⁻¹ ∈ (pPrimeCore 2 H).map H.subtype)
    (hsection : ∀ i ∈ B, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      chi i (ConjClasses.mk (z * v)) = chi i (ConjClasses.mk z))
    (horthOne : ∀ q : G, IsInvolution q →
      ∑ i ∈ B,
        chi i (ConjClasses.mk q) * chi i (ConjClasses.mk (1 : G)) = 0) :
    False := by
  have hoddProduct : ∀ g : G, Odd (orderOf ((g * t * g⁻¹) * t)) :=
    orderOf_conjugate_mul_odd_of_weaklyClosed S t htI htCentral htWeak
  have hoddComm : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)) :=
    orderOf_commutator_odd_of_weaklyClosed S t htI htCentral htWeak
  have hnotConj_of_mem_ne {r : G}
      (hrS : r ∈ (S : Subgroup G)) (hrne : r ≠ t) : ¬ IsConj r t := by
    intro hrt
    rcases isConj_iff.mp hrt.symm with ⟨g, hg⟩
    have hweak := htWeak.2 g (by simpa [hg] using hrS)
    exact hrne (hg.symm.trans hweak)
  have hstNotConj : ¬ IsConj s t := hnotConj_of_mem_ne hsS hst
  have hcommTS : Commute t s := by
    change t * s = s * t
    exact (htCentral s hsS).symm
  have htsS : t * s ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem htS hsS
  have htsI : IsInvolution (t * s) := by
    constructor
    · intro htsOne
      apply hst
      calc
        s = t⁻¹ * (t * s) := by simp [mul_assoc]
        _ = t⁻¹ := by rw [htsOne, mul_one]
        _ = t := inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
    · have htt : t * t = 1 := by simpa [pow_two] using htI.2
      have hss : s * s = 1 := by simpa [pow_two] using hsI.2
      calc
        (t * s) ^ 2 = t ^ 2 * s ^ 2 := hcommTS.mul_pow 2
        _ = (t * t) * (s * s) := by rw [pow_two, pow_two]
        _ = 1 := by rw [htt, hss, one_mul]
  have hts_ne_t : t * s ≠ t := by
    intro h
    apply hsI.1
    calc
      s = t⁻¹ * (t * s) := by simp [mul_assoc]
      _ = t⁻¹ * t := by rw [h]
      _ = 1 := inv_mul_cancel t
  have htsNotConj : ¬ IsConj (t * s) t :=
    hnotConj_of_mem_ne htsS hts_ne_t
  have hreplacements (q : G) (hqI : IsInvolution q)
      (hqNotConj : ¬ IsConj q t) (i : I) (hi : i ∈ B) :
      ∀ r : G, r ∈ (ConjClasses.mk q).carrier →
        ∃ r0 : G, r0 ∈ (ConjClasses.mk q).carrier ∧ Commute t r0 ∧
          chi i (ConjClasses.mk (t * r)) =
            chi i (ConjClasses.mk (t * r0)) := by
    intro r hr
    have hrq : IsConj r q :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp hr)
    have hrI : IsInvolution r := by
      rcases isConj_iff.mp hrq.symm with ⟨g, hg⟩
      rw [← hg]
      exact OddCommutators.isInvolution_conjugate hqI g
    have hrNotConj : ¬ IsConj r t := by
      intro hrt
      exact hqNotConj (hrq.symm.trans hrt)
    obtain ⟨r0, hr0, htr0, hvalue⟩ :=
      SectionReplacement.exists_commuting_replacement_of_section_invariance
        (chi i) t r htI hrI hrNotConj hoddProduct hcentralizerProper
        hproperCoreCentral (hsection i hi)
    refine ⟨r0, ?_, htr0, hvalue⟩
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact (ConjClasses.mem_carrier_iff_mk_eq.mp hr0).trans
      (ConjClasses.mem_carrier_iff_mk_eq.mp hr)
  apply false_of_principalBlock_replacements_of_properNormal_centrality
    chi hchi B principal hprincipal_mem hprincipal t s htI htNotCentral
    hoddComm hproperCentral
  · exact hreplacements s hsI hstNotConj
  · exact hreplacements (t * s) htsI htsNotConj
  · exact horthOne s hsI
  · exact horthOne (t * s) htsI

end BlockArgument

end Submission.ZStar
