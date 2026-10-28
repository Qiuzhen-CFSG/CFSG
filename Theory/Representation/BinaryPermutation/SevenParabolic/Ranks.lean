module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.Quasithin.Rank
import Mathlib.Tactic
/-!
# Rank bounds for the seven-point actor and complementary-plane fixer

The whole actor embeds in S₇ and has two-rank at most three. A permutation
fixing all three pair vectors on the complementary letters fixes each letter
there; restriction then embeds its pointwise fixer into S₄, whose two-rank
is at most two. Weight-four conjugacy transports this bound without assuming
that the full actor is A₇ or that its Sylow centralizer is always D₈.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final argument
of Lemma 12.8.13(6), printed pp.856–857.
-/

@[expose] public section
namespace BinaryPermutation.SevenParabolic

open Theory.GroupTheory Subgroup

lemma actor_twoRank_le {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 7)) (hf : Function.Injective f) : primeRank 2 A ≤ 3 := by
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans_eq
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric

private lemma symmetricFour_twoRank_le : primeRank 2 (Equiv.Perm (Fin 4)) ≤ 2 := by
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := Classical.choice inferInstance
  obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  rw [P.primeRank_eq, primeRank_equiv 2 e]
  exact dihedral_rank_le_two 2

lemma support_invariant (v : Space) (g : pointStabilizer v) (i : Fin 7) :
    v.val (g.val i) ≠ 0 ↔ v.val i ≠ 0 := by
  have h := congrArg (fun w : Space => w.val (g.val i)) g.property
  change v.val (g.val.symm (g.val i)) = v.val (g.val i) at h
  simp only [Equiv.symm_apply_apply] at h
  rw [h]

/-- The restriction of the point stabilizer to the support of its fixed vector. -/
def supportAction (v : Space) : pointStabilizer v →* Equiv.Perm {i // v.val i ≠ 0} where
  toFun g := g.val.subtypePerm (support_invariant v g)
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

private lemma firstFour_support (i : Fin 7) : firstFour.val i ≠ 0 ↔ i.val < 4 := by
  fin_cases i <;> decide

private lemma fixes_last_three (g : plusFixer firstFour) :
    ∀ i : Fin 7, 4 ≤ i.val → g.val i = i := by
  have h56 := g.property.2 pair56 ((plus_firstFour _).mpr (Or.inr (Or.inl rfl)))
  have h57 := g.property.2 pair57 ((plus_firstFour _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h67 := g.property.2 pair67 ((plus_firstFour _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have h4 : g.val.symm 4 = 4 := by
    have h := congrArg (fun w : Space => w.val 4) h56
    have k := congrArg (fun w : Space => w.val 4) h57
    change pair56.val (g.val.symm 4) = 1 at h
    change pair57.val (g.val.symm 4) = 1 at k
    generalize hi : g.val.symm 4 = i at h k ⊢
    fin_cases i <;> simp_all [pair56, pair57]
  have h5 : g.val.symm 5 = 5 := by
    have h := congrArg (fun w : Space => w.val 5) h56
    have k := congrArg (fun w : Space => w.val 5) h67
    change pair56.val (g.val.symm 5) = 1 at h
    change pair67.val (g.val.symm 5) = 1 at k
    generalize hi : g.val.symm 5 = i at h k ⊢
    fin_cases i <;> simp_all [pair56, pair67]
  have h6 : g.val.symm 6 = 6 := by
    have h := congrArg (fun w : Space => w.val 6) h57
    have k := congrArg (fun w : Space => w.val 6) h67
    change pair57.val (g.val.symm 6) = 1 at h
    change pair67.val (g.val.symm 6) = 1 at k
    generalize hi : g.val.symm 6 = i at h k ⊢
    fin_cases i <;> simp_all [pair57, pair67]
  intro i hi
  apply g.val.symm.injective
  fin_cases i <;> simp_all

private def standardFixerSupport : plusFixer firstFour →* Equiv.Perm {i // firstFour.val i ≠ 0} :=
  (supportAction firstFour).comp
    (Subgroup.inclusion (show plusFixer firstFour ≤ pointStabilizer firstFour from fun _ h => h.1))

private lemma standardFixerSupport_injective : Function.Injective standardFixerSupport := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 4
  · exact congrArg Subtype.val
      (Equiv.congr_fun he (⟨i, (firstFour_support i).mpr hi⟩ : {i // firstFour.val i ≠ 0}))
  · rw [fixes_last_three g i (by omega), fixes_last_three h i (by omega)]

lemma standard_plusFixer_twoRank_le : primeRank 2 (plusFixer firstFour) ≤ 2 := by
  let e : {i // firstFour.val i ≠ 0} ≃ Fin 4 := Fintype.equivOfCardEq (by decide)
  have h := Theory.GroupTheory.primeRank_le_of_injective 2 standardFixerSupport standardFixerSupport_injective
  have he := primeRank_equiv 2 (Equiv.permCongrHom e)
  exact h.trans (he.le.trans symmetricFour_twoRank_le)

lemma plus_permute (s : Equiv.Perm (Fin 7)) (v w : Space) (hw : w ∈ plus v) :
    action s w ∈ plus (action s v) := by
  intro i hi
  exact hw (s.symm i) hi

/-- Conjugation respects both the distinguished point and its complementary plane. -/
def conjugatePlusFixer (s : Equiv.Perm (Fin 7)) (v : Space) :
    plusFixer v →* plusFixer (action s v) :=
  ((MulAut.conj s).toMonoidHom.comp (plusFixer v).subtype).codRestrict _ (by
    intro g
    constructor
    · change action (s * g.val * s⁻¹) (action s v) = action s v
      change action s (action g.val (action s⁻¹ (action s v))) = action s v
      have hi : action s⁻¹ (action s v) = v := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      rw [hi, g.property.1]
    · intro w hw
      have hw' : action s⁻¹ w ∈ plus v := by
        have h := plus_permute s⁻¹ (action s v) w hw
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] using h
      change action (s * g.val * s⁻¹) w = w
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, g.property.2 _ hw']
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply])

lemma plusFixer_twoRank_le (v : Space) (hv : weight v = 4) : primeRank 2 (plusFixer v) ≤ 2 := by
  obtain ⟨s, hs⟩ := exists_permutation_firstFour v hv
  have hf : Function.Injective (conjugatePlusFixer s v) := by
    intro g h he
    exact Subtype.ext ((MulAut.conj s).injective (congrArg Subtype.val he))
  have hr := Theory.GroupTheory.primeRank_le_of_injective 2 (conjugatePlusFixer s v) hf
  rw [hs] at hr
  exact hr.trans standard_plusFixer_twoRank_le

/-- For a subgroup T fixing v, this literal intersection is its pointwise
centralizer of the complementary plane. Its inclusion in the permutation
fixer gives the bound for the actual actor and subgroup, in both overgroups. -/
lemma actor_planeCentralizer_twoRank_le {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 7)) (hf : Function.Injective f)
    (T : Subgroup A) (v : Space) (hv : weight v = 4) :
    primeRank 2 (T ⊓ (plusFixer v).comap f : Subgroup A) ≤ 2 := by
  let C := T ⊓ (plusFixer v).comap f
  let j : C →* plusFixer v := (f.comp C.subtype).codRestrict _ (fun x => x.property.2)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
    (plusFixer_twoRank_le v hv)

end BinaryPermutation.SevenParabolic
