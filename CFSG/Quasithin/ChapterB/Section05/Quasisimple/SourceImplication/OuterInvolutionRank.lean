module

public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank

/-!
# Outer-involution centralizer ranks for B.5.1

For the concrete PSL₄(2) and PSL₅(2) carriers, the centralizer of an outer
involution in the full automorphism group has two-rank at most four.
In degree four the entire automorphism group already has this rank bound.

In degree five, restrict the actual quotient by inner automorphisms to the
full centralizer. Its kernel embeds in the literal inner centralizer, which
is isomorphic to the fixed S₆ by `SixSylowActors.Five.exists_fixedModel` and
the faithful inner embedding. The imported sharp S₆ bound uses a nonabelian
Sylow subgroup of order sixteen. The cyclic outer quotient contributes at
most one more to the rank. Transport uses `OuterCyclic.projectiveEquivLinear`
and preserves both innerness and commutation with the given involution.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 proof,
case (II), printed p.101 (PDF p.112). This module supplies the independent
intrinsic model bound; the source assembly retains the embedding of its actor
and the exchanged-summand argument.
-/

public section

open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.OuterInvolutionRank

open BinaryNaturalDual.FiveActors in
/-- An outer involution in the full automorphism group of GL₅(2) has
centralizer of two-rank at most four. The inner kernel is the fixed S₆. -/
theorem linear_five_centralizer_rank_le_four
    (t : MulAut (LinearGroup 5)) (ht : t ^ 2 = 1)
    (hout : t ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    primeRank 2 (centralizer ({t} : Set (MulAut (LinearGroup 5)))) ≤ 4 := by
  let C := centralizer ({t} : Set (MulAut (LinearGroup 5)))
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 5))).comp C.subtype
  let j : f.ker →* innerCentralizer t :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property,
        x.1.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    have he : x.1.1 = y.1.1 :=
      congrArg (fun z : innerCentralizer t => (z : MulAut (LinearGroup 5))) h
    exact Subtype.ext (Subtype.ext he)
  obtain ⟨e⟩ := innerCentralizer_equiv_six t ht hout
  have hk : primeRank 2 f.ker ≤ 3 := by
    apply (primeRank_le_of_injective 2 j hj).trans
    rw [primeRank_equiv 2 e]
    exact ModuleGeometry.symmetric_six_rank_le_three
  let : IsCyclic (MulAut.Outer (LinearGroup 5)) := linear_outer_isCyclic (Or.inr rfl)
  have ho : primeRank 2 (MulAut.Outer (LinearGroup 5)) ≤ 1 := by
    let P : Sylow 2 (MulAut.Outer (LinearGroup 5)) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic inferInstance
  exact (primeRank_le_ker_add (p := 2) f).trans (Nat.add_le_add hk ho)

/-- The degree-four bound holds for the centralizer of every automorphism. -/
theorem psl4_centralizer_rank_le_four
    (t : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    primeRank 2 (centralizer ({t} : Set (MulAut
      (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))))) ≤ 4 :=
  (primeRank_le_of_injective 2 (centralizer ({t} : Set _)).subtype
    Subtype.val_injective).trans BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le

/-- The full automorphism centralizer of an outer involution of PSL₅(2)
has two-rank at most four, using the actual projective-to-linear isomorphism. -/
theorem psl5_outer_involution_centralizer_rank_le_four
    (t : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)))
    (ht : orderOf t = 2)
    (hout : t ∉ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))) :
    primeRank 2 (centralizer ({t} : Set (MulAut
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))))) ≤ 4 := by
  let e := projectiveEquivLinear (by decide : 0 < 5)
  let a := MulAut.congr e
  have ht' : (a t) ^ 2 = 1 := by
    have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
    rw [← map_pow, ht2, map_one]
  have hout' : a t ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    rintro ⟨g, hg⟩
    apply hout
    refine ⟨e.symm g, a.injective ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm g)) = a t
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hg
  let C := centralizer ({t} : Set (MulAut
    (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))))
  let D := centralizer ({a t} : Set (MulAut (LinearGroup 5)))
  let j : C →* D := (a.toMonoidHom.comp C.subtype).codRestrict D (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    exact (a.map_mul _ _).symm.trans
      ((congrArg a (mem_centralizer_singleton_iff.mp x.property)).trans (a.map_mul _ _)))
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (a.injective (congrArg Subtype.val h))
  exact (primeRank_le_of_injective 2 j hj).trans
    (linear_five_centralizer_rank_le_four (a t) ht' hout')

/-- The intrinsic model bound used in case (II) of the B.5.1 proof.
Both the noninner hypothesis and the centralizer refer to the literal full
automorphism group of the projective special linear carrier. -/
theorem psl_outer_involution_centralizer_rank_le_four
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (t : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
    (ht : orderOf t = 2)
    (hout : t ∉ MulAut.innerSubgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    primeRank 2 (centralizer ({t} : Set (MulAut
      (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))))) ≤ 4 := by
  rcases hn with rfl | rfl
  · exact psl4_centralizer_rank_le_four t
  · exact psl5_outer_involution_centralizer_rank_le_four t ht hout

end CFSG.Quasithin.ChapterB.QuasisimpleSource.OuterInvolutionRank
