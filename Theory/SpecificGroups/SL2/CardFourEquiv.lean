module

public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import GorensteinWalter.PSL2PerfectOfCard
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# PSL2 over the field of four elements

The faithful action on the five projective points identifies PSL2(4) with A5.
Perfection makes the sign of every permutation trivial, and both groups have
order sixty, so the resulting injection into A5 is surjective.

Source: the classical exceptional isomorphism PSL2(4) = A5, using the natural
projective-line action and the PSL2 order formula.
-/

open scoped LinearAlgebra.Projectivization

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The exceptional isomorphism PSL2(4) = A5, via its projective-line action. -/
public theorem equiv_alternatingGroup_of_card_four
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hK)
  let G := ProjectiveSpecialLinearGroup (Fin 2) K
  let Ω := ℙ K (Fin 2 → K)
  let : Fintype Ω := Fintype.ofFinite _
  have hΩ : Nat.card Ω = 5 := by
    change Nat.card (ℙ K (Fin 2 → K)) = 5
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hK]
  let eΩ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hΩ)
  let f : G →* Equiv.Perm (Fin 5) :=
    eΩ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Ω)
  have hf : Function.Injective f :=
    eΩ.permCongrHom.injective.comp MulAction.toPerm_injective
  let : Group.IsPerfect G :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three K (by omega)
  let sign : G →* ℤˣ := Equiv.Perm.sign.comp f
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  have hsign (g : G) : sign g = 1 := by
    exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict g) 1)
  let a : G →* alternatingGroup (Fin 5) := f.codRestrict _ (by
    intro g
    exact Equiv.Perm.mem_alternatingGroup.mpr (hsign g))
  have ha : Function.Injective a := by
    intro x y h
    exact hf (congrArg Subtype.val h)
  have hG : Nat.card G = 60 := by
    have h := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1), mul_one, hK] at h
    exact h
  refine ⟨MulEquiv.ofBijective a ((Nat.bijective_iff_injective_and_card a).mpr
    ⟨ha, ?_⟩)⟩
  rw [hG, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

end Matrix.ProjectiveSpecialLinearGroup
