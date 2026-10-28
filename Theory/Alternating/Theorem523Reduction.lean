module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public import Theory.Alternating.EvenBlock
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.TwoWreath -/
public section

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5.SchurPresentation

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The full two-block wreath product `(S_d × S_d) ⋊ S₂`. -/
public abbrev twoBlockWreathGroup (d : Nat) :=
  (Fin 2 → Equiv.Perm (Fin d)) ⋊[
    permuteCoordinatesHom (Fin 2) (Equiv.Perm (Fin d))
  ] Equiv.Perm (Fin 2)

/-- The product-to-sum relabelling used by the two-block wreath action. -/
@[expose]
public def twoWreathFinTwoProdEquivSum (d : Nat) :
    Fin 2 × Fin d ≃ Fin d ⊕ Fin d :=
  (finTwoEquiv.prodCongr (Equiv.refl (Fin d))).trans
    (Equiv.boolProdEquivSum (Fin d))

/-- The standard full two-block wreath action, relabelled onto `Fin (d + d)`. -/
@[expose]
public def twoBlockWreathFinPermHom (d : Nat) :
    twoBlockWreathGroup d →* Equiv.Perm (Fin (d + d)) :=
  (((twoWreathFinTwoProdEquivSum d).trans finSumFinEquiv).permCongrHom.toMonoidHom).comp
    (imprimitiveWreathPermHom (Fin 2) (Fin d))

public theorem twoBlockWreathFinPermHom_injective
    (d : Nat) [Nonempty (Fin d)] :
    Function.Injective (twoBlockWreathFinPermHom d) := by
  exact ((twoWreathFinTwoProdEquivSum d).trans finSumFinEquiv).permCongrHom.injective.comp
    imprimitiveWreathPermHom_injective

/-- Sign of the full wreath action. Its kernel is the index-two subgroup of
even permutations in the full wreath product. -/
@[expose]
public def twoBlockWreathSignHom (d : Nat) : twoBlockWreathGroup d →* ℤˣ :=
  Equiv.Perm.sign.comp (twoBlockWreathFinPermHom d)

public abbrev evenTwoBlockWreathGroup (d : Nat) :=
  (twoBlockWreathSignHom d).ker

/-- The even part of the full two-block wreath product, embedded in
`A_(d+d)`. -/
@[expose]
public def evenTwoBlockWreathFinHom (d : Nat) :
    evenTwoBlockWreathGroup d →* alternatingGroup (Fin (d + d)) :=
  ((twoBlockWreathFinPermHom d).comp
      (Subgroup.subtype (twoBlockWreathSignHom d).ker)).codRestrict _
    (fun x => Equiv.Perm.mem_alternatingGroup.mpr x.2)

public theorem evenTwoBlockWreathFinHom_injective
    (d : Nat) [Nonempty (Fin d)] :
    Function.Injective (evenTwoBlockWreathFinHom d) := by
  intro x y hxy
  apply Subtype.ext
  apply twoBlockWreathFinPermHom_injective d
  exact congrArg Subtype.val hxy

public theorem twoBlockWreathFinPermHom_sign_inl (d : Nat)
    (h : Fin 2 → Equiv.Perm (Fin d)) :
    Equiv.Perm.sign
        (twoBlockWreathFinPermHom d (SemidirectProduct.inl h)) =
      ∏ i, Equiv.Perm.sign (h i) := by
  rw [twoBlockWreathFinPermHom, MonoidHom.comp_apply]
  change Equiv.Perm.sign
      (((twoWreathFinTwoProdEquivSum d).trans finSumFinEquiv).permCongr
        (imprimitiveWreathPermHom (Fin 2) (Fin d)
          (SemidirectProduct.inl h))) = _
  rw [Equiv.Perm.sign_permCongr]
  have heq :
      imprimitiveWreathPermHom (Fin 2) (Fin d)
          (SemidirectProduct.inl h) =
        blockBasePermHom (Fin 2) (Fin d) h := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    simp
  rw [heq]
  exact Equiv.Perm.sign_prodCongrRight h

public theorem twoBlockWreathFinPermHom_sign (d : Nat)
    (x : twoBlockWreathGroup d) :
    Equiv.Perm.sign (twoBlockWreathFinPermHom d x) =
      (∏ i, Equiv.Perm.sign (x.left i)) *
        Equiv.Perm.sign x.right ^ d := by
  rw [twoBlockWreathFinPermHom, MonoidHom.comp_apply]
  change Equiv.Perm.sign
      (((twoWreathFinTwoProdEquivSum d).trans finSumFinEquiv).permCongr
        (imprimitiveWreathPermHom (Fin 2) (Fin d) x)) = _
  rw [Equiv.Perm.sign_permCongr]
  have heq : imprimitiveWreathPermHom (Fin 2) (Fin d) x =
      blockBasePermHom (Fin 2) (Fin d) x.left *
        blockTopPermHom (Fin 2) (Fin d) x.right := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    simp [imprimitiveWreathPermHom_apply, Equiv.Perm.mul_apply]
  rw [heq, Equiv.Perm.sign_mul]
  have hbaseSign :
      Equiv.Perm.sign (blockBasePermHom (Fin 2) (Fin d) x.left) =
        ∏ i, Equiv.Perm.sign (x.left i) := by
    change Equiv.Perm.sign (Equiv.prodCongrRight x.left) = _
    exact Equiv.Perm.sign_prodCongrRight x.left
  have htopSign :
      Equiv.Perm.sign (blockTopPermHom (Fin 2) (Fin d) x.right) =
        Equiv.Perm.sign x.right ^ d := by
    change Equiv.Perm.sign
      (Equiv.prodCongrLeft (fun _ : Fin d => x.right)) = _
    simpa using Equiv.Perm.sign_prodCongrLeft (fun _ : Fin d => x.right)
  rw [hbaseSign, htopSign]

public theorem twoBlockWreathSignHom_surjective (d : Nat) (hd : 2 ≤ d) :
    Function.Surjective (twoBlockWreathSignHom d) := by
  let x0 : Fin d := ⟨0, by omega⟩
  let x1 : Fin d := ⟨1, by omega⟩
  have hx : x0 ≠ x1 := by
    intro h
    exact zero_ne_one (congrArg Fin.val h)
  let τ : Equiv.Perm (Fin d) := Equiv.swap x0 x1
  let b : Fin 2 → Equiv.Perm (Fin d) := Pi.mulSingle 0 τ
  let t : twoBlockWreathGroup d := SemidirectProduct.inl b
  have ht : twoBlockWreathSignHom d t = -1 := by
    rw [twoBlockWreathSignHom, MonoidHom.comp_apply,
      twoBlockWreathFinPermHom_sign_inl]
    simp [b, τ, Pi.mulSingle, Equiv.Perm.sign_swap hx]
  intro z
  rcases Int.units_eq_one_or z with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨t, ht⟩

public theorem twoBlockWreathGroup_card (d : Nat) :
    Nat.card (twoBlockWreathGroup d) = d.factorial ^ 2 * 2 := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_fin, Nat.card_perm,
    Nat.card_fin]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

public theorem evenTwoBlockWreathGroup_card (d : Nat) (hd : 2 ≤ d) :
    Nat.card (evenTwoBlockWreathGroup d) = d.factorial ^ 2 := by
  have hrange : (twoBlockWreathSignHom d).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (twoBlockWreathSignHom_surjective d hd)
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hcard := (twoBlockWreathSignHom d).ker.card_mul_index
  rw [Subgroup.index_ker, hrange, Subgroup.card_top,
    hunits, twoBlockWreathGroup_card] at hcard
  exact Nat.mul_right_cancel (by decide) hcard

public theorem evenTwoBlockWreathGroup_factorization_eq_ambient
    (s : Nat) (hs : 0 < s) :
    (Nat.card (evenTwoBlockWreathGroup (2 ^ s))).factorization 2 =
      (Nat.card (alternatingGroup (Fin (2 ^ s + 2 ^ s)))).factorization 2 := by
  let d := 2 ^ s
  have hd2 : 2 ≤ d := by
    simpa only [d, pow_one] using
      (pow_le_pow_right₀ (show 1 ≤ 2 by decide) hs)
  let : Nontrivial (Fin (d + d)) :=
    Fin.nontrivial_iff_two_le.mpr (by omega)
  have hambient :
      1 + (Nat.card (alternatingGroup (Fin (d + d)))).factorization 2 =
        (d + d).factorial.factorization 2 := by
    have h := congrArg (fun m : Nat => m.factorization 2)
      (two_mul_nat_card_alternatingGroup (α := Fin (d + d)))
    rw [Nat.factorization_mul (by decide) Nat.card_pos.ne'] at h
    simpa [Finsupp.add_apply, Nat.prime_two.factorization_self,
      Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card,
      Fintype.card_perm] using h
  have hfactorial :
      (d + d).factorial.factorization 2 =
        d.factorial.factorization 2 + d := by
    rw [show d + d = 2 * d by omega]
    exact Nat.factorization_factorial_mul Nat.prime_two
  have hrelation := factorial_power_factorization_relation 2 s Nat.prime_two
  change 2 * d.factorial.factorization 2 + 1 =
    d.factorial.factorization 2 + d at hrelation
  change (Nat.card (evenTwoBlockWreathGroup d)).factorization 2 =
    (Nat.card (alternatingGroup (Fin (d + d)))).factorization 2
  rw [evenTwoBlockWreathGroup_card d hd2, Nat.factorization_pow,
    Finsupp.smul_apply, nsmul_eq_mul]
  omega

/-- For `d = 2^s`, the even full two-block wreath subgroup of `A_(d+d)`
contains an ambient Sylow `2`-subgroup. -/
public theorem exists_sylow_two_le_evenTwoBlockWreathFinHom_range
    (s : Nat) (hs : 0 < s) :
    ∃ P : Sylow 2 (alternatingGroup (Fin (2 ^ s + 2 ^ s))),
      (P : Subgroup (alternatingGroup (Fin (2 ^ s + 2 ^ s)))) ≤
        (evenTwoBlockWreathFinHom (2 ^ s)).range := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nonempty (Fin (2 ^ s)) :=
    ⟨⟨0, pow_pos (by decide) s⟩⟩
  let : Finite (twoBlockWreathGroup (2 ^ s)) :=
    Finite.of_equiv
      ((Fin 2 → Equiv.Perm (Fin (2 ^ s))) × Equiv.Perm (Fin 2))
      (SemidirectProduct.equivProd
        (φ := permuteCoordinatesHom (Fin 2)
          (Equiv.Perm (Fin (2 ^ s))))).symm
  let Q : Sylow 2 (evenTwoBlockWreathGroup (2 ^ s)) :=
    Classical.choice Sylow.nonempty
  let H : Subgroup (alternatingGroup (Fin (2 ^ s + 2 ^ s))) :=
    (Q : Subgroup (evenTwoBlockWreathGroup (2 ^ s))).map
      (evenTwoBlockWreathFinHom (2 ^ s))
  have hinj : Function.Injective (evenTwoBlockWreathFinHom (2 ^ s)) :=
    evenTwoBlockWreathFinHom_injective (2 ^ s)
  have hHcard : Nat.card H =
      2 ^ (Nat.card
        (alternatingGroup (Fin (2 ^ s + 2 ^ s)))).factorization 2 := by
    change Nat.card
        ((Q : Subgroup (evenTwoBlockWreathGroup (2 ^ s))).map
          (evenTwoBlockWreathFinHom (2 ^ s))) = _
    rw [Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity Q,
      evenTwoBlockWreathGroup_factorization_eq_ambient s hs]
  let P : Sylow 2 (alternatingGroup (Fin (2 ^ s + 2 ^ s))) :=
    Sylow.ofCard H hHcard
  refine ⟨P, ?_⟩
  change H ≤ (evenTwoBlockWreathFinHom (2 ^ s)).range
  exact Subgroup.map_le_range _ _

/-- Put a pair of permutations into the two base coordinates. -/
@[expose]
public def twoBlockBasePairHom (d : Nat) :
    Equiv.Perm (Fin d) × Equiv.Perm (Fin d) →*
      (Fin 2 → Equiv.Perm (Fin d)) where
  toFun x i := if i = 0 then x.1 else x.2
  map_one' := by
    funext i
    split_ifs <;> rfl
  map_mul' x y := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

/-- The ordered base inside the full two-block wreath product. -/
@[expose]
public def twoBlockWreathBaseHom (d : Nat) :
    Equiv.Perm (Fin d) × Equiv.Perm (Fin d) →* twoBlockWreathGroup d :=
  SemidirectProduct.inl.comp (twoBlockBasePairHom d)

/-- The parity-correlated ordered block group inside the even full wreath
group. -/
@[expose]
public def evenBlockToEvenTwoWreathHom (d : Nat) :
    evenBlockProductGroup d d →* evenTwoBlockWreathGroup d :=
  ((twoBlockWreathBaseHom d).comp
      (Subgroup.subtype (evenBlockProductGroup d d))).codRestrict _ (fun x => by
    change twoBlockWreathSignHom d
      (twoBlockWreathBaseHom d (x : Equiv.Perm (Fin d) ×
        Equiv.Perm (Fin d))) = 1
    rw [twoBlockWreathSignHom, MonoidHom.comp_apply,
      twoBlockWreathBaseHom, MonoidHom.comp_apply,
      twoBlockWreathFinPermHom_sign_inl]
    have hx := x.2
    change Equiv.Perm.sign (permProdBlockHom d d x.1) = 1 at hx
    rw [permProdBlockHom_apply, Equiv.Perm.sign_permCongr,
      Equiv.Perm.sign_sumCongr] at hx
    simpa [twoBlockBasePairHom] using hx)

public theorem twoBlockWreathBaseHom_injective (d : Nat) :
    Function.Injective (twoBlockWreathBaseHom d) := by
  intro x y hxy
  have hbase := congrArg SemidirectProduct.left hxy
  apply Prod.ext
  · simpa [twoBlockWreathBaseHom, twoBlockBasePairHom] using
      congrFun hbase (0 : Fin 2)
  · simpa [twoBlockWreathBaseHom, twoBlockBasePairHom] using
      congrFun hbase (1 : Fin 2)

public theorem evenBlockToEvenTwoWreathHom_injective (d : Nat) :
    Function.Injective (evenBlockToEvenTwoWreathHom d) := by
  intro x y hxy
  apply Subtype.ext
  apply twoBlockWreathBaseHom_injective d
  exact congrArg Subtype.val hxy

public theorem twoBlockWreathBaseHom_ambient (d : Nat)
    (x : Equiv.Perm (Fin d) × Equiv.Perm (Fin d)) :
    twoBlockWreathFinPermHom d (twoBlockWreathBaseHom d x) =
      permProdBlockHom d d x := by
  have hbase :
      imprimitiveWreathPermHom (Fin 2) (Fin d)
          (twoBlockWreathBaseHom d x) =
        blockBasePermHom (Fin 2) (Fin d) (twoBlockBasePairHom d x) := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    simp [twoBlockWreathBaseHom, imprimitiveWreathPermHom_apply]
  rw [twoBlockWreathFinPermHom, MonoidHom.comp_apply]
  change ((twoWreathFinTwoProdEquivSum d).trans finSumFinEquiv).permCongr
      (imprimitiveWreathPermHom (Fin 2) (Fin d)
        (twoBlockWreathBaseHom d x)) = _
  rw [hbase]
  have hzero : finTwoEquiv (0 : Fin 2) = false := by decide
  have hone : finTwoEquiv (1 : Fin 2) = true := by decide
  have hsymmFalse : finTwoEquiv.symm false = (0 : Fin 2) := by decide
  have hsymmTrue : finTwoEquiv.symm true = (1 : Fin 2) := by decide
  have hsum :
      (twoWreathFinTwoProdEquivSum d).permCongr
          (blockBasePermHom (Fin 2) (Fin d) (twoBlockBasePairHom d x)) =
        Equiv.sumCongr x.1 x.2 := by
    apply Equiv.ext
    intro z
    rcases z with a | a <;>
      simp [twoWreathFinTwoProdEquivSum, twoBlockBasePairHom,
        hzero, hone, hsymmFalse, hsymmTrue]
  calc
    _ = finSumFinEquiv.permCongr
        ((twoWreathFinTwoProdEquivSum d).permCongr
          (blockBasePermHom (Fin 2) (Fin d) (twoBlockBasePairHom d x))) := by
      exact (DFunLike.congr_fun
        (Equiv.permCongrHom_trans (twoWreathFinTwoProdEquivSum d)
          finSumFinEquiv)
        (blockBasePermHom (Fin 2) (Fin d) (twoBlockBasePairHom d x))).symm
    _ = finSumFinEquiv.permCongr (Equiv.sumCongr x.1 x.2) := by rw [hsum]
    _ = permProdBlockHom d d x := by rw [permProdBlockHom_apply]

public theorem evenBlockToEvenTwoWreathHom_ambient (d : Nat)
    (x : evenBlockProductGroup d d) :
    evenTwoBlockWreathFinHom d (evenBlockToEvenTwoWreathHom d x) =
      evenBlockProductHom d d x := by
  apply Subtype.ext
  exact twoBlockWreathBaseHom_ambient d x.1

/-- Extend a permutation of the first two points by the identity. -/
@[expose]
public def twoWreathFirstTwoPermHom (d : Nat) (hd : 2 ≤ d) :
    Equiv.Perm (Fin 2) →* Equiv.Perm (Fin d) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hd)

/-- Raw Klein-four section: the first factor acts by the same first-two-point
permutation in both blocks, and the second factor permutes the blocks. -/
@[expose]
public def twoWreathKleinFourRawHom (d : Nat) (hd : 2 ≤ d) :
    Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) →* twoBlockWreathGroup d where
  toFun x := ⟨fun _ => twoWreathFirstTwoPermHom d hd x.1, x.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext i
      simp [twoWreathFirstTwoPermHom]
    · simp
  map_mul' x y := by
    apply SemidirectProduct.ext
    · funext i
      simp [permuteCoordinatesHom_apply]
    · simp

/-- The Klein-four section of the quotient of the even wreath group by
`A_d × A_d`. -/
@[expose]
public def twoWreathKleinFourHom (d : Nat) (hd : 2 ≤ d) (heven : Even d) :
    Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) →*
      evenTwoBlockWreathGroup d :=
  (twoWreathKleinFourRawHom d hd).codRestrict _ (fun x => by
    change Equiv.Perm.sign
      (twoBlockWreathFinPermHom d (twoWreathKleinFourRawHom d hd x)) = 1
    rw [twoBlockWreathFinPermHom_sign]
    have hbase :
        Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1) *
            Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1) = 1 := by
      rcases Int.units_eq_one_or
          (Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1)) with h | h <;>
        simp [h]
    have htop : Equiv.Perm.sign x.2 ^ d = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign x.2) with h | h
      · simp [h]
      · rw [h]
        exact (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mpr heven
    rw [Fin.prod_univ_two]
    change (Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1) *
        Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1)) *
          Equiv.Perm.sign x.2 ^ d = 1
    rw [hbase, htop, mul_one])

public theorem twoWreathKleinFourHom_injective
    (d : Nat) (hd : 2 ≤ d) (heven : Even d) :
    Function.Injective (twoWreathKleinFourHom d hd heven) := by
  intro x y hxy
  have hraw := congrArg Subtype.val hxy
  apply Prod.ext
  · apply Equiv.Perm.viaEmbeddingHom_injective
    have hleft := congrArg SemidirectProduct.left hraw
    simpa [twoWreathKleinFourHom, twoWreathKleinFourRawHom,
      twoWreathFirstTwoPermHom] using congrFun hleft (0 : Fin 2)
  · exact congrArg SemidirectProduct.right hraw

public theorem sign_twoWreathFirstTwoPermHom (d : Nat) (hd : 2 ≤ d)
    (x : Equiv.Perm (Fin 2)) :
    Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x) =
      Equiv.Perm.sign x := by
  simp [twoWreathFirstTwoPermHom, Equiv.Perm.viaEmbeddingHom,
    Equiv.Perm.sign_extendDomain]

/-- The alternating base `A_d × A_d` in the even wreath group. -/
@[expose]
public def evenTwoBlockWreathBaseHom (d : Nat) :
    alternatingGroup (Fin d) × alternatingGroup (Fin d) →*
      evenTwoBlockWreathGroup d :=
  (evenBlockToEvenTwoWreathHom d).comp (evenBlockAlternatingHom d d)

public abbrev evenTwoBlockWreathBase (d : Nat) :
    Subgroup (evenTwoBlockWreathGroup d) :=
  (evenTwoBlockWreathBaseHom d).range

public abbrev twoWreathKleinFour
    (d : Nat) (hd : 2 ≤ d) (heven : Even d) :
    Subgroup (evenTwoBlockWreathGroup d) :=
  (twoWreathKleinFourHom d hd heven).range

public theorem twoWreathKleinFour_inf_base_eq_bot
    (d : Nat) (hd : 2 ≤ d) (heven : Even d) :
    twoWreathKleinFour d hd heven ⊓ evenTwoBlockWreathBase d = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  rcases hz.1 with ⟨x, hx⟩
  rcases hz.2 with ⟨y, hy⟩
  have hxy : twoWreathKleinFourHom d hd heven x =
      evenTwoBlockWreathBaseHom d y := hx.trans hy.symm
  have hraw := congrArg Subtype.val hxy
  have hx2 : x.2 = 1 := by
    have hright := congrArg SemidirectProduct.right hraw
    simpa [twoWreathKleinFourHom, twoWreathKleinFourRawHom,
      evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
      twoBlockWreathBaseHom, evenBlockAlternatingHom] using hright
  have hfirst : twoWreathFirstTwoPermHom d hd x.1 = y.1.1 := by
    have hleft := congrArg SemidirectProduct.left hraw
    simpa [twoWreathKleinFourHom, twoWreathKleinFourRawHom,
      evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
      twoBlockWreathBaseHom, twoBlockBasePairHom,
      evenBlockAlternatingHom] using congrFun hleft (0 : Fin 2)
  have hsign : Equiv.Perm.sign x.1 = 1 := by
    calc
      Equiv.Perm.sign x.1 =
          Equiv.Perm.sign (twoWreathFirstTwoPermHom d hd x.1) :=
        (sign_twoWreathFirstTwoPermHom d hd x.1).symm
      _ = Equiv.Perm.sign y.1.1 := congrArg Equiv.Perm.sign hfirst
      _ = 1 := y.1.2
  have hcard : Nat.card (alternatingGroup (Fin 2)) = 1 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hsub : Subsingleton (alternatingGroup (Fin 2)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have hx1 : x.1 = 1 := by
    exact congrArg Subtype.val
      (hsub.elim (⟨x.1, hsign⟩ : alternatingGroup (Fin 2)) 1)
  have hxone : x = 1 := Prod.ext hx1 hx2
  calc
    z = twoWreathKleinFourHom d hd heven x := hx.symm
    _ = twoWreathKleinFourHom d hd heven 1 := by rw [hxone]
    _ = 1 := map_one _

public theorem exists_twoWreathKleinFour_mul_base
    (d : Nat) (hd : 2 ≤ d) (heven : Even d)
    (z : evenTwoBlockWreathGroup d) :
    ∃ x : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2),
      ∃ y : alternatingGroup (Fin d) × alternatingGroup (Fin d),
        twoWreathKleinFourHom d hd heven x *
          evenTwoBlockWreathBaseHom d y = z := by
  let w : twoBlockWreathGroup d := z.1
  obtain ⟨σ, hσ⟩ := Equiv.Perm.sign_surjective (Fin 2)
    (Equiv.Perm.sign (w.left (w.right 0)))
  let x : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) := ⟨σ, w.right⟩
  let b : evenTwoBlockWreathGroup d :=
    twoWreathKleinFourHom d hd heven x
  let r : evenTwoBlockWreathGroup d := b⁻¹ * z
  have hright : r.1.right = 1 := by
    simp [r, b, x, w, twoWreathKleinFourHom,
      twoWreathKleinFourRawHom]
  have hcoord (f : Fin 2 → Equiv.Perm (Fin d)) (i : Fin 2) :
      (permuteCoordinatesHom (Fin 2) (Equiv.Perm (Fin d)) w.right).symm f i =
        f (w.right i) := by
    rfl
  have hleft0 : r.1.left 0 =
      (twoWreathFirstTwoPermHom d hd σ)⁻¹ *
        w.left (w.right 0) := by
    simp [r, b, x, w, twoWreathKleinFourHom,
      twoWreathKleinFourRawHom, hcoord]
  have hr0 : Equiv.Perm.sign (r.1.left 0) = 1 := by
    rw [hleft0, Equiv.Perm.sign_mul, map_inv,
      sign_twoWreathFirstTwoPermHom, hσ]
    simp
  have hrsign := r.2
  change Equiv.Perm.sign (twoBlockWreathFinPermHom d r.1) = 1 at hrsign
  rw [twoBlockWreathFinPermHom_sign, Fin.prod_univ_two, hright] at hrsign
  simp only [Equiv.Perm.sign_one, one_pow, mul_one] at hrsign
  have hr1 : Equiv.Perm.sign (r.1.left 1) = 1 := by
    rw [hr0, one_mul] at hrsign
    exact hrsign
  let y0 : alternatingGroup (Fin d) := ⟨r.1.left 0, hr0⟩
  let y1 : alternatingGroup (Fin d) := ⟨r.1.left 1, hr1⟩
  let y : alternatingGroup (Fin d) × alternatingGroup (Fin d) := ⟨y0, y1⟩
  have hy : evenTwoBlockWreathBaseHom d y = r := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · funext i
      fin_cases i <;>
        simp [evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
          evenBlockAlternatingHom, twoBlockWreathBaseHom,
          twoBlockBasePairHom, y, y0, y1]
    · simpa [evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
        evenBlockAlternatingHom, twoBlockWreathBaseHom] using hright.symm
  refine ⟨x, y, ?_⟩
  rw [hy]
  change b * (b⁻¹ * z) = z
  group

public def twoWreathTensorAssoc (m : Nat) :
    Fin 2 × Fin (2 * m) ≃ (Fin 2 × Fin 2) × Fin m :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv.symm).trans
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin m)).symm

/-- The tensor-coordinate flip `(i, (j, a)) ↦ (j, (i, a))`. -/
public def twoWreathTensorFlipProd (m : Nat) : Equiv.Perm (Fin 2 × Fin (2 * m)) :=
  (twoWreathTensorAssoc m).symm.permCongr
    (Equiv.prodCongrLeft (fun _ : Fin m => Equiv.prodComm (Fin 2) (Fin 2)))

/-- The tensor-coordinate flip, relabelled on the standard `Fin` model. -/
public def twoWreathTensorFlip (m : Nat) : Equiv.Perm (Fin ((2 * m) + (2 * m))) :=
  ((twoWreathFinTwoProdEquivSum (2 * m)).trans finSumFinEquiv).permCongr
    (twoWreathTensorFlipProd m)

public theorem sign_twoWreathTensorFlipProd (m : Nat) :
    Equiv.Perm.sign (twoWreathTensorFlipProd m) = (-1 : ℤˣ) ^ m := by
  rw [twoWreathTensorFlipProd, Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_prodCongrLeft]
  have hcomm : Equiv.Perm.sign (Equiv.prodComm (Fin 2) (Fin 2)) = (-1 : ℤˣ) := by
    all_goals decide
  simp [hcomm]

public theorem twoWreathTensorFlip_mem_alternatingGroup (m : Nat) (hm : Even m) :
    twoWreathTensorFlip m ∈ alternatingGroup (Fin ((2 * m) + (2 * m))) := by
  rw [Equiv.Perm.mem_alternatingGroup, twoWreathTensorFlip,
    Equiv.Perm.sign_permCongr, sign_twoWreathTensorFlipProd]
  obtain ⟨k, rfl⟩ := hm
  rw [show k + k = 2 * k by omega]
  calc
    (-1 : ℤˣ) ^ (2 * k) = ((-1 : ℤˣ) ^ 2) ^ k := pow_mul _ _ _
    _ = 1 := by norm_num

theorem twoWreathViaEmbedding_finProdFinEquiv (m : Nat) (hm : 2 ≤ m)
    (p : Equiv.Perm (Fin 2)) (j : Fin 2) (a : Fin m) :
    (p.viaEmbedding (Fin.castLEEmb (by omega : 2 ≤ 2 * m))) (finProdFinEquiv (j, a)) =
      finProdFinEquiv
        (j, if j = 0 then p.viaEmbedding (Fin.castLEEmb hm) a else a) := by
  fin_cases j
  · simp only [Fin.zero_eta, ↓reduceIte]
    by_cases ha : a.val < 2
    · let b : Fin 2 := ⟨a.val, ha⟩
      have hab : Fin.castLE hm b = a := by ext; rfl
      rw [← hab]
      have hx : finProdFinEquiv ((0 : Fin 2), Fin.castLE hm b) =
          Fin.castLE (by omega : 2 ≤ 2 * m) b := by
        apply Fin.ext
        simp [finProdFinEquiv_apply_val]
      rw [hx]
      change
        (p.viaEmbedding (Fin.castLEEmb (by omega : 2 ≤ 2 * m)))
            ((Fin.castLEEmb (by omega : 2 ≤ 2 * m)) b) =
          finProdFinEquiv
            ((0 : Fin 2), (p.viaEmbedding (Fin.castLEEmb hm)) ((Fin.castLEEmb hm) b))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply]
      apply Fin.ext
      simp [finProdFinEquiv_apply_val]
    · have haSmall : a ∉ Set.range (Fin.castLEEmb hm) := by
        simpa [Fin.coe_castLEEmb, Fin.range_castLE] using ha
      have haLarge : finProdFinEquiv ((0 : Fin 2), a) ∉
          Set.range (Fin.castLEEmb (by omega : 2 ≤ 2 * m)) := by
        simpa [Fin.coe_castLEEmb, Fin.range_castLE, finProdFinEquiv_apply_val] using ha
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ haLarge,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ haSmall]
  · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte]
    have haLarge : finProdFinEquiv ((1 : Fin 2), a) ∉
        Set.range (Fin.castLEEmb (by omega : 2 ≤ 2 * m)) := by
      rw [Fin.coe_castLEEmb, Fin.range_castLE]
      simp only [Set.mem_ofPred_eq, finProdFinEquiv_apply_val]
      omega
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ haLarge]

@[simp] theorem twoWreathTensorFlipProd_apply (m : Nat) (i j : Fin 2) (a : Fin m) :
    twoWreathTensorFlipProd m (i, finProdFinEquiv (j, a)) =
      (j, finProdFinEquiv (i, a)) := by
  simp [twoWreathTensorFlipProd, twoWreathTensorAssoc]

@[simp] theorem twoWreathTensorFlipProd_symm_apply (m : Nat) (i j : Fin 2) (a : Fin m) :
    (twoWreathTensorFlipProd m).symm (i, finProdFinEquiv (j, a)) =
      (j, finProdFinEquiv (i, a)) := by
  apply (twoWreathTensorFlipProd m).injective
  simp

noncomputable def twoWreathRawElement (m : Nat) (hm : 2 ≤ m)
    (p q : Equiv.Perm (Fin 2)) :
    (Fin 2 → Equiv.Perm (Fin (2 * m))) ⋊[
      permuteCoordinatesHom (Fin 2) (Equiv.Perm (Fin (2 * m)))] Equiv.Perm (Fin 2) :=
  ⟨fun _ => p.viaEmbedding (Fin.castLEEmb (by omega : 2 ≤ 2 * m)), q⟩

noncomputable def twoWreathNewBlockPerm (m : Nat) (hm : 2 ≤ m) (j : Fin 2)
    (p q : Equiv.Perm (Fin 2)) : Equiv.Perm (Fin (2 * m)) :=
  finProdFinEquiv.permCongr
    (Equiv.prodCongrLeft (fun _ : Fin m => q) *
      Equiv.prodCongrRight (fun _ : Fin 2 =>
        if j = 0 then p.viaEmbedding (Fin.castLEEmb hm) else 1))

@[simp] theorem twoWreathNewBlockPerm_apply (m : Nat) (hm : 2 ≤ m) (j i : Fin 2)
    (a : Fin m) (p q : Equiv.Perm (Fin 2)) :
    twoWreathNewBlockPerm m hm j p q (finProdFinEquiv (i, a)) =
      finProdFinEquiv
        (q i, if j = 0 then p.viaEmbedding (Fin.castLEEmb hm) a else a) := by
  simp [twoWreathNewBlockPerm, Equiv.Perm.mul_apply]
  split_ifs <;> simp_all

noncomputable def twoWreathBaseElement (m : Nat) (hm : 2 ≤ m)
    (p q : Equiv.Perm (Fin 2)) :
    (Fin 2 → Equiv.Perm (Fin (2 * m))) ⋊[
      permuteCoordinatesHom (Fin 2) (Equiv.Perm (Fin (2 * m)))] Equiv.Perm (Fin 2) :=
  ⟨fun j => twoWreathNewBlockPerm m hm j p q, 1⟩

theorem twoWreathTensorFlipProd_conj_raw (m : Nat) (hm : 2 ≤ m)
    (p q : Equiv.Perm (Fin 2)) :
    twoWreathTensorFlipProd m *
          imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
            (twoWreathRawElement m hm p q) *
        (twoWreathTensorFlipProd m)⁻¹ =
      imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
        (twoWreathBaseElement m hm p q) := by
  apply Equiv.ext
  rintro ⟨j, x⟩
  generalize hia : finProdFinEquiv.symm x = ia
  rcases ia with ⟨i, a⟩
  have hx : x = finProdFinEquiv (i, a) := by
    calc
      x = finProdFinEquiv (finProdFinEquiv.symm x) :=
        (finProdFinEquiv.apply_symm_apply x).symm
      _ = finProdFinEquiv (i, a) := congrArg finProdFinEquiv hia
  rw [hx]
  change
    twoWreathTensorFlipProd m
        (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
          (twoWreathRawElement m hm p q)
          ((twoWreathTensorFlipProd m).symm (j, finProdFinEquiv (i, a)))) =
      imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
        (twoWreathBaseElement m hm p q) (j, finProdFinEquiv (i, a))
  simp [imprimitiveWreathPermHom_apply, twoWreathRawElement,
    twoWreathBaseElement]
  rw [twoWreathViaEmbedding_finProdFinEquiv m hm p j a]
  simp

theorem viaEmbedding_eq_viaFintypeEmbedding {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (p : Equiv.Perm α) (f : α ↪ β) :
    p.viaEmbedding f = p.viaFintypeEmbedding f := by
  apply Equiv.ext
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [Equiv.Perm.viaEmbedding_apply,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hb,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hb]

theorem twoWreathNewBlockPerm_mem_alternatingGroup (m : Nat) (hm : 2 ≤ m)
    (hmEven : Even m) (j : Fin 2) (p q : Equiv.Perm (Fin 2)) :
    twoWreathNewBlockPerm m hm j p q ∈ alternatingGroup (Fin (2 * m)) := by
  rw [Equiv.Perm.mem_alternatingGroup, twoWreathNewBlockPerm,
    Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight]
  have hqpow : Equiv.Perm.sign q ^ m = 1 := by
    obtain ⟨k, rfl⟩ := hmEven
    rw [show k + k = 2 * k by omega]
    calc
      Equiv.Perm.sign q ^ (2 * k) = (Equiv.Perm.sign q ^ 2) ^ k := pow_mul _ _ _
      _ = 1 := by rw [Int.units_pow_two, one_pow]
  have hp : Equiv.Perm.sign (p.viaEmbedding (Fin.castLEEmb hm)) =
      Equiv.Perm.sign p := by
    rw [viaEmbedding_eq_viaFintypeEmbedding]
    exact Equiv.Perm.viaFintypeEmbedding_sign p (Fin.castLEEmb hm)
  fin_cases j <;> simp [hp] <;> exact hqpow

theorem twoWreathRawElement_eq_twoWreathKleinFourRawHom (m : Nat) (hm : 2 ≤ m)
    (p q : Equiv.Perm (Fin 2)) :
    twoWreathRawElement m hm p q =
      twoWreathKleinFourRawHom (2 * m) (by omega) (p, q) := by
  rfl

noncomputable def twoWreathBasePair (m : Nat) (hm : 2 ≤ m) (hmEven : Even m)
    (p q : Equiv.Perm (Fin 2)) :
    alternatingGroup (Fin (2 * m)) × alternatingGroup (Fin (2 * m)) :=
  (⟨twoWreathNewBlockPerm m hm 0 p q,
      twoWreathNewBlockPerm_mem_alternatingGroup m hm hmEven 0 p q⟩,
    ⟨twoWreathNewBlockPerm m hm 1 p q,
      twoWreathNewBlockPerm_mem_alternatingGroup m hm hmEven 1 p q⟩)

theorem twoWreathBasePair_eq_evenTwoBlockWreathBaseHom (m : Nat) (hm : 2 ≤ m)
    (hmEven : Even m) (p q : Equiv.Perm (Fin 2)) :
    (evenTwoBlockWreathBaseHom (2 * m) (twoWreathBasePair m hm hmEven p q)).1 =
      twoWreathBaseElement m hm p q := by
  simp [evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
    evenBlockAlternatingHom, twoBlockWreathBaseHom, twoBlockBasePairHom,
    twoWreathBasePair, twoWreathBaseElement]
  funext j
  fin_cases j <;> simp

theorem twoWreathKleinFourHom_val_eq_raw (m : Nat) (hm : 2 ≤ m)
    (_hmEven : Even m) (p q : Equiv.Perm (Fin 2)) :
    (twoWreathKleinFourHom (2 * m) (by omega) (⟨m, by omega⟩) (p, q)).1 =
      twoWreathRawElement m hm p q := by
  rfl

theorem twoWreathTensorFlip_conj_evenKleinFour (m : Nat) (hm : 2 ≤ m)
    (hmEven : Even m) (p q : Equiv.Perm (Fin 2)) :
    ∃ y : alternatingGroup (Fin (2 * m)) × alternatingGroup (Fin (2 * m)),
      (⟨twoWreathTensorFlip m, twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩ :
          alternatingGroup (Fin ((2 * m) + (2 * m)))) *
          evenTwoBlockWreathFinHom (2 * m)
            (twoWreathKleinFourHom (2 * m) (by omega) (⟨m, by omega⟩) (p, q)) *
        (⟨twoWreathTensorFlip m, twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩ :
          alternatingGroup (Fin ((2 * m) + (2 * m))))⁻¹ =
      evenTwoBlockWreathFinHom (2 * m)
        (evenTwoBlockWreathBaseHom (2 * m) y) := by
  refine ⟨twoWreathBasePair m hm hmEven p q, ?_⟩
  apply Subtype.ext
  change
    twoWreathTensorFlip m *
        twoBlockWreathFinPermHom (2 * m)
          ((twoWreathKleinFourHom (2 * m) (by omega) (⟨m, by omega⟩) (p, q)).1) *
      (twoWreathTensorFlip m)⁻¹ =
      twoBlockWreathFinPermHom (2 * m)
        ((evenTwoBlockWreathBaseHom (2 * m)
          (twoWreathBasePair m hm hmEven p q)).1)
  rw [twoWreathKleinFourHom_val_eq_raw m hm hmEven p q,
    twoWreathBasePair_eq_evenTwoBlockWreathBaseHom m hm hmEven p q]
  let e := (twoWreathFinTwoProdEquivSum (2 * m)).trans finSumFinEquiv
  change
    e.permCongr (twoWreathTensorFlipProd m) *
        e.permCongr (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
          (twoWreathRawElement m hm p q)) *
      (e.permCongr (twoWreathTensorFlipProd m))⁻¹ =
      e.permCongr (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
        (twoWreathBaseElement m hm p q))
  have hinv : (e.permCongr (twoWreathTensorFlipProd m))⁻¹ =
      e.permCongr (twoWreathTensorFlipProd m)⁻¹ := by
    exact (map_inv e.permCongrHom (twoWreathTensorFlipProd m)).symm
  calc
    e.permCongr (twoWreathTensorFlipProd m) *
          e.permCongr (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
            (twoWreathRawElement m hm p q)) *
        (e.permCongr (twoWreathTensorFlipProd m))⁻¹ =
        e.permCongr (twoWreathTensorFlipProd m) *
          e.permCongr (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
            (twoWreathRawElement m hm p q)) *
          e.permCongr (twoWreathTensorFlipProd m)⁻¹ := by rw [hinv]
    _ = e.permCongr
          (twoWreathTensorFlipProd m *
            imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
              (twoWreathRawElement m hm p q) *
            (twoWreathTensorFlipProd m)⁻¹) := by
      rw [← e.permCongr_mul, ← e.permCongr_mul]
    _ = e.permCongr (imprimitiveWreathPermHom (Fin 2) (Fin (2 * m))
          (twoWreathBaseElement m hm p q)) := by
      rw [twoWreathTensorFlipProd_conj_raw]

theorem permCongr_conj {α β : Type*} (e : α ≃ β) (c x : Equiv.Perm α) :
    e.permCongr c * e.permCongr x * (e.permCongr c)⁻¹ =
      e.permCongr (c * x * c⁻¹) := by
  have hinv : (e.permCongr c)⁻¹ = e.permCongr c⁻¹ := by
    exact (map_inv e.permCongrHom c).symm
  calc
    e.permCongr c * e.permCongr x * (e.permCongr c)⁻¹ =
        e.permCongr (c * x) * e.permCongr c⁻¹ := by rw [hinv, ← e.permCongr_mul]
    _ = e.permCongr ((c * x) * c⁻¹) := by rw [← e.permCongr_mul]
    _ = e.permCongr (c * x * c⁻¹) := by rfl

public theorem twoWreathKleinFour_sup_base_eq_top
    (d : Nat) (hd : 2 ≤ d) (heven : Even d) :
    twoWreathKleinFour d hd heven ⊔ evenTwoBlockWreathBase d = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x, y, hxy⟩ :=
    exists_twoWreathKleinFour_mul_base d hd heven z
  rw [← hxy]
  exact mul_mem
    ((show twoWreathKleinFour d hd heven ≤
        twoWreathKleinFour d hd heven ⊔ evenTwoBlockWreathBase d from
      le_sup_left) ⟨x, rfl⟩)
    ((show evenTwoBlockWreathBase d ≤
        twoWreathKleinFour d hd heven ⊔ evenTwoBlockWreathBase d from
      le_sup_right) ⟨y, rfl⟩)

open scoped commutatorElement

private theorem __ch5_TwoWreath_commutatorElement_mul_left_of_mem_center
    {G : Type*} [Group G] (k x y : G)
    (hk : k ∈ Subgroup.center G) :
    ⁅k * x, y⁆ = ⁅x, y⁆ := by
  have hky : Commute k y := (Subgroup.mem_center_iff.mp hk y).symm
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_left_eq_conj_mul,
    hky.commutator_eq, mul_one]
  exact hkcomm.mul_inv_cancel

private theorem __ch5_TwoWreath_commutatorElement_mul_right_of_mem_center
    {G : Type*} [Group G] (x k y : G)
    (hk : k ∈ Subgroup.center G) :
    ⁅x, k * y⁆ = ⁅x, y⁆ := by
  have hxk : Commute x k := Subgroup.mem_center_iff.mp hk x
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_right_eq_mul_conj,
    hxk.commutator_eq, one_mul]
  exact hkcomm.mul_inv_cancel

/-- The fused component-derived product is the derived subgroup of the full
preimage of the ordered alternating base.  This identifies the subgroup that
must be normalized in the transitive two-wreath reduction intrinsically. -/
public theorem evenBlockComponentDerivedProduct_eq_commutator
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    evenBlockComponentDerivedProduct qA qB f hf hker =
      commutator (alternatingBlockPreimage (qA + 5) (qB + 5) f) := by
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let L := evenBlockComponentDerivedProduct qA qB f hf hker
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center
      (qA + 5) (qB + 5) f hker
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    apply Subgroup.mul_mem (commutator E)
    · have hx : ((x.1 : prodLeftPreimage r) : E) ∈
          ⁅(prodLeftPreimage r : Subgroup E), prodLeftPreimage r⁆ := by
        rw [← (prodLeftPreimage r).map_subtype_commutator]
        exact ⟨x.1, x.1.2, rfl⟩
      exact (Subgroup.commutator_mono le_top le_top) hx
    · have hx : ((x.2 : prodRightPreimage r) : E) ∈
          ⁅(prodRightPreimage r : Subgroup E), prodRightPreimage r⁆ := by
        rw [← (prodRightPreimage r).map_subtype_commutator]
        exact ⟨x.2, x.2.2, rfl⟩
      exact (Subgroup.commutator_mono le_top le_top) hx
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨kx, dx, hx⟩ :=
      evenBlockComponentDerivedProduct_decomposition qA qB f hf hker x
    obtain ⟨ky, dy, hy⟩ :=
      evenBlockComponentDerivedProduct_decomposition qA qB f hf hker y
    have hkx : (kx : E) ∈ Subgroup.center E := hrker kx.2
    have hky : (ky : E) ∈ Subgroup.center E := hrker ky.2
    have hcomm : ⁅x, y⁆ = ⁅(dx : E), (dy : E)⁆ := by
      rw [← hx, ← hy,
        __ch5_TwoWreath_commutatorElement_mul_left_of_mem_center _ _ _ hkx,
        __ch5_TwoWreath_commutatorElement_mul_right_of_mem_center _ _ _ hky]
    rw [hcomm]
    exact (Subgroup.commutator_le_self L)
      (Subgroup.commutator_mem_commutator dx.2 dy.2)

/-- The ordered alternating base is normal in the full even two-wreath group. -/
public theorem evenTwoBlockWreathBase_normal (d : Nat) :
    (evenTwoBlockWreathBase d).Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ z
  let c : evenTwoBlockWreathGroup d :=
    z * evenTwoBlockWreathBaseHom d y * z⁻¹
  have hright : c.1.right = 1 := by
    simp [c, evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
      twoBlockWreathBaseHom]
  have hy0 : Equiv.Perm.sign
      ((evenBlockAlternatingHom d d y :
        evenBlockProductGroup d d) :
          Equiv.Perm (Fin d) × Equiv.Perm (Fin d)).1 = 1 := by
    change Equiv.Perm.sign (y.1 : Equiv.Perm (Fin d)) = 1
    exact y.1.2
  have hy1 : Equiv.Perm.sign
      ((evenBlockAlternatingHom d d y :
        evenBlockProductGroup d d) :
          Equiv.Perm (Fin d) × Equiv.Perm (Fin d)).2 = 1 := by
    change Equiv.Perm.sign (y.2 : Equiv.Perm (Fin d)) = 1
    exact y.2.2
  have hsign (i : Fin 2) : Equiv.Perm.sign (c.1.left i) = 1 := by
    simp [c, evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
      twoBlockWreathBaseHom, twoBlockBasePairHom,
      permuteCoordinatesHom_apply];
      split_ifs <;>
      simp [Equiv.Perm.sign_mul, hy0, hy1]
  let y' : alternatingGroup (Fin d) × alternatingGroup (Fin d) :=
    (⟨c.1.left 0, hsign 0⟩, ⟨c.1.left 1, hsign 1⟩)
  refine ⟨y', ?_⟩
  change evenTwoBlockWreathBaseHom d y' = c
  apply Subtype.ext
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;>
      simp [y', evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
        twoBlockWreathBaseHom, twoBlockBasePairHom,
        evenBlockAlternatingHom]
  · simpa [evenTwoBlockWreathBaseHom, evenBlockToEvenTwoWreathHom,
      twoBlockWreathBaseHom] using hright.symm

/- The kernel intersection endpoint for a normal factor and a quotient
complement.  The quotient-side disjointness is kept explicit because the
ambient wreath proof uses a complement that is conjugated into the base. -/
public theorem kernel_inf_sup_of_map_of_normal
    {H Q : Type*} [Group H] [Group Q]
    (r : H →* Q)
    (K U L C : Subgroup H) (B A : Subgroup Q)
    (hLnormal : L.Normal)
    (hK : K ≤ r.ker) (hkerK : r.ker ≤ K)
    (hU : U ≤ B.comap r)
    (hL : L ≤ A.comap r)
    (hBA : B ⊓ A = ⊥)
    (hKU : K ⊓ U ≤ C)
    (hKL : K ⊓ L = C) :
    K ⊓ (U ⊔ L) = C := by
  apply le_antisymm
  · rintro x ⟨hxK, hxD⟩
    obtain ⟨u, huU, l, hlL, hul⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := U) (t := L)).mp hxD
    have hrx : r x = 1 := MonoidHom.mem_ker.mp (hK hxK)
    have hrua : r u * r l = 1 := by
      rw [← map_mul, hul, hrx]
    have hruB : r u ∈ B := hU huU
    have hrlA : r l ∈ A := hL hlL
    have hruA : r u ∈ A := by
      have huEq : r u = (r l)⁻¹ := (eq_inv_iff_mul_eq_one).2 hrua
      rw [huEq]
      exact A.inv_mem hrlA
    have hru0 : r u = 1 := by
      have : r u ∈ B ⊓ A := ⟨hruB, hruA⟩
      rw [hBA] at this
      exact this
    have huK : u ∈ K := hkerK (MonoidHom.mem_ker.mpr hru0)
    have huC : u ∈ C := hKU ⟨huK, huU⟩
    have hlK : l ∈ K := by
      have hxl : l = u⁻¹ * x := by rw [← hul]; group
      rw [hxl]
      exact K.mul_mem (K.inv_mem huK) hxK
    have hlC : l ∈ C :=
      hKL ▸ (show l ∈ K ⊓ L from ⟨hlK, hlL⟩)
    rw [← hul]
    exact C.mul_mem huC hlC
  · intro x hx
    have hx' : x ∈ K ⊓ L := hKL.symm ▸ hx
    exact ⟨hx'.1, Subgroup.mem_sup_right hx'.2⟩

/- The full even-wreath preimage in a central extension of `A_(d+d)`. -/
public abbrev evenTwoBlockWreathPreimage
    {H : Type*} [Group H] (d : Nat)
    (f : H →* alternatingGroup (Fin (d + d))) : Subgroup H :=
  (evenTwoBlockWreathFinHom d).range.comap f

@[expose]
public noncomputable def evenTwoBlockWreathPreimageProjection
    {H : Type*} [Group H] (d : Nat) (hd : 2 ≤ d)
    (f : H →* alternatingGroup (Fin (d + d))) :
    evenTwoBlockWreathPreimage d f →* evenTwoBlockWreathGroup d :=
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let e := MonoidHom.ofInjective (evenTwoBlockWreathFinHom_injective d)
  e.symm.toMonoidHom.comp
    ((f.comp (evenTwoBlockWreathPreimage d f).subtype).codRestrict
      (evenTwoBlockWreathFinHom d).range (fun x => x.2))

public theorem evenTwoBlockWreathPreimageProjection_surjective
    {H : Type*} [Group H] (d : Nat) (hd : 2 ≤ d)
    (f : H →* alternatingGroup (Fin (d + d)))
    (hf : Function.Surjective f) :
    Function.Surjective (evenTwoBlockWreathPreimageProjection d hd f) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  intro y
  let e := MonoidHom.ofInjective (evenTwoBlockWreathFinHom_injective d)
  obtain ⟨x, hx⟩ := hf (evenTwoBlockWreathFinHom d y)
  have hxE : x ∈ evenTwoBlockWreathPreimage d f := ⟨y, hx.symm⟩
  let xE : evenTwoBlockWreathPreimage d f := ⟨x, hxE⟩
  refine ⟨xE, ?_⟩
  dsimp [evenTwoBlockWreathPreimageProjection]
  change e.symm ⟨f x, hxE⟩ = y
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem evenTwoBlockWreathPreimageProjection_fac
    {H : Type*} [Group H] (d : Nat) (hd : 2 ≤ d)
    (f : H →* alternatingGroup (Fin (d + d)))
    (x : evenTwoBlockWreathPreimage d f) :
    evenTwoBlockWreathFinHom d
        (evenTwoBlockWreathPreimageProjection d hd f x) = f x := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let e := MonoidHom.ofInjective (evenTwoBlockWreathFinHom_injective d)
  dsimp [evenTwoBlockWreathPreimageProjection]
  change evenTwoBlockWreathFinHom d
      (e.symm ⟨f x, x.2⟩) = f x
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨f x, x.2⟩)
  exact h

public theorem evenTwoBlockWreathPreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (d : Nat) (hd : 2 ≤ d)
    (f : H →* alternatingGroup (Fin (d + d))) :
    (evenTwoBlockWreathPreimageProjection d hd f).ker =
      f.ker.comap (evenTwoBlockWreathPreimage d f).subtype := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let e := MonoidHom.ofInjective (evenTwoBlockWreathFinHom_injective d)
  let r0 := (f.comp (evenTwoBlockWreathPreimage d f).subtype).codRestrict
    (evenTwoBlockWreathFinHom d).range (fun x => x.2)
  calc
    (evenTwoBlockWreathPreimageProjection d hd f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = f.ker.comap (evenTwoBlockWreathPreimage d f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

/-- The parity-correlated block product embeds as the ordered base of the
full wreath group. -/
@[expose]
public noncomputable def evenBlockProductToEvenTwoWreathHom (d : Nat) :
    evenBlockProductGroup d d →* evenTwoBlockWreathGroup d :=
  ((twoBlockWreathBaseHom d).comp
      (evenBlockProductGroup d d).subtype).codRestrict
    (evenTwoBlockWreathGroup d) (by
      intro x
      change Equiv.Perm.sign
        (twoBlockWreathFinPermHom d (twoBlockWreathBaseHom d x)) = 1
      rw [twoBlockWreathBaseHom_ambient]
      exact x.property)

public theorem evenBlockProductToEvenTwoWreathHom_injective (d : Nat) :
    Function.Injective (evenBlockProductToEvenTwoWreathHom d) := by
  intro x y h
  have hbaseEq : twoBlockWreathBaseHom d
      (x : Equiv.Perm (Fin d) × Equiv.Perm (Fin d)) =
      twoBlockWreathBaseHom d
        (y : Equiv.Perm (Fin d) × Equiv.Perm (Fin d)) := by
    simpa [evenBlockProductToEvenTwoWreathHom] using
      congrArg Subtype.val h
  apply Subtype.ext
  apply twoBlockWreathBaseHom_injective d
  exact hbaseEq

public theorem evenTwoBlockWreathBaseHom_ambient (d : Nat)
    (y : alternatingGroup (Fin d) × alternatingGroup (Fin d)) :
    evenTwoBlockWreathFinHom d
        (evenTwoBlockWreathBaseHom d y) =
      alternatingProdBlockHom d d y := by
  change evenTwoBlockWreathFinHom d
      (evenBlockToEvenTwoWreathHom d (evenBlockAlternatingHom d d y)) = _
  rw [evenBlockToEvenTwoWreathHom_ambient d
      (evenBlockAlternatingHom d d y)]
  exact DFunLike.congr_fun
    (evenBlockProductHom_comp_evenBlockAlternatingHom d d) y

end

end GLS3.Chapter5.SchurPresentation
/- END Theory.TwoWreath -/

/- BEGIN Theory.InvolutionRotationPermutationSemidirect -/
noncomputable section

namespace GLS3.Chapter5

universe __ch5_InvolutionRotationPermutationSemidirect_u

public abbrev InvolutionRotationPermutationSemidirect
    {Ω : Type __ch5_InvolutionRotationPermutationSemidirect_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
  CycleRotationGroup x ⋊[cyclePermutationActionOnCycleRotations x]
    cyclePermutationSubgroup x

/-- The rotation-permutation factor is its explicit cycle wreath semidirect
product. -/
public noncomputable def involutionRotationPermutationSemidirectEquiv
    {Ω : Type __ch5_InvolutionRotationPermutationSemidirect_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    InvolutionRotationPermutationSemidirect x ≃*
      ↥(cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) := by
  let R := cycleRotationSubgroup x
  let L := cyclePermutationSubgroup x
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let compat : ∀ l : L,
      (cycleRotationToCentralizer x).comp
          ((cyclePermutationActionOnCycleRotations x) l).toMonoidHom =
        (MulAut.conj l.1).toMonoidHom.comp (cycleRotationToCentralizer x) := by
    intro l
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact cyclePermutationActionOnCycleRotations_apply x l a
  let raw : InvolutionRotationPermutationSemidirect x →* C :=
    SemidirectProduct.lift (cycleRotationToCentralizer x) L.subtype compat
  let f : InvolutionRotationPermutationSemidirect x →* ↥(R ⊔ L) :=
    raw.codRestrict (R ⊔ L) (by
      intro z
      change raw z ∈ R ⊔ L
      change cycleRotationToCentralizer x z.1 * z.2.1 ∈ R ⊔ L
      exact Subgroup.mul_mem_sup ⟨z.1, rfl⟩ z.2.2)
  apply MulEquiv.ofBijective f
  constructor
  · intro z w hzw
    have hval := congrArg (fun q : ↥(R ⊔ L) => q.1) hzw
    change cycleRotationToCentralizer x z.1 * z.2.1 =
      cycleRotationToCentralizer x w.1 * w.2.1 at hval
    have hinter :
        (cycleRotationToCentralizer x z.1)⁻¹ * cycleRotationToCentralizer x w.1 ∈
          R ⊓ L := by
      constructor
      · exact R.mul_mem (R.inv_mem ⟨z.1, rfl⟩) ⟨w.1, rfl⟩
      · have hright :
            cycleRotationToCentralizer x w.1 =
              cycleRotationToCentralizer x z.1 * z.2.1 * w.2.1⁻¹ := by
          calc
            _ = (cycleRotationToCentralizer x w.1 * w.2.1) * w.2.1⁻¹ := by group
            _ = (cycleRotationToCentralizer x z.1 * z.2.1) * w.2.1⁻¹ := by rw [hval]
            _ = _ := by group
        have heq :
            (cycleRotationToCentralizer x z.1)⁻¹ *
                cycleRotationToCentralizer x w.1 = z.2.1 * w.2.1⁻¹ := by
          rw [hright]
          group
        simpa [heq] using L.mul_mem z.2.2 (L.inv_mem w.2.2)
    have hone : (cycleRotationToCentralizer x z.1)⁻¹ *
        cycleRotationToCentralizer x w.1 = 1 := by
      have hbot :
          ((cycleRotationToCentralizer x z.1)⁻¹ *
              cycleRotationToCentralizer x w.1 : C) ∈ (⊥ : Subgroup C) := by
        rw [← cycleRotationSubgroup_inf_cyclePermutationSubgroup_eq_bot x]
        exact hinter
      simpa using hbot
    have hrot : z.1 = w.1 := by
      apply cycleRotationToCentralizer_injective x
      exact inv_mul_eq_one.mp hone
    apply SemidirectProduct.ext
    · exact hrot
    · apply Subtype.ext
      rw [hrot] at hval
      exact mul_left_cancel hval
  · intro y
    have hy : y.1 ∈ (↑(R ⊔ L) : Set C) := y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R L
      (cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x)] at hy
    rcases hy with ⟨r, hr, l, hl, hrl⟩
    obtain ⟨a, rfl⟩ := hr
    refine ⟨⟨a, ⟨l, hl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hrl

end GLS3.Chapter5
/- END Theory.InvolutionRotationPermutationSemidirect -/

/- BEGIN Theory.Theorem523Core1 -/
noncomputable section

/- Source: theorem_5_2_3_a.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523Core1_w

namespace GLS3.Chapter5.SchurPresentation


/-! Printed Theorem 5.2.3(a): the explicit Schur presentation gives the
standard double covering and its two-element kernel. -/

public theorem theorem_5_2_3_a (n : Nat) :
    Nat.card (schurAlternatingCovering n).toMonoidHom.ker = 2 :=
  natCard_ker_schurAlternatingCovering n

end GLS3.Chapter5.SchurPresentation

/- Source: theorem_5_2_3_b.lean -/

namespace GLS3.Chapter5.SchurPresentation

/-! The universal-cover part of the next Schur clause is proved from the
project's Covering API. The exceptional multiplier and Sylow-3 assertions
remain classification input and are intentionally not encoded as assumptions.
-/
public theorem theorem_5_2_3_b_universal
    {G₁ G₂ : Type} [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (n : Nat)
    (f₁ : Covering G₁ (alternatingGroup (Fin (n + 5))))
    (f₂ : Covering G₂ (alternatingGroup (Fin (n + 5))))
    (hf₁ : Covering.IsUniversal.{0, 0, 0} f₁)
    (hf₂ : Covering.IsUniversal.{0, 0, 0} f₂) :
    ∃! e : G₁ ≃* G₂,
      f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  exact theorem_5_2_3_a_2_universal n f₁ f₂ hf₁ hf₂

end GLS3.Chapter5.SchurPresentation

/- Source: theorem_5_2_3_rest.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Theorem 5.2.3 (Schur), remaining clauses

The first clause of the printed Theorem 5.2.3 — the existence of the double
cover `2A_{n+5} → A_{n+5}` with kernel of order two — is proved as
`theorem_5_2_3_a` / `theorem_5_2_3_a_1`, and the uniqueness of *universal*
covers is `theorem_5_2_3_a_2_universal`.  The remaining clauses are proved
below from explicit Schur-presentation calculations and finite covering
certificates.

Source proofs:
* [A1, 33.15] — `refs/KGroup/GLS3/Ch5A1.tex`, Aschbacher *Finite Group
  Theory* ch. 33 "Central extensions": (33.1) uniqueness of the universal
  central extension; (33.15) `M(A_n) ≅ Z₆` for `n = 6, 7`, `≅ Z₂` otherwise,
  plus the involution-lift clause (5.2.4a/e) and `3^{1+2}` Sylow-3 for
  `n = 6, 7` (the only source for the Sylow-3 clause).
* [Su1, pp. 301-306] — `refs/KGroup/GLS3/Ch5Su1.tex`, Suzuki *Group Theory I*
  Ch. 3 §2: (2.21) multiplier of the symmetric group; (2.22) multiplier of
  `A_n` of order 2 for `n ≠ 6, 7` (full presentation computation); p. 305
  "Exceptional Cases": `M(A₆) = ⟨k⟩` with `k³ = __ch5_Theorem523Core1_w`, `M(A₇) = ⟨k⟩` with
  `k⁶ = 1`, i.e. cyclic of order 6.  The 3-fold coverings `3A₆`, `3A₇` are
  NOT constructed there (deferred to Schur's original paper).

The transfer infrastructure for these statements lives in
`KGroup/GLS3/Chapter5/SchurMultiplier.lean` (`kernelMulEquiv`,
`universalKernelMulEquiv`, `universalKernel_card_eq`).  The 3-cover source
for `theorem_5_2_3_d_*` is being located separately.

The module is intended to be imported from `KGroup.lean` after its targeted
build and axiom audit succeed.
-/

open scoped commutatorElement

public theorem commutatorElement_mul_left_of_center
    {E : Type*} [Group E] (k x y : E) (hk : k ∈ Subgroup.center E) :
    ⁅k * x, y⁆ = ⁅x, y⁆ := by
  have hky : Commute k y := (Subgroup.mem_center_iff.mp hk y).symm
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hky.commutator_eq, mul_one]
  exact hkcomm.mul_inv_cancel

public theorem commutatorElement_mul_right_of_center
    {E : Type*} [Group E] (x k y : E) (hk : k ∈ Subgroup.center E) :
    ⁅x, k * y⁆ = ⁅x, y⁆ := by
  have hxk : Commute x k := Subgroup.mem_center_iff.mp hk x
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_right_eq_mul_conj, hxk.commutator_eq, one_mul]
  exact hkcomm.mul_inv_cancel

/- A finite extension with a 2-group kernel splits over the inverse image of
   a cyclic subgroup of order three.  We keep this local because it is only
   needed for the exceptional `A₄ × A₄` endpoint in degree eight. -/
public theorem exists_order_three_lift_of_two_kernel
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    (f : H →* G) (hf : Function.Surjective f)
    (hker2 : IsPGroup 2 f.ker)
    (a : G) (ha : orderOf a = 3) :
    ∃ y : H, f y = a ∧ orderOf y = 3 := by
  let C : Subgroup G := Subgroup.zpowers a
  let E : Subgroup H := C.comap f
  let r : E →* C :=
    (f.comp E.subtype).codRestrict C (by intro x; exact x.2)
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x, hx⟩ := hf (z : G)
    have hxC : f x ∈ C := by rw [hx]; exact z.2
    let xE : E := ⟨x, hxC⟩
    refine ⟨xE, ?_⟩
    apply Subtype.ext
    exact hx
  let K : Subgroup E := r.ker
  have hK : K = f.ker.comap E.subtype := by
    ext x
    change r x = 1 ↔ E.subtype x ∈ f.ker
    constructor
    · intro hx
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp hx
  have hcardC : Nat.card C = 3 := by
    dsimp [C]
    rw [Nat.card_zpowers, ha]
  have hquot : E ⧸ K ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective r hr
  have hindex : K.index = 3 := by
    rw [Subgroup.index_eq_card]
    calc
      Nat.card (E ⧸ K) = Nat.card C := Nat.card_congr hquot.toEquiv
      _ = 3 := hcardC
  have hker2E : IsPGroup 2 K := by
    rw [hK]
    exact hker2.comap_subtype
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hker2E
  have hcop : Nat.Coprime (Nat.card K) K.index := by
    rw [he, hindex]
    exact (by decide : Nat.Coprime 2 3).pow_left e
  obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hScard : Nat.card S = 3 := by
    rw [← hS.symm.index_eq_card, hindex]
  obtain ⟨x, hx⟩ := hf a
  let xE : E :=
    ⟨x, by
      have : f x ∈ C := by rw [hx]; exact Subgroup.mem_zpowers a
      exact this⟩
  have hrx : r xE = ⟨a, Subgroup.mem_zpowers a⟩ := by
    apply Subtype.ext
    exact hx
  have hcomp : Subgroup.IsComplement (K : Set E) (S : Set E) :=
    Subgroup.isComplement'_def.mp hS
  obtain ⟨ks, hss⟩ := hcomp.existsUnique xE
  let sS : S := ks.2
  let s : E := sS
  have hxs : (ks.1 : E) * s = xE := hss.1
  have hrs : r s = ⟨a, Subgroup.mem_zpowers a⟩ := by
    have hk1 : r ks.1 = 1 := MonoidHom.mem_ker.mp ks.1.2
    have h := congrArg r hxs
    rw [map_mul, hk1, one_mul, hrx] at h
    exact h
  have hfs : f (s : H) = a := congrArg Subtype.val hrs
  have hsn : (s : E) ≠ 1 := by
    intro hs1
    have h : f (s : H) = 1 := by rw [hs1]; simp
    rw [hfs] at h
    have ha_ne : a ≠ 1 := by
      intro ha1
      have h' := ha
      rw [ha1] at h'
      norm_num at h'
    exact ha_ne h
  have hdiv : orderOf sS ∣ Nat.card S := orderOf_dvd_natCard sS
  have horder : orderOf sS = 3 := by
    rw [hScard] at hdiv
    have hne : orderOf sS ≠ 1 := by
      intro h1
      exact hsn (by
        apply Subtype.ext
        simpa [s, Subgroup.orderOf_coe] using (orderOf_eq_one_iff.mp h1))
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv).resolve_left hne
  refine ⟨s, hfs, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact horder

public theorem natCard_ker_comp_commutator_le_two_of_klein
    {E V : Type*} [Group E] [Finite E] [Group V] [Finite V] [IsKleinFour V]
    (r : E →* V) (hr : Function.Surjective r)
    (hker : r.ker ≤ Subgroup.center E) :
    Nat.card (r.comp (commutator E).subtype).ker ≤ 2 := by
  classical
  let : Nontrivial V :=
    Finite.one_lt_card_iff_nontrivial.mp (by simp : 1 < Nat.card V)
  obtain ⟨a, ha⟩ := exists_ne (1 : V)
  have hb : ∃ b : V, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    have h' : ∀ b : V, b = 1 ∨ b = a := by
      intro b
      by_contra hb'
      push Not at hb'
      exact h ⟨b, hb'.1, hb'.2⟩
    have hsub : (Set.univ : Set V) ⊆ ({1, a} : Set V) := by
      intro b _
      rcases h' b with hba | hbb
      · simp [hba]
      · simp [hbb]
    have hn := Set.ncard_le_ncard hsub
    have htwo : ({1, a} : Set V).ncard = 2 := by
      rw [show ({1, a} : Set V) = insert 1 {a} by rfl,
        Set.ncard_insert_of_notMem]
      · simp
      · exact fun h => ha h.symm
    simp [Set.ncard_univ, IsKleinFour.card_four, htwo] at hn
  obtain ⟨b, hb1, hba⟩ := hb
  obtain ⟨x, hx⟩ := hr a
  obtain ⟨y, hy⟩ := hr b
  have hx2ker : x ^ 2 ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    simpa using (Monoid.pow_exponent_eq_one a)
  have hy2ker : y ^ 2 ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy]
    simpa using (Monoid.pow_exponent_eq_one b)
  have hx2center : x ^ 2 ∈ Subgroup.center E := hker hx2ker
  have hy2center : y ^ 2 ∈ Subgroup.center E := hker hy2ker
  let c : E := ⁅x, y⁆
  let : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hcKer : c ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative V)) _ _
  have hcCenter : c ∈ Subgroup.center E := hker hcKer
  have hc2 : c ^ 2 = 1 := by
    have hxx : Commute (x * x) y := by
      change x * x * y = y * (x * x)
      simpa [pow_two] using
        (Subgroup.mem_center_iff.mp hx2center y).symm
    have hleft : ⁅x * x, y⁆ = 1 := hxx.commutator_eq
    have hconj : x * c * x⁻¹ = c := by
      have hcx : c * x = x * c :=
        (Subgroup.mem_center_iff.mp hcCenter x).symm
      rw [← hcx]
      group
    have hident := commutatorElement_mul_left_eq_conj_mul x x y
    calc
      c ^ 2 = c * c := by rw [pow_two]
      _ = x * c * x⁻¹ * c := by rw [hconj]
      _ = ⁅x * x, y⁆ := by simpa [c] using hident.symm
      _ = 1 := hleft
  have hdecomp (z : E) : ∃ k : r.ker, ∃ l : E,
      z = (k : E) * l ∧ r l = r z ∧
        (l = 1 ∨ l = x ∨ l = y ∨ l = x * y) := by
    by_cases hz1 : r z = 1
    · refine ⟨⟨z, hz1⟩, 1, by simp, by simpa using hz1.symm,
        Or.inl rfl⟩
    by_cases hza : r z = a
    · refine ⟨⟨z * x⁻¹, ?_⟩, x, by group, ?_,
        Or.inr (Or.inl rfl)⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hx, hza]
        simp
      · exact hx.trans hza.symm
    by_cases hzb : r z = b
    · refine ⟨⟨z * y⁻¹, ?_⟩, y, by group, ?_,
        Or.inr (Or.inr (Or.inl rfl))⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hy, hzb]
        simp
      · exact hy.trans hzb.symm
    have hza' : r z ≠ a := by intro h; exact hza h
    have hzb' : r z ≠ b := by intro h; exact hzb h
    have hab : a ≠ b := by intro h; exact hba h.symm
    have heq : r z = a * b :=
      IsKleinFour.eq_mul_of_ne_all ha hb1 hab hz1 hza' hzb'
    refine ⟨⟨z * (x * y)⁻¹, ?_⟩, x * y, by group, ?_,
      Or.inr (Or.inr (Or.inr rfl))⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hx, hy, heq]
      simp
    · rw [map_mul, hx, hy, heq]
  have hconj_c (z : E) : z * c * z⁻¹ = c := by
    have hcz : c * z = z * c :=
      (Subgroup.mem_center_iff.mp hcCenter z).symm
    rw [← hcz]
    group
  have hxy : ⁅x, x * y⁆ = c := by
    calc
      ⁅x, x * y⁆ = ⁅x, x⁆ * x * ⁅x, y⁆ * x⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj x x y
      _ = x * c * x⁻¹ := by simp [c]
      _ = c := hconj_c x
  have hxyy : ⁅x * y, y⁆ = c := by
    calc
      ⁅x * y, y⁆ = x * ⁅y, y⁆ * x⁻¹ * ⁅x, y⁆ :=
        commutatorElement_mul_left_eq_conj_mul x y y
      _ = c := by simp [c]
  have hyxy : ⁅y, x * y⁆ = c⁻¹ := by
    calc
      ⁅y, x * y⁆ = (⁅y, x * y⁆⁻¹)⁻¹ := by simp
      _ = ⁅x * y, y⁆⁻¹ := by rw [commutatorElement_inv]
      _ = c⁻¹ := by rw [hxyy]
  have hxyx : ⁅x * y, x⁆ = c⁻¹ := by
    calc
      ⁅x * y, x⁆ = (⁅x * y, x⁆⁻¹)⁻¹ := by simp
      _ = ⁅x, x * y⁆⁻¹ := by rw [commutatorElement_inv]
      _ = c⁻¹ := by rw [hxy]
  have hyx : ⁅y, x⁆ = c⁻¹ := by
    calc
      ⁅y, x⁆ = (⁅y, x⁆⁻¹)⁻¹ := by simp
      _ = ⁅x, y⁆⁻¹ := by rw [commutatorElement_inv]
      _ = c⁻¹ := by rfl
  have hcomm_cases (u v : E) : ⁅u, v⁆ ∈ Subgroup.zpowers c := by
    obtain ⟨ku, lu, hu, _, hlu⟩ := hdecomp u
    obtain ⟨kv, lv, hv, _, hlav⟩ := hdecomp v
    have hu' : (ku : E) ∈ Subgroup.center E := hker ku.property
    have hv' : (kv : E) ∈ Subgroup.center E := hker kv.property
    have hbase : ⁅u, v⁆ = ⁅lu, lv⁆ := by
      calc
        ⁅u, v⁆ = ⁅(ku : E) * lu, (kv : E) * lv⁆ := by rw [hu, hv]
        _ = ⁅lu, (kv : E) * lv⁆ :=
          commutatorElement_mul_left_of_center _ _ _ hu'
        _ = ⁅lu, lv⁆ :=
          commutatorElement_mul_right_of_center _ _ _ hv'
    rw [hbase]
    rcases hlu with h1 | h2 | h3 | h4 <;>
      rcases hlav with k1 | k2 | k3 | k4 <;>
      subst lu <;> subst lv <;>
      simp only [c, commutatorElement_one_left, commutatorElement_one_right,
        commutatorElement_self, hxy, hxyy, hyxy, hxyx, hyx] <;>
      first
      | exact Subgroup.one_mem _
      | exact Subgroup.mem_zpowers _
      | exact (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)
  have hcomm_le : commutator E ≤ Subgroup.zpowers c := by
    change ⁅(⊤ : Subgroup E), ⊤⁆ ≤ Subgroup.zpowers c
    rw [Subgroup.commutator_le]
    intro u _ v _
    exact hcomm_cases u v
  let inj : (r.comp (commutator E).subtype).ker → Subgroup.zpowers c :=
    fun z => ⟨(z.1 : E), hcomm_le z.1.property⟩
  have hinj : Function.Injective inj := by
    intro z₁ z₂ hz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun __ch5_Theorem523Core1_w : Subgroup.zpowers c => (__ch5_Theorem523Core1_w : E)) hz
  calc
    Nat.card (r.comp (commutator E).subtype).ker ≤ Nat.card (Subgroup.zpowers c) :=
      Nat.card_le_card_of_injective inj hinj
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by omega) hc2

public theorem natCard_a8_local_commutator_ker_le_two
    {E : Type*} [Group E] [Finite E]
    (r : E →* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))
    (hr : Function.Surjective r)
    (hker : r.ker ≤ Subgroup.center E) :
    ∃ D1 : Subgroup (commutator E),
      ∃ r1 : D1 →* alternatingGroup.kleinFour (Fin 4),
        Function.Surjective r1 ∧
          r1.ker =
            (r.comp (commutator E).subtype).ker.comap D1.subtype ∧
          r1.ker ≤ Subgroup.center D1 ∧
          Nat.card (r1.comp (commutator D1).subtype).ker ≤ 2 := by
  let A := alternatingGroup (Fin 4)
  let V := alternatingGroup.kleinFour (Fin 4)
  let V1 : Subgroup (A × A) := V.prod ⊥
  let rD : commutator E →* (A × A) :=
    r.comp (commutator E).subtype
  let D1 : Subgroup (commutator E) := V1.comap rD
  let r1 : D1 →* V :=
    ((MonoidHom.fst A A).comp (rD.comp D1.subtype)).codRestrict V
      (by intro x; exact x.2.1)
  have hmap : Subgroup.map r (commutator E) = V.prod V := by
    dsimp [A, V]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr]
    simpa [← commutator_def,
      alternatingGroup.kleinFour_eq_commutator (Nat.card_fin 4)] using
      (Subgroup.commutator_prod_prod
        (⊤ : Subgroup (alternatingGroup (Fin 4)))
        (⊤ : Subgroup (alternatingGroup (Fin 4)))
        (⊤ : Subgroup (alternatingGroup (Fin 4)))
        (⊤ : Subgroup (alternatingGroup (Fin 4))))
  have hr1 : Function.Surjective r1 := by
    intro v
    have hv : (v.1, (1 : A)) ∈ V.prod V := by
      exact ⟨v.2, Subgroup.one_mem _⟩
    have hv' : (v.1, (1 : A)) ∈ Subgroup.map r (commutator E) := by
      rw [hmap]
      exact hv
    obtain ⟨d, hd, hrd⟩ := Subgroup.mem_map.mp hv'
    let d1 : D1 := ⟨⟨d, hd⟩, by
      change r d ∈ V.prod ⊥
      rw [hrd]
      exact ⟨v.2, Subgroup.mem_bot.mpr rfl⟩⟩
    refine ⟨d1, ?_⟩
    apply Subtype.ext
    exact congrArg Prod.fst hrd
  have hkerEq : r1.ker = rD.ker.comap D1.subtype := by
    ext x
    constructor
    · intro hx
      apply MonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      · exact Subgroup.mem_bot.mp x.2.2
    · intro hx
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact congrArg Prod.fst (MonoidHom.mem_ker.mp hx)
  have hcenter : r1.ker ≤ Subgroup.center D1 := by
    intro x hx
    have hxD' : x ∈ rD.ker.comap D1.subtype := by
      rw [← hkerEq]
      exact hx
    change D1.subtype x ∈ rD.ker at hxD'
    have hxD : D1.subtype x ∈ rD.ker := hxD'
    have hrx : rD (D1.subtype x) = 1 := MonoidHom.mem_ker.mp hxD
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mp hrx))
      (D1.subtype y)
  let : IsKleinFour V := by
    dsimp [V]
    exact alternatingGroup.kleinFour_isKleinFour (Nat.card_fin 4)
  have hbound := natCard_ker_comp_commutator_le_two_of_klein
    r1 hr1 hcenter
  exact ⟨D1, r1, hr1, hkerEq, hcenter, hbound⟩

public theorem a4_exists_mul_order_three
    (a : alternatingGroup (Fin 4)) :
    ∃ b c : alternatingGroup (Fin 4),
      orderOf b = 3 ∧ orderOf c = 3 ∧ b * c = a := by
  have h : ∃ b c : alternatingGroup (Fin 4),
      b ^ 3 = 1 ∧ b ≠ 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ b * c = a := by
    fin_cases a <;> decide
  obtain ⟨b, c, hb3, hb1, hc3, hc1, hbc⟩ := h
  exact ⟨b, c, orderOf_eq_prime hb3 hb1,
    orderOf_eq_prime hc3 hc1, hbc⟩

public theorem rootA5PreimageDerivedProjection_fac_a8
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (x : rootA5PreimageDerived 3 f) :
    RootAm.tailAltHom 3 5 (by omega)
        (rootA5PreimageDerivedProjection 3 f x) =
      f x.1.1 := by
  have hproj :
      rootA5Equiv 3 (rootA5PreimageDerivedProjection 3 f x) =
        ⟨f x.1.1, x.1.2⟩ := by
    change rootA5Equiv 3
        ((rootA5Equiv 3).symm ⟨f x.1.1, x.1.2⟩) =
      ⟨f x.1.1, x.1.2⟩
    exact (rootA5Equiv 3).apply_symm_apply _
  exact congrArg Subtype.val hproj

public noncomputable def a8LeftA4Hom :
    alternatingGroup (Fin 4) →* alternatingGroup (Fin 5) where
  toFun σ := ⟨standardRootA4PermHom 0 σ.1, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_standardRootA4PermHom]
    exact σ.2⟩
  map_one' := by
    apply Subtype.ext
    simp [standardRootA4PermHom]
  map_mul' a b := by
    apply Subtype.ext
    simp [standardRootA4PermHom]

public theorem a8LeftA4Hom_injective :
    Function.Injective a8LeftA4Hom := by
  intro a b hab
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective
    (standardRootA4Embedding 0)
  exact congrArg Subtype.val hab

public theorem a8LeftA4Hom_ambient
    (a : alternatingGroup (Fin 4)) :
    RootAm.tailAltHom 3 5 (by omega) (a8LeftA4Hom a) =
      alternatingProdBlockHom 4 4 (a, 1) := by
  apply Subtype.ext
  simp only [a8LeftA4Hom, RootAm.tailAltHom,
    coe_alternatingProdBlockHom_apply]
  change RootAm.tailPermHom 3 5 (by omega)
      (standardRootA4PermHom 0 a.1) =
    permProdBlockHom 4 4 (a.1, 1)
  rw [permProdBlockHom_apply]
  apply Equiv.ext
  intro x
  by_cases hx : x.val < 4
  · let i : Fin 4 := ⟨x.val, hx⟩
    have htail : RootAm.tailEmbedding 3 5 (by omega)
        (standardRootA4Embedding 0 i) = x := by
      apply Fin.ext
      rfl
    have hblock :
        (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin (4 + 4))
          (Sum.inl i) = x := by
      apply Fin.ext
      rfl
    calc
      RootAm.tailPermHom 3 5 (by omega)
          (standardRootA4PermHom 0 a.1) x =
          RootAm.tailPermHom 3 5 (by omega)
            (standardRootA4PermHom 0 a.1)
              (RootAm.tailEmbedding 3 5 (by omega)
                (standardRootA4Embedding 0 i)) :=
        congrArg _ htail.symm
      _ = RootAm.tailEmbedding 3 5 (by omega)
            (standardRootA4Embedding 0 (a.1 i)) := by
        rw [RootAm.tailPermHom,
          Equiv.Perm.viaEmbeddingHom_apply,
          Equiv.Perm.viaEmbedding_apply]
        rw [standardRootA4PermHom,
          Equiv.Perm.viaEmbeddingHom_apply,
          Equiv.Perm.viaEmbedding_apply]
      _ = (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin (4 + 4))
          (Sum.inl (a.1 i)) := by
        apply Fin.ext
        rfl
      _ = (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin (4 + 4)).permCongr
          (Equiv.Perm.sumCongr a.1 (1 : Equiv.Perm (Fin 4))) x := by
        rw [← hblock]
        simp [Equiv.permCongr_apply]
  · let j : Fin 4 := ⟨x.val - 4, by omega⟩
    have hblock :
        (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin (4 + 4))
          (Sum.inr j) = x := by
      apply Fin.ext
      simp [j, finSumFinEquiv]
      omega
    have hright :
        (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin (4 + 4)).permCongr
          (Equiv.Perm.sumCongr a.1 (1 : Equiv.Perm (Fin 4))) x = x := by
      rw [← hblock]
      simp [Equiv.permCongr_apply]
    rw [hright]
    by_cases hx5 : x.val < 5
    · let k : Fin 5 := ⟨x.val, hx5⟩
      have htail : RootAm.tailEmbedding 3 5 (by omega) k = x := by
        apply Fin.ext
        rfl
      have hknot : k ∉ Set.range (standardRootA4Embedding 0) := by
        rintro ⟨i, hi⟩
        have hi' := congrArg Fin.val hi
        simp [k, standardRootA4Embedding] at hi'
        omega
      calc
        RootAm.tailPermHom 3 5 (by omega)
            (standardRootA4PermHom 0 a.1) x =
            RootAm.tailPermHom 3 5 (by omega)
              (standardRootA4PermHom 0 a.1)
                (RootAm.tailEmbedding 3 5 (by omega) k) :=
          congrArg _ htail.symm
        _ = RootAm.tailEmbedding 3 5 (by omega) k := by
          rw [RootAm.tailPermHom,
            Equiv.Perm.viaEmbeddingHom_apply,
            Equiv.Perm.viaEmbedding_apply]
          rw [standardRootA4PermHom,
            Equiv.Perm.viaEmbeddingHom_apply,
            Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hknot]
        _ = x := htail
    · have hxnot : x ∉ Set.range
          (RootAm.tailEmbedding 3 5 (by omega)) := by
        rintro ⟨k, hk⟩
        have hk' := congrArg Fin.val hk
        simp [RootAm.tailEmbedding] at hk'
        omega
      rw [RootAm.tailPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hxnot]

public def a8LeftRoot : Subgroup (alternatingGroup (Fin 5)) :=
  a8LeftA4Hom.range

public noncomputable def a8LeftRootEquiv :
    alternatingGroup (Fin 4) ≃* a8LeftRoot :=
  MonoidHom.ofInjective (f := a8LeftA4Hom)
    a8LeftA4Hom_injective

public abbrev a8LeftSubextension
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    Subgroup (rootA5PreimageDerived 3 f) :=
  a8LeftRoot.comap (rootA5PreimageDerivedProjection 3 f)

public noncomputable def a8LeftSubextensionProjection
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    a8LeftSubextension f →* alternatingGroup (Fin 4) :=
  a8LeftRootEquiv.symm.toMonoidHom.comp
    (((rootA5PreimageDerivedProjection 3 f).comp
        (a8LeftSubextension f).subtype).codRestrict
      a8LeftRoot (fun x => x.2))

public theorem a8LeftSubextensionProjection_surjective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) :
    Function.Surjective (a8LeftSubextensionProjection f) := by
  intro y
  let y' : a8LeftRoot := a8LeftRootEquiv y
  obtain ⟨x, hx⟩ :=
    rootA5PreimageDerivedProjection_surjective 3 f hf y'.1
  have hxRight : rootA5PreimageDerivedProjection 3 f x ∈ a8LeftRoot :=
    hx.symm ▸ y'.2
  refine ⟨⟨x, hxRight⟩, ?_⟩
  change a8LeftRootEquiv.symm
      ⟨rootA5PreimageDerivedProjection 3 f x, hxRight⟩ = y
  apply a8LeftRootEquiv.injective
  rw [a8LeftRootEquiv.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem a8LeftSubextensionProjection_fac
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (x : a8LeftSubextension f) :
    a8LeftA4Hom (a8LeftSubextensionProjection f x) =
      rootA5PreimageDerivedProjection 3 f x := by
  let r := rootA5PreimageDerivedProjection 3 f
  let e := a8LeftRootEquiv
  change a8LeftA4Hom (e.symm ⟨r x, x.2⟩) = r x
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨r x, x.2⟩)
  exact h

public theorem a8LeftSubextension_ambient_fac
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (x : a8LeftSubextension f) :
    f x.1.1.1 = alternatingProdBlockHom 4 4
      (a8LeftSubextensionProjection f x, 1) := by
  calc
    f x.1.1.1 = RootAm.tailAltHom 3 5 (by omega)
        (rootA5PreimageDerivedProjection 3 f x.1) :=
      (rootA5PreimageDerivedProjection_fac_a8 f x.1).symm
    _ = RootAm.tailAltHom 3 5 (by omega)
        (a8LeftA4Hom (a8LeftSubextensionProjection f x)) := by
      rw [a8LeftSubextensionProjection_fac]
    _ = alternatingProdBlockHom 4 4
        (a8LeftSubextensionProjection f x, 1) :=
      a8LeftA4Hom_ambient _

public def a8LeftSubextensionToBlockPreimage
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    a8LeftSubextension f →* alternatingBlockPreimage 4 4 f :=
  let i : a8LeftSubextension f →* H :=
    (rootA5Preimage 3 f).subtype.comp
      ((rootA5PreimageDerived 3 f).subtype.comp
        (a8LeftSubextension f).subtype)
  i.codRestrict (alternatingBlockPreimage 4 4 f) (by
    intro x
    refine ⟨(a8LeftSubextensionProjection f x, 1), ?_⟩
    exact (a8LeftSubextension_ambient_fac f x).symm)

public theorem a8LeftSubextensionToBlockPreimage_injective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    Function.Injective (a8LeftSubextensionToBlockPreimage f) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : alternatingBlockPreimage 4 4 f => (z : H)) hxy

public theorem a8LeftSubextensionToBlockPreimage_projection_fac
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (x : a8LeftSubextension f) :
    alternatingBlockPreimageProjection 4 4 f
        (a8LeftSubextensionToBlockPreimage f x) =
      (a8LeftSubextensionProjection f x, 1) := by
  apply alternatingProdBlockHom_injective 4 4
  calc
    alternatingProdBlockHom 4 4
        (alternatingBlockPreimageProjection 4 4 f
          (a8LeftSubextensionToBlockPreimage f x)) =
        f (a8LeftSubextensionToBlockPreimage f x) :=
      alternatingBlockPreimageProjection_fac 4 4 f _
    _ = f x.1.1.1 := rfl
    _ = alternatingProdBlockHom 4 4
        (a8LeftSubextensionProjection f x, 1) :=
      a8LeftSubextension_ambient_fac f x

public theorem a8LeftSubextensionProjection_ker_eq_comap
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    (a8LeftSubextensionProjection f).ker =
      (rootA5PreimageDerivedProjection 3 f).ker.comap
        (a8LeftSubextension f).subtype := by
  let r := rootA5PreimageDerivedProjection 3 f
  let e := a8LeftRootEquiv
  let r0 := (r.comp (a8LeftSubextension f).subtype).codRestrict
    a8LeftRoot (fun x => x.2)
  calc
    (a8LeftSubextensionProjection f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = r.ker.comap (a8LeftSubextension f).subtype := by
      ext x
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

public theorem natCard_a8LeftSubextensionProjection_ker_le_two
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (a8LeftSubextensionProjection f).ker ≤ 2 := by
  let r := rootA5PreimageDerivedProjection 3 f
  let R := a8LeftSubextension f
  have hkerEq : (a8LeftSubextensionProjection f).ker =
      r.ker.comap R.subtype :=
    a8LeftSubextensionProjection_ker_eq_comap f
  let inj : (a8LeftSubextensionProjection f).ker → r.ker := fun x => by
    have hx : x.1 ∈ r.ker.comap R.subtype := by
      rw [← hkerEq]
      exact x.2
    exact ⟨R.subtype x.1, hx⟩
  have hinj : Function.Injective inj := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : r.ker =>
      (z : rootA5PreimageDerived 3 f)) hxy
  calc
    Nat.card (a8LeftSubextensionProjection f).ker ≤ Nat.card r.ker :=
      Nat.card_le_card_of_injective inj hinj
    _ ≤ 2 := rootA5PreimageDerivedProjection_ker_card_le_two 3 f hf hker

public def a8BlockSwap : alternatingGroup (Fin 8) :=
  equalBlockSwap 4 (by exact ⟨2, rfl⟩)

public theorem a8BlockSwap_conj_left
    (x : alternatingGroup (Fin 4)) :
    a8BlockSwap * alternatingProdBlockHom 4 4 (x, 1) *
        a8BlockSwap⁻¹ =
      alternatingProdBlockHom 4 4 (1, x) := by
  exact equalBlockSwap_conj_left 4 (by exact ⟨2, rfl⟩) x

public noncomputable def a8BlockSwapLift
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) : H :=
  Classical.choose (hf a8BlockSwap)

public theorem a8BlockSwapLift_spec
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) :
    f (a8BlockSwapLift f hf) = a8BlockSwap :=
  Classical.choose_spec (hf a8BlockSwap)

public def a8LeftSubextensionEmbedding
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    a8LeftSubextension f →* H :=
  (rootA5Preimage 3 f).subtype.comp
    ((rootA5PreimageDerived 3 f).subtype.comp
      (a8LeftSubextension f).subtype)

public theorem a8LeftSubextensionEmbedding_fac
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (x : a8LeftSubextension f) :
    f (a8LeftSubextensionEmbedding f x) =
      alternatingProdBlockHom 4 4
        (a8LeftSubextensionProjection f x, 1) :=
  a8LeftSubextension_ambient_fac f x

public noncomputable def a8RightSubextensionEmbedding
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) :
    a8LeftSubextension f →* H :=
  (MulAut.conj (a8BlockSwapLift f hf)).toMonoidHom.comp
    (a8LeftSubextensionEmbedding f)

public theorem a8RightSubextensionEmbedding_fac
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (x : a8LeftSubextension f) :
    f (a8RightSubextensionEmbedding f hf x) =
      alternatingProdBlockHom 4 4
        (1, a8LeftSubextensionProjection f x) := by
  change f (a8BlockSwapLift f hf *
      a8LeftSubextensionEmbedding f x *
      (a8BlockSwapLift f hf)⁻¹) = _
  rw [map_mul, map_mul, map_inv, a8BlockSwapLift_spec,
    a8LeftSubextensionEmbedding_fac]
  exact a8BlockSwap_conj_left _

public theorem a8LeftSubextensionEmbedding_injective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    Function.Injective (a8LeftSubextensionEmbedding f) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

public theorem a8RightSubextensionEmbedding_injective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) :
    Function.Injective (a8RightSubextensionEmbedding f hf) := by
  intro x y hxy
  apply a8LeftSubextensionEmbedding_injective f
  exact (MulAut.conj (a8BlockSwapLift f hf)).injective hxy

public def a8LeftSubextensionKernelEmbedding
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    (a8LeftSubextensionProjection f).ker →* f.ker :=
  ((a8LeftSubextensionEmbedding f).comp
      (a8LeftSubextensionProjection f).ker.subtype).codRestrict
    f.ker (by
      intro x
      rw [MonoidHom.mem_ker]
      change f (a8LeftSubextensionEmbedding f x.1) = 1
      rw [a8LeftSubextensionEmbedding_fac]
      have hx := MonoidHom.mem_ker.mp x.2
      rw [hx]
      exact map_one (alternatingProdBlockHom 4 4))

public theorem a8LeftSubextensionKernelEmbedding_injective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    Function.Injective (a8LeftSubextensionKernelEmbedding f) := by
  intro x y hxy
  apply Subtype.ext
  apply a8LeftSubextensionEmbedding_injective f
  have hxy' := congrArg Subtype.val hxy
  change a8LeftSubextensionEmbedding f x.1 =
    a8LeftSubextensionEmbedding f y.1 at hxy'
  exact hxy'

public theorem a8LeftSubextensionProjection_ker_isTwoGroup
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hkerTwo : IsPGroup 2 f.ker) :
    IsPGroup 2 (a8LeftSubextensionProjection f).ker :=
  hkerTwo.of_injective (a8LeftSubextensionKernelEmbedding f)
    (a8LeftSubextensionKernelEmbedding_injective f)

public theorem exists_a8LeftSubextension_order_three_lift
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hkerTwo : IsPGroup 2 f.ker)
    (a : alternatingGroup (Fin 4)) (ha : orderOf a = 3) :
    ∃ x : a8LeftSubextension f,
      a8LeftSubextensionProjection f x = a ∧ orderOf x = 3 :=
  exists_order_three_lift_of_two_kernel
    (a8LeftSubextensionProjection f)
    (a8LeftSubextensionProjection_surjective f hf)
    (a8LeftSubextensionProjection_ker_isTwoGroup f hkerTwo) a ha

public theorem a8RightSubextensionEmbedding_eq_left_of_mem_ker
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : a8LeftSubextension f)
    (hx : x ∈ (a8LeftSubextensionProjection f).ker) :
    a8RightSubextensionEmbedding f hf x =
      a8LeftSubextensionEmbedding f x := by
  have hxGlobal : a8LeftSubextensionEmbedding f x ∈ f.ker := by
    rw [MonoidHom.mem_ker, a8LeftSubextensionEmbedding_fac]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact map_one (alternatingProdBlockHom 4 4)
  have hxCenter := hker hxGlobal
  change a8BlockSwapLift f hf * a8LeftSubextensionEmbedding f x *
      (a8BlockSwapLift f hf)⁻¹ = a8LeftSubextensionEmbedding f x
  rw [Subgroup.mem_center_iff.mp hxCenter (a8BlockSwapLift f hf)]
  group

public theorem a8_order_three_left_commutes_right
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (x y : a8LeftSubextension f)
    (hx : orderOf x = 3) :
    Commute (a8LeftSubextensionEmbedding f x)
      (a8RightSubextensionEmbedding f hf y) := by
  let lx := a8LeftSubextensionEmbedding f x
  let ry := a8RightSubextensionEmbedding f hf y
  let c : H := ⁅lx, ry⁆
  have hcKer : c ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    rw [a8LeftSubextensionEmbedding_fac,
      a8RightSubextensionEmbedding_fac]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [← map_mul, ← map_mul]
    congr 1
  have hcCenter : c ∈ Subgroup.center H := hker hcKer
  have hconj (z : H) : z * c * z⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hcCenter z]
    group
  have hlx3 : lx ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := by
      simpa [hx] using (pow_orderOf_eq_one x)
    exact congrArg (a8LeftSubextensionEmbedding f) hx3
  have hxx : ⁅lx * lx, ry⁆ = c ^ 2 := by
    calc
      ⁅lx * lx, ry⁆ = lx * c * lx⁻¹ * c := by
        simpa [c] using
          (commutatorElement_mul_left_eq_conj_mul lx lx ry)
      _ = c * c := by rw [hconj lx]
      _ = c ^ 2 := by rw [pow_two]
  have hxxx : ⁅(lx * lx) * lx, ry⁆ = c ^ 3 := by
    calc
      ⁅(lx * lx) * lx, ry⁆ =
          (lx * lx) * c * (lx * lx)⁻¹ * ⁅lx * lx, ry⁆ := by
        simpa [c] using
          (commutatorElement_mul_left_eq_conj_mul (lx * lx) lx ry)
      _ = c * c ^ 2 := by rw [hconj (lx * lx), hxx]
      _ = c ^ 3 := by group
  have hc3 : c ^ 3 = 1 := by
    rw [← hxxx]
    have hcube : (lx * lx) * lx = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hlx3
    rw [hcube, commutatorElement_one_left]
  let ck : f.ker := ⟨c, hcKer⟩
  have hdiv : orderOf ck ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    exact hc3
  have hcop : Nat.Coprime (orderOf ck) 3 :=
    hkerTwo.orderOf_coprime (by decide : Nat.Coprime 2 3) ck
  have hord : orderOf ck = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv
  have hck : ck = 1 := orderOf_eq_one_iff.mp hord
  apply commutatorElement_eq_one_iff_commute.mp
  exact congrArg Subtype.val hck

public theorem a8_left_right_commute
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (x y : a8LeftSubextension f) :
    Commute (a8LeftSubextensionEmbedding f x)
      (a8RightSubextensionEmbedding f hf y) := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    a4_exists_mul_order_three (a8LeftSubextensionProjection f x)
  obtain ⟨xa, hxa, hxa3⟩ :=
    exists_a8LeftSubextension_order_three_lift f hf hkerTwo a ha
  obtain ⟨xb, hxb, hxb3⟩ :=
    exists_a8LeftSubextension_order_three_lift f hf hkerTwo b hb
  let k : a8LeftSubextension f := x * (xa * xb)⁻¹
  have hk : k ∈ (a8LeftSubextensionProjection f).ker := by
    rw [MonoidHom.mem_ker]
    dsimp [k]
    rw [map_mul, map_inv, map_mul, hxa, hxb, hab]
    group
  have hkGlobal : a8LeftSubextensionEmbedding f k ∈ f.ker := by
    rw [MonoidHom.mem_ker, a8LeftSubextensionEmbedding_fac]
    rw [MonoidHom.mem_ker] at hk
    rw [hk]
    exact map_one (alternatingProdBlockHom 4 4)
  have hkCenter := hker hkGlobal
  have hka : Commute (a8LeftSubextensionEmbedding f xa)
      (a8RightSubextensionEmbedding f hf y) :=
    a8_order_three_left_commutes_right f hf hker hkerTwo xa y hxa3
  have hkb : Commute (a8LeftSubextensionEmbedding f xb)
      (a8RightSubextensionEmbedding f hf y) :=
    a8_order_three_left_commutes_right f hf hker hkerTwo xb y hxb3
  have hkComm : Commute (a8LeftSubextensionEmbedding f k)
      (a8RightSubextensionEmbedding f hf y) :=
    (Subgroup.mem_center_iff.mp hkCenter
      (a8RightSubextensionEmbedding f hf y)).symm
  have hall := Commute.mul_left hkComm (Commute.mul_left hka hkb)
  have hdecomp :
      a8LeftSubextensionEmbedding f k *
          (a8LeftSubextensionEmbedding f xa *
            a8LeftSubextensionEmbedding f xb) =
        a8LeftSubextensionEmbedding f x := by
    rw [← map_mul, ← map_mul]
    dsimp [k]
    group
  rw [hdecomp] at hall
  exact hall

public noncomputable def a8FusedProduct
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    a8LeftSubextension f × a8LeftSubextension f →* H :=
  (a8LeftSubextensionEmbedding f).noncommCoprod
    (a8RightSubextensionEmbedding f hf)
    (a8_left_right_commute f hf hker hkerTwo)

public theorem a8FusedProduct_fac
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (z : a8LeftSubextension f × a8LeftSubextension f) :
    f (a8FusedProduct f hf hker hkerTwo z) =
      alternatingProdBlockHom 4 4
        (a8LeftSubextensionProjection f z.1,
          a8LeftSubextensionProjection f z.2) := by
  rw [a8FusedProduct, MonoidHom.noncommCoprod_apply, map_mul,
    a8LeftSubextensionEmbedding_fac, a8RightSubextensionEmbedding_fac]
  rw [← map_mul]
  congr 1

public noncomputable def a8FusedProductToBlockPreimage
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    a8LeftSubextension f × a8LeftSubextension f →*
      alternatingBlockPreimage 4 4 f :=
  (a8FusedProduct f hf hker hkerTwo).codRestrict
    (alternatingBlockPreimage 4 4 f) (by
      intro z
      refine ⟨(a8LeftSubextensionProjection f z.1,
        a8LeftSubextensionProjection f z.2), ?_⟩
      exact (a8FusedProduct_fac f hf hker hkerTwo z).symm)

public theorem a8FusedProductToBlockPreimage_projection_fac
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (z : a8LeftSubextension f × a8LeftSubextension f) :
    alternatingBlockPreimageProjection 4 4 f
        (a8FusedProductToBlockPreimage f hf hker hkerTwo z) =
      (a8LeftSubextensionProjection f z.1,
        a8LeftSubextensionProjection f z.2) := by
  apply alternatingProdBlockHom_injective 4 4
  calc
    alternatingProdBlockHom 4 4
        (alternatingBlockPreimageProjection 4 4 f
          (a8FusedProductToBlockPreimage f hf hker hkerTwo z)) =
        f (a8FusedProductToBlockPreimage f hf hker hkerTwo z) :=
      alternatingBlockPreimageProjection_fac 4 4 f _
    _ = f (a8FusedProduct f hf hker hkerTwo z) := rfl
    _ = alternatingProdBlockHom 4 4
        (a8LeftSubextensionProjection f z.1,
          a8LeftSubextensionProjection f z.2) :=
      a8FusedProduct_fac f hf hker hkerTwo z

public theorem a8FusedProductToBlockPreimage_projection_surjective
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    Function.Surjective
      ((alternatingBlockPreimageProjection 4 4 f).comp
        (a8FusedProductToBlockPreimage f hf hker hkerTwo)) := by
  intro z
  obtain ⟨x, hx⟩ := a8LeftSubextensionProjection_surjective f hf z.1
  obtain ⟨y, hy⟩ := a8LeftSubextensionProjection_surjective f hf z.2
  refine ⟨(x, y), ?_⟩
  rw [MonoidHom.comp_apply,
    a8FusedProductToBlockPreimage_projection_fac, hx, hy]

public def a8LeftKernelToBlockPreimage
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    (a8LeftSubextensionProjection f).ker →*
      alternatingBlockPreimage 4 4 f :=
  (a8LeftSubextensionToBlockPreimage f).comp
    (a8LeftSubextensionProjection f).ker.subtype

public theorem a8LeftKernelToBlockPreimage_injective
    {H : Type} [Group H]
    (f : H →* alternatingGroup (Fin 8)) :
    Function.Injective (a8LeftKernelToBlockPreimage f) := by
  intro x y hxy
  apply Subtype.ext
  apply a8LeftSubextensionToBlockPreimage_injective f
  change a8LeftSubextensionToBlockPreimage f x.1 =
    a8LeftSubextensionToBlockPreimage f y.1 at hxy
  exact hxy

public theorem commutator_le_range_of_surjective_comp_of_ker_le_center
    {E X Q : Type*} [Group E] [Group X] [Group Q]
    (r : E →* Q) (g : X →* E)
    (hrg : Function.Surjective (r.comp g))
    (hker : r.ker ≤ Subgroup.center E) :
    commutator E ≤ g.range := by
  change ⁅(⊤ : Subgroup E), ⊤⁆ ≤ g.range
  rw [Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha⟩ := hrg (r x)
  obtain ⟨b, hb⟩ := hrg (r y)
  have ha' : r (g a) = r x := by simpa using ha
  have hb' : r (g b) = r y := by simpa using hb
  let kx : E := x * (g a)⁻¹
  let ky : E := y * (g b)⁻¹
  have hkx : kx ∈ r.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [kx]
    rw [map_mul, map_inv, ha']
    group
  have hky : ky ∈ r.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [ky]
    rw [map_mul, map_inv, hb']
    group
  have hx : x = kx * g a := by
    dsimp [kx]
    group
  have hy : y = ky * g b := by
    dsimp [ky]
    group
  have hcomm : ⁅x, y⁆ = ⁅g a, g b⁆ := by
    calc
      ⁅x, y⁆ = ⁅kx * g a, ky * g b⁆ := by rw [hx, hy]
      _ = ⁅g a, ky * g b⁆ :=
        commutatorElement_mul_left_of_center kx (g a) (ky * g b)
          (hker hkx)
      _ = ⁅g a, g b⁆ :=
        commutatorElement_mul_right_of_center (g a) ky (g b)
          (hker hky)
  refine ⟨⁅a, b⁆, ?_⟩
  rw [map_commutatorElement]
  exact hcomm.symm

public theorem a8LeftKernel_range_eq_fusedKernelRange
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    (a8LeftKernelToBlockPreimage f).range =
      (alternatingBlockPreimageProjection 4 4 f).ker ⊓
        (a8FusedProductToBlockPreimage f hf hker hkerTwo).range := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    constructor
    · change alternatingBlockPreimageProjection 4 4 f
          (a8LeftSubextensionToBlockPreimage f k.1) = 1
      rw [a8LeftSubextensionToBlockPreimage_projection_fac]
      have hk := MonoidHom.mem_ker.mp k.2
      rw [hk]
      rfl
    · refine ⟨(k.1, 1), ?_⟩
      apply Subtype.ext
      change a8FusedProduct f hf hker hkerTwo (k.1, 1) =
        a8LeftSubextensionEmbedding f k.1
      rw [a8FusedProduct, MonoidHom.noncommCoprod_apply]
      simp
  · intro hz
    obtain ⟨__ch5_Theorem523Core1_w, hw⟩ := hz.2
    have hp :
        (a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.1,
          a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.2) = 1 := by
      calc
        (a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.1,
            a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.2) =
            alternatingBlockPreimageProjection 4 4 f
              (a8FusedProductToBlockPreimage f hf hker hkerTwo __ch5_Theorem523Core1_w) :=
          (a8FusedProductToBlockPreimage_projection_fac
            f hf hker hkerTwo __ch5_Theorem523Core1_w).symm
        _ = alternatingBlockPreimageProjection 4 4 f z :=
          congrArg (alternatingBlockPreimageProjection 4 4 f) hw
        _ = 1 := MonoidHom.mem_ker.mp hz.1
    have hp1 : a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.1 = 1 := by
      simpa using congrArg Prod.fst hp
    have hp2 : a8LeftSubextensionProjection f __ch5_Theorem523Core1_w.2 = 1 := by
      simpa using congrArg Prod.snd hp
    let k : (a8LeftSubextensionProjection f).ker :=
      ⟨__ch5_Theorem523Core1_w.1 * __ch5_Theorem523Core1_w.2, by
        rw [MonoidHom.mem_ker, map_mul, hp1, hp2, one_mul]⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change a8LeftSubextensionEmbedding f (__ch5_Theorem523Core1_w.1 * __ch5_Theorem523Core1_w.2) = (z : H)
    calc
      a8LeftSubextensionEmbedding f (__ch5_Theorem523Core1_w.1 * __ch5_Theorem523Core1_w.2) =
          a8LeftSubextensionEmbedding f __ch5_Theorem523Core1_w.1 *
            a8LeftSubextensionEmbedding f __ch5_Theorem523Core1_w.2 := map_mul _ _ _
      _ = a8LeftSubextensionEmbedding f __ch5_Theorem523Core1_w.1 *
          a8RightSubextensionEmbedding f hf __ch5_Theorem523Core1_w.2 :=
        congrArg (a8LeftSubextensionEmbedding f __ch5_Theorem523Core1_w.1 * ·)
          (a8RightSubextensionEmbedding_eq_left_of_mem_ker
            f hf hker __ch5_Theorem523Core1_w.2 hp2).symm
      _ = a8FusedProduct f hf hker hkerTwo __ch5_Theorem523Core1_w := by
        rw [a8FusedProduct, MonoidHom.noncommCoprod_apply]
      _ = (a8FusedProductToBlockPreimage f hf hker hkerTwo __ch5_Theorem523Core1_w : H) := rfl
      _ = (z : H) := congrArg Subtype.val hw

public theorem natCard_a8BlockCommutatorKernel_le_two
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    Nat.card (((alternatingBlockPreimageProjection 4 4 f).ker ⊓
      commutator (alternatingBlockPreimage 4 4 f)) :
        Subgroup (alternatingBlockPreimage 4 4 f)) ≤ 2 := by
  let r := alternatingBlockPreimageProjection 4 4 f
  let g := a8FusedProductToBlockPreimage f hf hker hkerTwo
  let j := a8LeftKernelToBlockPreimage f
  have hrker : r.ker ≤ Subgroup.center (alternatingBlockPreimage 4 4 f) :=
    alternatingBlockPreimageProjection_ker_le_center 4 4 f hker
  have hcomm : commutator (alternatingBlockPreimage 4 4 f) ≤ g.range :=
    commutator_le_range_of_surjective_comp_of_ker_le_center r g
      (a8FusedProductToBlockPreimage_projection_surjective
        f hf hker hkerTwo) hrker
  have hrange : j.range = r.ker ⊓ g.range :=
    a8LeftKernel_range_eq_fusedKernelRange f hf hker hkerTwo
  have hle : r.ker ⊓ commutator (alternatingBlockPreimage 4 4 f) ≤
      j.range := by
    intro x hx
    rw [hrange]
    exact ⟨hx.1, hcomm hx.2⟩
  calc
    Nat.card ((r.ker ⊓ commutator (alternatingBlockPreimage 4 4 f)) :
        Subgroup (alternatingBlockPreimage 4 4 f)) ≤
        Nat.card j.range := Subgroup.card_le_of_le hle
    _ = Nat.card (a8LeftSubextensionProjection f).ker := by
      rw [MonoidHom.range_eq_map,
        Subgroup.card_map_of_injective
          (a8LeftKernelToBlockPreimage_injective f), Subgroup.card_top]
    _ ≤ 2 := natCard_a8LeftSubextensionProjection_ker_le_two f hf hker

public theorem natCard_a8FusedKernelRange_le_two
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker) :
    Nat.card (((alternatingBlockPreimageProjection 4 4 f).ker ⊓
      (a8FusedProductToBlockPreimage f hf hker hkerTwo).range) :
        Subgroup (alternatingBlockPreimage 4 4 f)) ≤ 2 := by
  rw [← a8LeftKernel_range_eq_fusedKernelRange f hf hker hkerTwo,
    MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective
      (a8LeftKernelToBlockPreimage_injective f), Subgroup.card_top]
  exact natCard_a8LeftSubextensionProjection_ker_le_two f hf hker

public theorem a4_prod_exists_mul_order_three
    (z : alternatingGroup (Fin 4) × alternatingGroup (Fin 4)) :
    ∃ a b : alternatingGroup (Fin 4) × alternatingGroup (Fin 4),
      orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = z := by
  obtain ⟨a1, b1, ha1, hb1, hab1⟩ := a4_exists_mul_order_three z.1
  obtain ⟨a2, b2, ha2, hb2, hab2⟩ := a4_exists_mul_order_three z.2
  refine ⟨(a1, a2), (b1, b2), ?_, ?_, ?_⟩
  · rw [Prod.orderOf_mk, ha1, ha2, Nat.lcm_self]
  · rw [Prod.orderOf_mk, hb1, hb2, Nat.lcm_self]
  · exact Prod.ext hab1 hab2

public theorem subgroups_eq_of_surjective_of_same_kernel_intersection_of_order_three
    {E Q : Type*} [Group E] [Finite E] [Group Q] [Finite Q]
    (r : E →* Q)
    (hker : r.ker ≤ Subgroup.center E)
    (hkerTwo : IsPGroup 2 r.ker)
    (hprod : ∀ q : Q, ∃ a b : Q,
      orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = q)
    (M N C : Subgroup E)
    (hM : Function.Surjective (r.comp M.subtype))
    (hN : Function.Surjective (r.comp N.subtype))
    (hMC : r.ker ⊓ M = C)
    (hNC : r.ker ⊓ N = C) :
    M = N := by
  let rM : M →* Q := r.comp M.subtype
  let rN : N →* Q := r.comp N.subtype
  have hkerM : IsPGroup 2 rM.ker := by
    let i : rM.ker →* r.ker :=
      ((M.subtype.comp rM.ker.subtype).codRestrict r.ker (by
        intro x
        exact x.2))
    apply hkerTwo.of_injective i
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : r.ker => (z : E)) hxy
  have hkerN : IsPGroup 2 rN.ker := by
    let i : rN.ker →* r.ker :=
      ((N.subtype.comp rN.ker.subtype).codRestrict r.ker (by
        intro x
        exact x.2))
    apply hkerTwo.of_injective i
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : r.ker => (z : E)) hxy
  have unique_order_three_lift
      (m : M) (n : N) (hm : rM m = rN n)
      (hm3 : orderOf m = 3) (hn3 : orderOf n = 3) :
      (m : E) = (n : E) := by
    let k : E := (m : E) * (n : E)⁻¹
    have hk : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv]
      change rM m * (rN n)⁻¹ = 1
      rw [hm]
      group
    have hkCenter := hker hk
    have hkm : (m : E) = k * (n : E) := by
      dsimp [k]
      group
    have hmPow : (m : E) ^ 3 = 1 := by
      have hm' : m ^ 3 = 1 := by
        simpa [hm3] using (pow_orderOf_eq_one m)
      exact congrArg Subtype.val hm'
    have hnPow : (n : E) ^ 3 = 1 := by
      have hn' : n ^ 3 = 1 := by
        simpa [hn3] using (pow_orderOf_eq_one n)
      exact congrArg Subtype.val hn'
    have hkn : Commute k (n : E) :=
      (Subgroup.mem_center_iff.mp hkCenter (n : E)).symm
    have hk3 : k ^ 3 = 1 := by
      calc
        k ^ 3 = k ^ 3 * (n : E) ^ 3 := by rw [hnPow, mul_one]
        _ = (k * (n : E)) ^ 3 := (hkn.mul_pow 3).symm
        _ = (m : E) ^ 3 := by rw [hkm]
        _ = 1 := hmPow
    let k0 : r.ker := ⟨k, hk⟩
    have hdiv : orderOf k0 ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      exact hk3
    have hcop : Nat.Coprime (orderOf k0) 3 :=
      hkerTwo.orderOf_coprime (by decide : Nat.Coprime 2 3) k0
    have hord : orderOf k0 = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv
    have hk1 : k = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
    rw [hkm, hk1, one_mul]
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ := hprod (r x)
    obtain ⟨ma, hma, hma3⟩ :=
      exists_order_three_lift_of_two_kernel rM hM hkerM a ha
    obtain ⟨mb, hmb, hmb3⟩ :=
      exists_order_three_lift_of_two_kernel rM hM hkerM b hb
    obtain ⟨na, hna, hna3⟩ :=
      exists_order_three_lift_of_two_kernel rN hN hkerN a ha
    obtain ⟨nb, hnb, hnb3⟩ :=
      exists_order_three_lift_of_two_kernel rN hN hkerN b hb
    have hea : (ma : E) = (na : E) :=
      unique_order_three_lift ma na (hma.trans hna.symm) hma3 hna3
    have heb : (mb : E) = (nb : E) :=
      unique_order_three_lift mb nb (hmb.trans hnb.symm) hmb3 hnb3
    let k : E := (x : E) * ((ma : E) * (mb : E))⁻¹
    have hkKer : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, map_mul]
      change r x * (rM ma * rM mb)⁻¹ = 1
      rw [hma, hmb, hab]
      group
    have hkM : k ∈ M := by
      dsimp [k]
      exact M.mul_mem hx (M.inv_mem (M.mul_mem ma.2 mb.2))
    have hkC : k ∈ C := by
      rw [← hMC]
      exact ⟨hkKer, hkM⟩
    have hkN : k ∈ N := by
      have : k ∈ r.ker ⊓ N := hNC.symm ▸ hkC
      exact this.2
    have hnaN : (na : E) ∈ N := na.2
    have hnbN : (nb : E) ∈ N := nb.2
    have hmaN : (ma : E) ∈ N := hea ▸ hnaN
    have hmbN : (mb : E) ∈ N := heb ▸ hnbN
    have hdecomp : (x : E) = k * ((ma : E) * (mb : E)) := by
      dsimp [k]
      group
    rw [hdecomp]
    exact N.mul_mem hkN (N.mul_mem hmaN hmbN)
  · intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ := hprod (r x)
    obtain ⟨ma, hma, hma3⟩ :=
      exists_order_three_lift_of_two_kernel rM hM hkerM a ha
    obtain ⟨mb, hmb, hmb3⟩ :=
      exists_order_three_lift_of_two_kernel rM hM hkerM b hb
    obtain ⟨na, hna, hna3⟩ :=
      exists_order_three_lift_of_two_kernel rN hN hkerN a ha
    obtain ⟨nb, hnb, hnb3⟩ :=
      exists_order_three_lift_of_two_kernel rN hN hkerN b hb
    have hea : (ma : E) = (na : E) :=
      unique_order_three_lift ma na (hma.trans hna.symm) hma3 hna3
    have heb : (mb : E) = (nb : E) :=
      unique_order_three_lift mb nb (hmb.trans hnb.symm) hmb3 hnb3
    let k : E := (x : E) * ((na : E) * (nb : E))⁻¹
    have hkKer : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, map_mul]
      change r x * (rN na * rN nb)⁻¹ = 1
      rw [hna, hnb, hab]
      group
    have hkN : k ∈ N := by
      dsimp [k]
      exact N.mul_mem hx (N.inv_mem (N.mul_mem na.2 nb.2))
    have hkC : k ∈ C := by
      rw [← hNC]
      exact ⟨hkKer, hkN⟩
    have hkM : k ∈ M := by
      have : k ∈ r.ker ⊓ M := hMC.symm ▸ hkC
      exact this.2
    have hmaM : (ma : E) ∈ M := ma.2
    have hmbM : (mb : E) ∈ M := mb.2
    have hnaM : (na : E) ∈ M := hea ▸ hmaM
    have hnbM : (nb : E) ∈ M := heb ▸ hmbM
    have hdecomp : (x : E) = k * ((na : E) * (nb : E)) := by
      dsimp [k]
      group
    rw [hdecomp]
    exact M.mul_mem hkM (M.mul_mem hnaM hnbM)

public theorem subgroup_map_eq_self_of_surjective_of_fixed_two_kernel
    {E Q : Type*} [Group E] [Finite E] [Group Q] [Finite Q]
    (r : E →* Q)
    (hker : r.ker ≤ Subgroup.center E)
    (hkerTwo : IsPGroup 2 r.ker)
    (hprod : ∀ q : Q, ∃ a b : Q,
      orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = q)
    (M : Subgroup E)
    (hM : Function.Surjective (r.comp M.subtype))
    (e : E ≃* E)
    (heKer : ∀ x : E, x ∈ r.ker → e x = x)
    (hMap : Function.Surjective
      (r.comp (M.map e.toMonoidHom).subtype)) :
    M.map e.toMonoidHom = M := by
  have hinter : r.ker ⊓ M.map e.toMonoidHom = r.ker ⊓ M := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hmM, hem⟩ := hx.2
      have hex : e x = x := heKer x hx.1
      have hmx : m = x := e.injective (hem.trans hex.symm)
      exact ⟨hx.1, hmx ▸ hmM⟩
    · intro hx
      refine ⟨hx.1, ⟨x, hx.2, ?_⟩⟩
      exact heKer x hx.1
  exact subgroups_eq_of_surjective_of_same_kernel_intersection_of_order_three
    r hker hkerTwo hprod (M.map e.toMonoidHom) M (r.ker ⊓ M)
      hMap hM hinter rfl

public theorem mapsTo_compl_of_mapsTo_perm
    {X : Type} (g : Equiv.Perm X) (S : Set X)
    (hinv : Set.MapsTo g.symm S S) :
    Set.MapsTo g Sᶜ Sᶜ := by
  intro x hx hgx
  exact hx (by simpa using hinv hgx)

public theorem natCard_ker_le_two_of_invariant_two_subset
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (S : Set (Fin m))
    (hS : Nat.card S = 2)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = q + 5)
    (hmaps : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S) :
    Nat.card f.ker ≤ 2 := by
  have hmapsSc : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) Sᶜ Sᶜ := by
    intro x
    exact mapsTo_compl_of_mapsTo_perm
      (f (x : H) : Equiv.Perm (Fin m)) S (by
        simpa using hmaps (x⁻¹))
  obtain ⟨f', hfker, hf', hP⟩ :=
    exists_relabelled_evenBlock_extension_of_sylow_mapsTo_subset
      m (q + 5) 2 f hf P Sᶜ hSc (by
        simpa only [compl_compl] using hS) hmapsSc
  have hker' : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hkerTwo' : IsPGroup 2 f'.ker := by
    rw [hfker]
    exact hkerTwo
  have hbound := natCard_ker_le_two_of_sylow_le_evenBlockPreimage_two
    q hM f' hf' hker' hkerTwo' P hP
  rwa [hfker] at hbound

public theorem natCard_ker_le_two_of_invariant_four_subset
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (S : Set (Fin m))
    (hS : Nat.card S = 4)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = q + 5)
    (hmaps : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S) :
    Nat.card f.ker ≤ 2 := by
  have hmapsSc : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) Sᶜ Sᶜ := by
    intro x
    exact mapsTo_compl_of_mapsTo_perm
      (f (x : H) : Equiv.Perm (Fin m)) S (by
        simpa using hmaps (x⁻¹))
  obtain ⟨f', hfker, hf', hP⟩ :=
    exists_relabelled_evenBlock_extension_of_sylow_mapsTo_subset
      m (q + 5) 4 f hf P Sᶜ hSc (by
        simpa only [compl_compl] using hS) hmapsSc
  have hker' : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hkerTwo' : IsPGroup 2 f'.ker := by
    rw [hfker]
    exact hkerTwo
  have hbound := natCard_ker_le_two_of_sylow_le_evenBlockPreimage_four
    q hM f' hf' hker' hkerTwo' P hP
  rwa [hfker] at hbound

public theorem natCard_ker_le_two_of_invariant_equal_large_subset
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (hqEven : Even (q + 5))
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (S : Set (Fin m))
    (hS : Nat.card S = q + 5)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = q + 5)
    (hmaps : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S) :
    Nat.card f.ker ≤ 2 := by
  obtain ⟨f', hfker, hf', hP⟩ :=
    exists_relabelled_evenBlock_extension_of_sylow_mapsTo_subset
      m (q + 5) (q + 5) f hf P S hS hSc hmaps
  have hker' : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hkerTwo' : IsPGroup 2 f'.ker := by
    rw [hfker]
    exact hkerTwo
  have hbound :=
    natCard_ker_le_two_of_sylow_le_evenBlockPreimage_equal_blocks
      q hM hqEven f' hf' hker' hkerTwo' P hP
  rwa [hfker] at hbound

public theorem natCard_ker_le_two_of_invariant_unequal_large_subset
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m qA qB : Nat)
    (hMA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (hMB : Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker ≤ 2)
    (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (S : Set (Fin m))
    (hS : Nat.card S = qA + 5)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = qB + 5)
    (hmaps : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S) :
    Nat.card f.ker ≤ 2 := by
  obtain ⟨f', hfker, hf', hP⟩ :=
    exists_relabelled_evenBlock_extension_of_sylow_mapsTo_subset
      m (qA + 5) (qB + 5) f hf P S hS hSc hmaps
  have hker' : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hkerTwo' : IsPGroup 2 f'.ker := by
    rw [hfker]
    exact hkerTwo
  have hbound :=
    natCard_ker_le_two_of_sylow_le_evenBlockPreimage_unequal_blocks
      qA qB hMA hMB hA hB f' hf' hker' hkerTwo' P hP
  rwa [hfker] at hbound


end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523Core1 -/

/- BEGIN Theory.PrimeCycleRotationCoordinates -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_PrimeCycleRotationCoordinates_u

/-- Coordinates on the independent rotations of a prime-order permutation,
indexed by its nontrivial cycles. -/
@[expose]
public noncomputable def primeCycleRotationCoordinates
    {Ω : Type __ch5_PrimeCycleRotationCoordinates_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime) :
    CycleRotationGroup x ≃*
      ((c : x.cycleFactorsFinset) →
        Multiplicative (ZMod (orderOf x))) := by
  apply MulEquiv.piCongrRight
  intro c
  exact (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
    (cycleFactorZPowers_card_of_primeOrder x hx c)).symm

@[simp]
public theorem primeCycleRotationCoordinates_apply
    {Ω : Type __ch5_PrimeCycleRotationCoordinates_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime)
    (a : CycleRotationGroup x) (c : x.cycleFactorsFinset) :
    primeCycleRotationCoordinates x hx a c =
      (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
        (cycleFactorZPowers_card_of_primeOrder x hx c)).symm (a c) := rfl

end GLS3.Chapter5
/- END Theory.PrimeCycleRotationCoordinates -/

/- BEGIN Theory.Theorem523Core -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523Core_w

namespace GLS3.Chapter5.SchurPresentation

public theorem exists_invariant_two_subset_of_invariant_six_subset
    (m : Nat)
    (Q : Sylow 2 (alternatingGroup (Fin m)))
    (S : Set (Fin m))
    (hS : Nat.card S = 6)
    (hmaps : ∀ q : Q, Set.MapsTo
      ((q : alternatingGroup (Fin m)) : Fin m → Fin m) S S) :
    ∃ T : Set (Fin m),
      Nat.card T = 2 ∧ T ⊆ S ∧
        ∀ q : Q, Set.MapsTo
          ((q : alternatingGroup (Fin m)) : Fin m → Fin m) T T := by
  classical
  by_cases horbitTwo :
      ∃ y : Fin m, y ∈ S ∧ Nat.card (MulAction.orbit Q y) = 2
  · obtain ⟨y, hyS, hycard⟩ := horbitTwo
    refine ⟨MulAction.orbit Q y, hycard, ?_, ?_⟩
    · intro z hz
      obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hz
      exact hmaps q hyS
    · intro q
      exact MulAction.mapsTo_smul_orbit q y
  by_cases horbitFour :
      ∃ y : Fin m, y ∈ S ∧ Nat.card (MulAction.orbit Q y) = 4
  · obtain ⟨y, hyS, hycard⟩ := horbitFour
    let O : Set (Fin m) := MulAction.orbit Q y
    have hOS : O ⊆ S := by
      intro z hz
      obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hz
      exact hmaps q hyS
    refine ⟨S \ O, ?_, Set.sdiff_subset, ?_⟩
    · have hcard := Set.ncard_sdiff_add_ncard_of_subset hOS
      have hScard : S.ncard = 6 := by
        simpa only [Nat.card_coe_set_eq] using hS
      have hOcard : O.ncard = 4 := by
        simpa only [O, Nat.card_coe_set_eq] using hycard
      have hdiff : (S \ O).ncard = 2 := by omega
      simpa only [Nat.card_coe_set_eq] using hdiff
    · intro q z hz
      refine ⟨hmaps q hz.1, ?_⟩
      intro hqz
      have hback := MulAction.mapsTo_smul_orbit (q⁻¹) y hqz
      change (q⁻¹ : Q) • (q • z) ∈ O at hback
      exact hz.2 (by simpa only [inv_smul_smul] using hback)
  have hfixed : ∀ y : Fin m, y ∈ S →
      y ∈ MulAction.fixedPoints Q (Fin m) := by
    intro y hyS
    rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
    obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
    have horbitSub : MulAction.orbit Q y ⊆ S := by
      intro z hz
      obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hz
      exact hmaps q hyS
    have hle : Nat.card (MulAction.orbit Q y) ≤ 6 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard horbitSub).trans_eq
        (by simpa only [Nat.card_coe_set_eq] using hS)
    have hrlt : r < 3 := by
      by_contra hrnot
      have hpow : 2 ^ 3 ≤ 2 ^ r :=
        pow_le_pow_right₀ (by omega : 1 ≤ 2) (by omega)
      rw [← hr] at hpow
      omega
    have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hrCases with rfl | rfl | rfl
    · simpa only [Nat.card_eq_fintype_card, pow_zero] using hr
    · exfalso
      apply horbitTwo
      exact ⟨y, hyS, by simpa only [pow_one] using hr⟩
    · exfalso
      apply horbitFour
      exact ⟨y, hyS, by
        calc
          Nat.card (MulAction.orbit Q y) = 2 ^ 2 := hr
          _ = 4 := by norm_num⟩
  let eS : Fin 6 ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let j : Fin 2 → Fin m := fun i =>
    (eS (Fin.castLE (by omega : 2 ≤ 6) i) : S)
  have hj : Function.Injective j := by
    intro i k hik
    apply Fin.castLE_injective (by omega : 2 ≤ 6)
    apply eS.injective
    exact Subtype.ext hik
  let T : Set (Fin m) := Set.range j
  refine ⟨T, ?_, ?_, ?_⟩
  · simp only [T, Nat.card_coe_set_eq, Set.ncard_range_of_injective hj]
    exact Nat.card_fin 2
  · rintro x ⟨i, rfl⟩
    exact (eS (Fin.castLE (by omega : 2 ≤ 6) i)).2
  · intro q x hx
    obtain ⟨i, rfl⟩ := hx
    have hfix := MulAction.mem_fixedPoints.mp
      (hfixed (j i) (eS (Fin.castLE (by omega : 2 ≤ 6) i)).2) q
    change q • j i ∈ T
    rw [hfix]
    exact ⟨i, rfl⟩

public theorem natCard_ker_le_two_of_even_degree_of_not_pretransitive_sylow
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m : Nat) (hm10 : 10 ≤ m) (hmeven : Even m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hnotTrans : ¬ MulAction.IsPretransitive
      (P.mapSurjective hf) (Fin m))
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m → d ≠ 6 → d ≠ 7 →
      Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker ≤ 2) :
    Nat.card f.ker ≤ 2 := by
  let Q : Sylow 2 (alternatingGroup (Fin m)) := P.mapSurjective hf
  have hmapsP (U : Set (Fin m))
      (hU : ∀ q : Q, Set.MapsTo
        ((q : alternatingGroup (Fin m)) : Fin m → Fin m) U U) :
      ∀ x : P, Set.MapsTo (f (x : H) : Fin m → Fin m) U U := by
    intro x
    let q : Q := ⟨f (x : H), ⟨x, x.2, rfl⟩⟩
    exact hU q
  have hmapsCompl (U : Set (Fin m))
      (hU : ∀ q : Q, Set.MapsTo
        ((q : alternatingGroup (Fin m)) : Fin m → Fin m) U U) :
      ∀ q : Q, Set.MapsTo
        ((q : alternatingGroup (Fin m)) : Fin m → Fin m) Uᶜ Uᶜ := by
    intro q
    exact mapsTo_compl_of_mapsTo_perm
      (q : Equiv.Perm (Fin m)) U (by simpa using hU (q⁻¹))
  have finish (T : Set (Fin m))
      (h2T : 2 ∣ Nat.card T) (hT2 : 2 ≤ Nat.card T)
      (h2Tc : 2 ∣ Nat.card (Tᶜ : Set (Fin m)))
      (hTc2 : 2 ≤ Nat.card (Tᶜ : Set (Fin m)))
      (hT6 : Nat.card T ≠ 6)
      (hTc6 : Nat.card (Tᶜ : Set (Fin m)) ≠ 6)
      (hmapsT : ∀ q : Q, Set.MapsTo
        ((q : alternatingGroup (Fin m)) : Fin m → Fin m) T T) :
      Nat.card f.ker ≤ 2 := by
    let a := Nat.card T
    let b := Nat.card (Tᶜ : Set (Fin m))
    have hsum : m = a + b := by
      have h := Set.ncard_add_ncard_compl T
      simpa [a, b, Nat.card_fin, add_comm] using h.symm
    have hmapsTP := hmapsP T hmapsT
    have hmapsTcP := hmapsP Tᶜ (hmapsCompl T hmapsT)
    have ha2 : 2 ≤ a := by simpa only [a] using hT2
    have hb2 : 2 ≤ b := by simpa only [b] using hTc2
    have h2a : 2 ∣ a := by simpa only [a] using h2T
    have h2b : 2 ∣ b := by simpa only [b] using h2Tc
    have ha6 : a ≠ 6 := by simpa only [a] using hT6
    have hb6 : b ≠ 6 := by simpa only [b] using hTc6
    by_cases haTwo : a = 2
    · let q := b - 5
      have hb8 : 8 ≤ b := by omega
      have hqb : q + 5 = b := by omega
      have hM := hsmall b (by omega) (by omega) hb6 (by omega)
      apply natCard_ker_le_two_of_invariant_two_subset
        m q (by simpa only [hqb] using hM) f hf hker hkerTwo P T
      · simpa only [a] using haTwo
      · change b = q + 5
        omega
      · exact hmapsTP
    by_cases hbTwo : b = 2
    · let q := a - 5
      have ha8 : 8 ≤ a := by omega
      have hqa : q + 5 = a := by omega
      have hM := hsmall a (by omega) (by omega) ha6 (by omega)
      apply natCard_ker_le_two_of_invariant_two_subset
        m q (by simpa only [hqa] using hM) f hf hker hkerTwo P Tᶜ
      · simpa only [b] using hbTwo
      · simpa only [compl_compl, a] using hqa.symm
      · exact hmapsTcP
    by_cases haFour : a = 4
    · let q := b - 5
      have hb8 : 8 ≤ b := by omega
      have hqb : q + 5 = b := by omega
      have hM := hsmall b (by omega) (by omega) hb6 (by omega)
      apply natCard_ker_le_two_of_invariant_four_subset
        m q (by simpa only [hqb] using hM) f hf hker hkerTwo P T
      · simpa only [a] using haFour
      · change b = q + 5
        omega
      · exact hmapsTP
    by_cases hbFour : b = 4
    · let q := a - 5
      have ha8 : 8 ≤ a := by omega
      have hqa : q + 5 = a := by omega
      have hM := hsmall a (by omega) (by omega) ha6 (by omega)
      apply natCard_ker_le_two_of_invariant_four_subset
        m q (by simpa only [hqa] using hM) f hf hker hkerTwo P Tᶜ
      · simpa only [b] using hbFour
      · simpa only [compl_compl, a] using hqa.symm
      · exact hmapsTcP
    have ha8 : 8 ≤ a := by
      obtain ⟨ka, hka⟩ := h2a
      omega
    have hb8 : 8 ≤ b := by
      obtain ⟨kb, hkb⟩ := h2b
      omega
    have haLt : a < m := by omega
    have hbLt : b < m := by omega
    have hMA := hsmall a (by omega) haLt ha6 (by omega)
    by_cases hab : a = b
    · let q := a - 5
      have hqa : q + 5 = a := by omega
      have hqEven : Even (q + 5) :=
        even_iff_two_dvd.mpr (by simpa only [hqa] using h2a)
      apply natCard_ker_le_two_of_invariant_equal_large_subset
        m q (by simpa only [hqa] using hMA) hqEven
        f hf hker hkerTwo P T
      · change a = q + 5
        omega
      · change b = q + 5
        omega
      · exact hmapsTP
    · let qA := a - 5
      let qB := b - 5
      have hqA : qA + 5 = a := by omega
      have hqB : qB + 5 = b := by omega
      have hMB := hsmall b (by omega) hbLt hb6 (by omega)
      apply natCard_ker_le_two_of_invariant_unequal_large_subset
        m qA qB (by simpa only [hqA] using hMA)
        (by simpa only [hqB] using hMB) (by omega) (by omega)
        f hf hker hkerTwo P T
      · change a = qA + 5
        omega
      · change b = qB + 5
        omega
      · exact hmapsTP
  obtain ⟨S, h2S, hS2, h2Sc, hSc2, hmapsS⟩ :=
    exists_invariant_even_proper_subset_of_not_pretransitive_sylow_two
      m (by omega) hmeven Q hnotTrans
  have hmapsSc := hmapsCompl S hmapsS
  by_cases hS6 : Nat.card S = 6
  · obtain ⟨T, hT2, -, hmapsT⟩ :=
      exists_invariant_two_subset_of_invariant_six_subset
        m Q S hS6 hmapsS
    have hsumT : m = Nat.card T + Nat.card (Tᶜ : Set (Fin m)) := by
      have h := Set.ncard_add_ncard_compl T
      simpa [Nat.card_fin, add_comm] using h.symm
    have h2T : 2 ∣ Nat.card T := by rw [hT2]
    have h2m : 2 ∣ m := even_iff_two_dvd.mp hmeven
    have h2Tc : 2 ∣ Nat.card (Tᶜ : Set (Fin m)) := by
      apply (Nat.dvd_add_iff_right h2T).mpr
      rwa [← hsumT]
    apply finish T h2T (by omega) h2Tc (by omega) (by omega) (by omega) hmapsT
  by_cases hSc6 : Nat.card (Sᶜ : Set (Fin m)) = 6
  · obtain ⟨T, hT2, -, hmapsT⟩ :=
      exists_invariant_two_subset_of_invariant_six_subset
        m Q Sᶜ hSc6 hmapsSc
    have hsumT : m = Nat.card T + Nat.card (Tᶜ : Set (Fin m)) := by
      have h := Set.ncard_add_ncard_compl T
      simpa [Nat.card_fin, add_comm] using h.symm
    have h2T : 2 ∣ Nat.card T := by rw [hT2]
    have h2m : 2 ∣ m := even_iff_two_dvd.mp hmeven
    have h2Tc : 2 ∣ Nat.card (Tᶜ : Set (Fin m)) := by
      apply (Nat.dvd_add_iff_right h2T).mpr
      rwa [← hsumT]
    apply finish T h2T (by omega) h2Tc (by omega) (by omega) (by omega) hmapsT
  exact finish S h2S hS2 h2Sc hSc2 hS6 hSc6 hmapsS

/- The wreath-product helper declarations for the universality proof are
   private to this module. -/
public theorem test_wreath_jE
    {H : Type} [Group H]
    (d : Nat) (hd : 2 ≤ d) (_heven : Even d)
    (f : H →* alternatingGroup (Fin (d + d)))
    (hf : Function.Surjective f) :
    let W := evenTwoBlockWreathPreimage d f
    let r := evenTwoBlockWreathPreimageProjection d hd f
    let A := evenTwoBlockWreathBase d
    let E : Subgroup W := A.comap r
    ∃ (jE : E →* alternatingBlockPreimage d d f),
      Function.Surjective jE ∧
        ∀ x : E, (jE x : H) = (W.subtype.comp E.subtype) x := by
  have _ := hf
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let W := evenTwoBlockWreathPreimage d f
  let r := evenTwoBlockWreathPreimageProjection d hd f
  let A := evenTwoBlockWreathBase d
  let E : Subgroup W := A.comap r
  have hEbase (x : E) :
      f (W.subtype (E.subtype x)) ∈
        (alternatingProdBlockHom d d).range := by
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, ?_⟩
    calc
      alternatingProdBlockHom d d y =
          evenTwoBlockWreathFinHom d (evenTwoBlockWreathBaseHom d y) :=
        (evenTwoBlockWreathBaseHom_ambient d y).symm
      _ = evenTwoBlockWreathFinHom d (r x) :=
        congrArg (evenTwoBlockWreathFinHom d) hy
      _ = f (W.subtype (E.subtype x)) :=
        evenTwoBlockWreathPreimageProjection_fac d hd f (E.subtype x)
  let jE : E →* alternatingBlockPreimage d d f :=
    (W.subtype.comp E.subtype).codRestrict _ hEbase
  have hjE : Function.Surjective jE := by
    intro z
    obtain ⟨y, hy⟩ := z.2
    have hfin : evenTwoBlockWreathFinHom d
          (evenTwoBlockWreathBaseHom d y) =
            (f z : alternatingGroup (Fin (d + d))) := by
      calc
        evenTwoBlockWreathFinHom d (evenTwoBlockWreathBaseHom d y) =
            alternatingProdBlockHom d d y :=
          evenTwoBlockWreathBaseHom_ambient d y
        _ = f z := hy
    let __ch5_Theorem523Core_w : W :=
      ⟨(z : H), ⟨evenTwoBlockWreathBaseHom d y, hfin⟩⟩
    have hrw : r __ch5_Theorem523Core_w = evenTwoBlockWreathBaseHom d y := by
      apply evenTwoBlockWreathFinHom_injective d
      calc
        evenTwoBlockWreathFinHom d (r __ch5_Theorem523Core_w) = f __ch5_Theorem523Core_w :=
          evenTwoBlockWreathPreimageProjection_fac d hd f __ch5_Theorem523Core_w
        _ = f z := rfl
        _ = evenTwoBlockWreathFinHom d (evenTwoBlockWreathBaseHom d y) :=
          hfin.symm
    let e : E := ⟨__ch5_Theorem523Core_w, ⟨y, hrw.symm⟩⟩
    refine ⟨e, ?_⟩
    apply Subtype.ext
    rfl
  exact ⟨jE, hjE, by intro x; rfl⟩

public theorem test_exists_wreath_base_lift
    {H : Type} [Group H] [Finite H]
    (q m : Nat) (hm4 : 4 ≤ m) (hdm : 2 * m = q + 5)
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (y : alternatingGroup (Fin (q + 5)) × alternatingGroup (Fin (q + 5)))
    (W : Subgroup H)
    (rW : W →* evenTwoBlockWreathGroup (q + 5))
    (E : Subgroup W)
    (jE : E →* alternatingBlockPreimage (q + 5) (q + 5) f)
    (hjE : Function.Surjective jE)
    (hfac : ∀ x : W,
      evenTwoBlockWreathFinHom (q + 5) (rW x) = f x)
    (hEbase : ∀ x : E,
      f ((W.subtype.comp E.subtype) x) ∈
        (alternatingProdBlockHom (q + 5) (q + 5)).range)
    (hjEval : ∀ x : E,
      (jE x : H) = (W.subtype.comp E.subtype) x) :
    ∃ e : E,
      rW e = evenTwoBlockWreathBaseHom (q + 5) y ∧
        e ∈ commutator E := by
  have _ := hm4
  have _ := hdm
  have _ := hEbase
  let A0 := alternatingBlockPreimage (q + 5) (q + 5) f
  let r0 := alternatingBlockPreimageProjection (q + 5) (q + 5) f
  obtain ⟨z, hz⟩ := hf (alternatingProdBlockHom (q + 5) (q + 5) y)
  let zE : A0 := ⟨z, ⟨y, hz.symm⟩⟩
  obtain ⟨k, l, hkl⟩ :=
    evenBlockComponentDerivedProduct_decomposition q q f hf hker zE
  have hzproj : r0 zE = y := by
    apply alternatingProdBlockHom_injective (q + 5) (q + 5)
    calc
      alternatingProdBlockHom (q + 5) (q + 5) (r0 zE) = f zE :=
        alternatingBlockPreimageProjection_fac
          (q + 5) (q + 5) f zE
      _ = alternatingProdBlockHom (q + 5) (q + 5) y := hz
  have hlproj : r0 (l : A0) = y := by
    have h := congrArg r0 hkl
    have hk1 : r0 (k : A0) = 1 := MonoidHom.mem_ker.mp k.2
    rw [map_mul, hk1, one_mul, hzproj] at h
    exact h
  have hfl : f (l : H) = alternatingProdBlockHom (q + 5) (q + 5) y := by
    calc
      f (l : H) = alternatingProdBlockHom (q + 5) (q + 5) (r0 (l : A0)) :=
        (alternatingBlockPreimageProjection_fac
          (q + 5) (q + 5) f (l : A0)).symm
      _ = alternatingProdBlockHom (q + 5) (q + 5) y := by rw [hlproj]
  have hcommL : (l : A0) ∈ commutator A0 := by
    rw [← evenBlockComponentDerivedProduct_eq_commutator q q f hf hker]
    exact l.2
  have hmap : (commutator E).map jE = commutator A0 := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hjE,
      commutator_def]
  have hlmap : (l : A0) ∈ (commutator E).map jE := by
    rw [hmap]
    exact hcommL
  obtain ⟨e, he, heval⟩ := hlmap
  have hecomm : e ∈ commutator E := he
  have heL : (jE e : H) = (l : H) := by
    exact congrArg (fun a : A0 => (a : H)) heval
  have hef : f ((W.subtype.comp E.subtype) e) =
      alternatingProdBlockHom (q + 5) (q + 5) y := by
    rw [← hjEval e, heL, hfl]
  have her : rW e = evenTwoBlockWreathBaseHom (q + 5) y := by
    apply evenTwoBlockWreathFinHom_injective (q + 5)
    calc
      evenTwoBlockWreathFinHom (q + 5) (rW e) = f e := hfac e
      _ = alternatingProdBlockHom (q + 5) (q + 5) y := hef
      _ = evenTwoBlockWreathFinHom (q + 5)
          (evenTwoBlockWreathBaseHom (q + 5) y) :=
        (evenTwoBlockWreathBaseHom_ambient (q + 5) y).symm
  exact ⟨e, her, hecomm⟩

public theorem test_exists_wreath_base_lift_a8
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (y : alternatingGroup (Fin 4) × alternatingGroup (Fin 4))
    (hy : y ∈ (alternatingGroup.kleinFour (Fin 4)).prod
      (alternatingGroup.kleinFour (Fin 4)))
    (W : Subgroup H)
    (rW : W →* evenTwoBlockWreathGroup 4)
    (E : Subgroup W)
    (jE : E →* alternatingBlockPreimage 4 4 f)
    (hjE : Function.Surjective jE)
    (hfac : ∀ x : W,
      evenTwoBlockWreathFinHom 4 (rW x) = f x)
    (hjEval : ∀ x : E,
      (jE x : H) = (W.subtype.comp E.subtype) x) :
    ∃ e : E,
      rW e = evenTwoBlockWreathBaseHom 4 y ∧
        e ∈ commutator E := by
  let A := alternatingGroup (Fin 4)
  let V := alternatingGroup.kleinFour (Fin 4)
  let A0 := alternatingBlockPreimage 4 4 f
  let r0 := alternatingBlockPreimageProjection 4 4 f
  have hr0 : Function.Surjective r0 :=
    alternatingBlockPreimageProjection_surjective 4 4 f hf
  have hmap : (commutator A0).map r0 = V.prod V := by
    dsimp [A, V]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr0]
    simpa [← commutator_def,
      alternatingGroup.kleinFour_eq_commutator (Nat.card_fin 4)] using
      (Subgroup.commutator_prod_prod
        (⊤ : Subgroup A) (⊤ : Subgroup A)
        (⊤ : Subgroup A) (⊤ : Subgroup A))
  obtain ⟨l, hlcomm, hly⟩ : ∃ l : A0, l ∈ commutator A0 ∧ r0 l = y := by
    have hy' : y ∈ (commutator A0).map r0 := by
      rw [hmap]
      exact hy
    obtain ⟨l, hlcomm, hly⟩ := Subgroup.mem_map.mp hy'
    exact ⟨l, hlcomm, hly⟩
  have hmapj : (commutator E).map jE = commutator A0 := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hjE,
      commutator_def]
  have hlmap : l ∈ (commutator E).map jE := by
    rw [hmapj]
    exact hlcomm
  obtain ⟨e, hecomm, hel⟩ := Subgroup.mem_map.mp hlmap
  refine ⟨e, ?_, hecomm⟩
  apply evenTwoBlockWreathFinHom_injective 4
  calc
    evenTwoBlockWreathFinHom 4 (rW e) = f (W.subtype (E.subtype e)) :=
      hfac (E.subtype e)
    _ = f (jE e) := by
      rw [hjEval e]
      rfl
    _ = f l := by rw [hel]
    _ = alternatingProdBlockHom 4 4 (r0 l) := by
      exact (alternatingBlockPreimageProjection_fac 4 4 f l).symm
    _ = alternatingProdBlockHom 4 4 y := by rw [hly]
    _ = evenTwoBlockWreathFinHom 4 (evenTwoBlockWreathBaseHom 4 y) :=
      (evenTwoBlockWreathBaseHom_ambient 4 y).symm

public theorem test_tensor_flip_conj_of_eq
    (m d : Nat) (hm : 2 ≤ m) (hdm : 2 * m = d)
    (hmEven : Even m) (hd : 2 ≤ d) (heven : Even d)
    (x : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) :
    let c0 : alternatingGroup (Fin ((2 * m) + (2 * m))) :=
      ⟨twoWreathTensorFlip m,
        twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩
    let c : alternatingGroup (Fin (d + d)) := by
      have hsize : (2 * m) + (2 * m) = d + d := by omega
      exact hsize ▸ c0
    ∃ y : alternatingGroup (Fin d) × alternatingGroup (Fin d),
      c * evenTwoBlockWreathFinHom d
          (twoWreathKleinFourHom d hd heven x) * c⁻¹ =
        evenTwoBlockWreathFinHom d
          (evenTwoBlockWreathBaseHom d y) := by
  dsimp
  cases hdm
  simpa using (twoWreathTensorFlip_conj_evenKleinFour m hm hmEven x.1 x.2)

public theorem exists_tensor_flip_conj_base_mem_a8
    (p q : Equiv.Perm (Fin 2)) :
    ∃ y : alternatingGroup (Fin 4) × alternatingGroup (Fin 4),
      (⟨twoWreathTensorFlip 2,
          twoWreathTensorFlip_mem_alternatingGroup 2 (by exact ⟨1, rfl⟩)⟩ :
          alternatingGroup (Fin (4 + 4))) *
            evenTwoBlockWreathFinHom 4
              (twoWreathKleinFourHom 4 (by omega)
                (by exact ⟨2, rfl⟩) (p, q)) *
          (⟨twoWreathTensorFlip 2,
            twoWreathTensorFlip_mem_alternatingGroup 2 (by exact ⟨1, rfl⟩)⟩ :
            alternatingGroup (Fin (4 + 4)))⁻¹ =
        evenTwoBlockWreathFinHom 4 (evenTwoBlockWreathBaseHom 4 y) ∧
      y ∈ (alternatingGroup.kleinFour (Fin 4)).prod
        (alternatingGroup.kleinFour (Fin 4)) := by
  let hm2 : 2 ≤ 2 := by omega
  let heven2 : Even 2 := by exact ⟨1, rfl⟩
  let hd4 : 2 ≤ 4 := by omega
  let heven4 : Even 4 := by exact ⟨2, rfl⟩
  let c : alternatingGroup (Fin (4 + 4)) :=
    ⟨twoWreathTensorFlip 2,
      twoWreathTensorFlip_mem_alternatingGroup 2 heven2⟩
  let kHom := twoWreathKleinFourHom 4 hd4 heven4
  let kW := kHom (p, q)
  let kA := evenTwoBlockWreathFinHom 4 kW
  obtain ⟨y, hconj⟩ :=
    twoWreathTensorFlip_conj_evenKleinFour 2 hm2 heven2 p q
  let bA := evenTwoBlockWreathFinHom 4 (evenTwoBlockWreathBaseHom 4 y)
  have hconj' : c * kA * c⁻¹ = bA := by
    exact hconj
  refine ⟨y, ?_, ?_⟩
  · simpa only [c, kA, kW, kHom, bA] using hconj'
  have hp : p ^ 2 = 1 := by fin_cases p <;> decide
  have hq : q ^ 2 = 1 := by fin_cases q <;> decide
  have hx : (p, q) ^ 2 = (1, 1) := Prod.ext hp hq
  have hkW : kW ^ 2 = 1 := by
    change (kHom (p, q)) ^ 2 = 1
    calc
      (kHom (p, q)) ^ 2 = kHom ((p, q) ^ 2) := (map_pow kHom (p, q) 2).symm
      _ = kHom (1, 1) := congrArg kHom hx
      _ = 1 := map_one kHom
  have hkA : kA ^ 2 = 1 := by
    change (evenTwoBlockWreathFinHom 4 kW) ^ 2 = 1
    calc
      (evenTwoBlockWreathFinHom 4 kW) ^ 2 =
          evenTwoBlockWreathFinHom 4 (kW ^ 2) :=
        (map_pow (evenTwoBlockWreathFinHom 4) kW 2).symm
      _ = evenTwoBlockWreathFinHom 4 1 :=
        congrArg (evenTwoBlockWreathFinHom 4) hkW
      _ = 1 := map_one (evenTwoBlockWreathFinHom 4)
  have hbA : bA ^ 2 = 1 := by
    rw [← hconj']
    calc
      (c * kA * c⁻¹) ^ 2 = c * kA ^ 2 * c⁻¹ := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hkA]; simp
  have hbW : (evenTwoBlockWreathBaseHom 4 y) ^ 2 = 1 := by
    apply evenTwoBlockWreathFinHom_injective 4
    simpa only [bA, map_pow, map_one] using hbA
  have hbaseInj : Function.Injective (evenTwoBlockWreathBaseHom 4) := by
    intro a b hab
    apply evenBlockAlternatingHom_injective 4 4
    apply evenBlockToEvenTwoWreathHom_injective 4
    exact hab
  have hy2 : y ^ 2 = 1 := by
    apply hbaseInj
    simpa only [map_pow, map_one] using hbW
  change
    y.1 ∈ (↑(alternatingGroup.kleinFour (Fin 4)) :
      Set (alternatingGroup (Fin 4))) ∧
    y.2 ∈ (↑(alternatingGroup.kleinFour (Fin 4)) :
      Set (alternatingGroup (Fin 4)))
  constructor
  · rw [alternatingGroup.coe_kleinFour_of_card_eq_four (Nat.card_fin 4)]
    have hsA : y.1 ^ 2 = 1 := congrArg
      (fun z : alternatingGroup (Fin 4) × alternatingGroup (Fin 4) => z.1) hy2
    have hs : ((y.1 : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) ^ 2 = 1 :=
      congrArg Subtype.val hsA
    have hc := alternatingGroup.mem_kleinFour_of_order_two_pow
      (Nat.card_fin 4) y.1.2 (n := 1)
      (by simpa using orderOf_dvd_of_pow_eq_one hs)
    simpa using hc
  · rw [alternatingGroup.coe_kleinFour_of_card_eq_four (Nat.card_fin 4)]
    have hsA : y.2 ^ 2 = 1 := congrArg
      (fun z : alternatingGroup (Fin 4) × alternatingGroup (Fin 4) => z.2) hy2
    have hs : ((y.2 : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) ^ 2 = 1 :=
      congrArg Subtype.val hsA
    have hc := alternatingGroup.mem_kleinFour_of_order_two_pow
      (Nat.card_fin 4) y.2.2 (n := 1)
      (by simpa using orderOf_dvd_of_pow_eq_one hs)
    simpa using hc

public theorem test_exists_wreath_complement_lift
    {H : Type} [Group H] [Finite H]
    (q m : Nat) (hm4 : 4 ≤ m) (hdm : 2 * m = q + 5)
    (hmEven : Even m)
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    let hd : 2 ≤ q + 5 := by omega
    let heven : Even (q + 5) := by
      obtain ⟨k, hk⟩ := hmEven
      exact ⟨2 * k, by omega⟩
    let W := evenTwoBlockWreathPreimage (q + 5) f
    let r := evenTwoBlockWreathPreimageProjection (q + 5) hd f
    let A := evenTwoBlockWreathBase (q + 5)
    let B := twoWreathKleinFour (q + 5) hd heven
    let E : Subgroup W := A.comap r
    let L : Subgroup E := commutator E
    let c0 : alternatingGroup (Fin ((2 * m) + (2 * m))) :=
      ⟨twoWreathTensorFlip m,
        twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩
    let c : alternatingGroup (Fin ((q + 5) + (q + 5))) := by
      have hsize : (2 * m) + (2 * m) = (q + 5) + (q + 5) := by omega
      exact hsize ▸ c0
    let conjL : L →* H :=
      (MulAut.conj (Classical.choose (hf c))⁻¹).toMonoidHom.comp
        (W.subtype.comp (E.subtype.comp L.subtype))
    let U : Subgroup W :=
      B.comap r ⊓ (MonoidHom.range conjL).comap W.subtype
    ∃ t : H, f t = c ∧
      ∀ b : B, ∃ u : U, r u = b := by
  dsimp
  let hd : 2 ≤ q + 5 := by omega
  let heven : Even (q + 5) := by
    obtain ⟨k, hk⟩ := hmEven
    exact ⟨2 * k, by omega⟩
  let W := evenTwoBlockWreathPreimage (q + 5) f
  let r := evenTwoBlockWreathPreimageProjection (q + 5) hd f
  let A := evenTwoBlockWreathBase (q + 5)
  let B := twoWreathKleinFour (q + 5) hd heven
  let E : Subgroup W := A.comap r
  let L : Subgroup E := commutator E
  let c0 : alternatingGroup (Fin ((2 * m) + (2 * m))) :=
    ⟨twoWreathTensorFlip m,
      twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩
  let c : alternatingGroup (Fin ((q + 5) + (q + 5))) := by
    have hsize : (2 * m) + (2 * m) = (q + 5) + (q + 5) := by omega
    exact hsize ▸ c0
  let t : H := Classical.choose (hf c)
  have ht : f t = c := Classical.choose_spec (hf c)
  obtain ⟨jE, hjE, hjEval⟩ := test_wreath_jE (q + 5) hd heven f hf
  have hEbase (x : E) :
      f (W.subtype (E.subtype x)) ∈
        (alternatingProdBlockHom (q + 5) (q + 5)).range := by
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, ?_⟩
    calc
      alternatingProdBlockHom (q + 5) (q + 5) y =
          evenTwoBlockWreathFinHom (q + 5)
            (evenTwoBlockWreathBaseHom (q + 5) y) :=
        (evenTwoBlockWreathBaseHom_ambient (q + 5) y).symm
      _ = evenTwoBlockWreathFinHom (q + 5) (r x) :=
        congrArg (evenTwoBlockWreathFinHom (q + 5)) hy
      _ = f (W.subtype (E.subtype x)) :=
        evenTwoBlockWreathPreimageProjection_fac (q + 5) hd f (E.subtype x)
  let U : Subgroup W :=
    B.comap r ⊓ (MonoidHom.range
      ((MulAut.conj t⁻¹).toMonoidHom.comp
        (W.subtype.comp (E.subtype.comp L.subtype)))).comap W.subtype
  have hfac (x : W) :
      evenTwoBlockWreathFinHom (q + 5) (r x) = f x :=
    evenTwoBlockWreathPreimageProjection_fac (q + 5) hd f x
  have hexists (y : alternatingGroup (Fin (q + 5)) ×
      alternatingGroup (Fin (q + 5))) :
      ∃ e : E, r e = evenTwoBlockWreathBaseHom (q + 5) y ∧
        e ∈ commutator E :=
    test_exists_wreath_base_lift q m hm4 hdm f hf hker y W r E jE hjE
      hfac hEbase hjEval
  refine ⟨t, ht, ?_⟩
  intro b
  obtain ⟨x, hx⟩ := b.2
  obtain ⟨y, hy⟩ := test_tensor_flip_conj_of_eq m (q + 5) (by omega)
    hdm hmEven hd heven x
  obtain ⟨e, her, heL⟩ := hexists y
  let uH : H := t⁻¹ * (W.subtype (E.subtype e)) * t
  have hconj : c⁻¹ *
      evenTwoBlockWreathFinHom (q + 5) (r e) * c =
      evenTwoBlockWreathFinHom (q + 5)
        (twoWreathKleinFourHom (q + 5) hd heven x) := by
    have hbase : evenTwoBlockWreathFinHom (q + 5) (r e) =
        c * evenTwoBlockWreathFinHom (q + 5)
          (twoWreathKleinFourHom (q + 5) hd heven x) * c⁻¹ := by
      calc
        evenTwoBlockWreathFinHom (q + 5) (r e) =
            evenTwoBlockWreathFinHom (q + 5)
              (evenTwoBlockWreathBaseHom (q + 5) y) :=
          congrArg (evenTwoBlockWreathFinHom (q + 5)) her
        _ = c * evenTwoBlockWreathFinHom (q + 5)
            (twoWreathKleinFourHom (q + 5) hd heven x) * c⁻¹ := hy.symm
    calc
      c⁻¹ * evenTwoBlockWreathFinHom (q + 5) (r e) * c =
          c⁻¹ * (c * evenTwoBlockWreathFinHom (q + 5)
            (twoWreathKleinFourHom (q + 5) hd heven x) * c⁻¹) * c := by
        rw [hbase]
      _ = evenTwoBlockWreathFinHom (q + 5)
          (twoWreathKleinFourHom (q + 5) hd heven x) := by group
  have huH : f uH = evenTwoBlockWreathFinHom (q + 5)
      (twoWreathKleinFourHom (q + 5) hd heven x) := by
    change f (t⁻¹ * (W.subtype (E.subtype e)) * t) = _
    rw [map_mul, map_mul, map_inv, ht]
    have hfe := hfac (E.subtype e)
    change evenTwoBlockWreathFinHom (q + 5) (r (E.subtype e)) =
      f (W.subtype (E.subtype e)) at hfe
    rw [← hfe]
    exact hconj
  let u : W :=
    ⟨uH, ⟨twoWreathKleinFourHom (q + 5) hd heven x, huH.symm⟩⟩
  have hur : r u = b := by
    apply evenTwoBlockWreathFinHom_injective (q + 5)
    calc
      evenTwoBlockWreathFinHom (q + 5) (r u) = f u := hfac u
      _ = evenTwoBlockWreathFinHom (q + 5)
          (twoWreathKleinFourHom (q + 5) hd heven x) := huH
      _ = evenTwoBlockWreathFinHom (q + 5)
          (b : evenTwoBlockWreathGroup (q + 5)) := by
        exact congrArg (evenTwoBlockWreathFinHom (q + 5)) hx
  refine ⟨⟨u, ?_⟩, hur⟩
  constructor
  · change r u ∈ B
    rw [hur]
    exact b.2
  · refine ⟨⟨e, heL⟩, ?_⟩
    simp [t, uH, u]

public theorem test_exists_wreath_complement_lift_a8
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f) :
    let hd : 2 ≤ 4 := by omega
    let heven : Even 4 := by exact ⟨2, rfl⟩
    let W := evenTwoBlockWreathPreimage 4 f
    let r := evenTwoBlockWreathPreimageProjection 4 hd f
    let A := evenTwoBlockWreathBase 4
    let B := twoWreathKleinFour 4 hd heven
    let E : Subgroup W := A.comap r
    let L : Subgroup E := commutator E
    let c : alternatingGroup (Fin 8) :=
      ⟨twoWreathTensorFlip 2,
        twoWreathTensorFlip_mem_alternatingGroup 2 (by exact ⟨1, rfl⟩)⟩
    let conjL : L →* H :=
      (MulAut.conj (Classical.choose (hf c))⁻¹).toMonoidHom.comp
        (W.subtype.comp (E.subtype.comp L.subtype))
    let U : Subgroup W :=
      B.comap r ⊓ (MonoidHom.range conjL).comap W.subtype
    ∃ t : H, f t = c ∧
      ∀ b : B, ∃ u : U, r u = b := by
  dsimp
  let hd : 2 ≤ 4 := by omega
  let heven : Even 4 := by exact ⟨2, rfl⟩
  let W := evenTwoBlockWreathPreimage 4 f
  let r := evenTwoBlockWreathPreimageProjection 4 hd f
  let A := evenTwoBlockWreathBase 4
  let B := twoWreathKleinFour 4 hd heven
  let E : Subgroup W := A.comap r
  let L : Subgroup E := commutator E
  let c : alternatingGroup (Fin 8) :=
    ⟨twoWreathTensorFlip 2,
      twoWreathTensorFlip_mem_alternatingGroup 2 (by exact ⟨1, rfl⟩)⟩
  let t : H := Classical.choose (hf c)
  have ht : f t = c := Classical.choose_spec (hf c)
  obtain ⟨jE, hjE, hjEval⟩ := test_wreath_jE 4 hd heven f hf
  let U : Subgroup W :=
    B.comap r ⊓ (MonoidHom.range
      ((MulAut.conj t⁻¹).toMonoidHom.comp
        (W.subtype.comp (E.subtype.comp L.subtype)))).comap W.subtype
  have hfac (x : W) :
      evenTwoBlockWreathFinHom 4 (r x) = f x :=
    evenTwoBlockWreathPreimageProjection_fac 4 hd f x
  refine ⟨t, ht, ?_⟩
  intro b
  obtain ⟨x, hx⟩ := b.2
  obtain ⟨y, hy, hyV⟩ :=
    exists_tensor_flip_conj_base_mem_a8 x.1 x.2
  obtain ⟨e, her, heL⟩ :=
    test_exists_wreath_base_lift_a8 f hf y hyV W r E jE hjE hfac hjEval
  let uH : H := t⁻¹ * (W.subtype (E.subtype e)) * t
  have hconj : c⁻¹ * evenTwoBlockWreathFinHom 4 (r e) * c =
      evenTwoBlockWreathFinHom 4
        (twoWreathKleinFourHom 4 hd heven x) := by
    have hbase : evenTwoBlockWreathFinHom 4 (r e) =
        c * evenTwoBlockWreathFinHom 4
          (twoWreathKleinFourHom 4 hd heven x) * c⁻¹ := by
      calc
        evenTwoBlockWreathFinHom 4 (r e) =
            evenTwoBlockWreathFinHom 4
              (evenTwoBlockWreathBaseHom 4 y) :=
          congrArg (evenTwoBlockWreathFinHom 4) her
        _ = c * evenTwoBlockWreathFinHom 4
            (twoWreathKleinFourHom 4 hd heven x) * c⁻¹ := by
          exact hy.symm
    calc
      c⁻¹ * evenTwoBlockWreathFinHom 4 (r e) * c =
          c⁻¹ * (c * evenTwoBlockWreathFinHom 4
            (twoWreathKleinFourHom 4 hd heven x) * c⁻¹) * c := by
        rw [hbase]
      _ = evenTwoBlockWreathFinHom 4
          (twoWreathKleinFourHom 4 hd heven x) := by group
  have huH : f uH = evenTwoBlockWreathFinHom 4
      (twoWreathKleinFourHom 4 hd heven x) := by
    change f (t⁻¹ * (W.subtype (E.subtype e)) * t) = _
    rw [map_mul, map_mul, map_inv, ht]
    have hfe := hfac (E.subtype e)
    change evenTwoBlockWreathFinHom 4 (r (E.subtype e)) =
      f (W.subtype (E.subtype e)) at hfe
    rw [← hfe]
    exact hconj
  let u : W :=
    ⟨uH, ⟨twoWreathKleinFourHom 4 hd heven x, huH.symm⟩⟩
  have hur : r u = b := by
    apply evenTwoBlockWreathFinHom_injective 4
    calc
      evenTwoBlockWreathFinHom 4 (r u) = f u := hfac u
      _ = evenTwoBlockWreathFinHom 4
          (twoWreathKleinFourHom 4 hd heven x) := huH
      _ = evenTwoBlockWreathFinHom 4 (b : evenTwoBlockWreathGroup 4) := by
        exact congrArg (evenTwoBlockWreathFinHom 4) hx
  refine ⟨⟨u, ?_⟩, hur⟩
  constructor
  · change r u ∈ B
    rw [hur]
    exact b.2
  · refine ⟨⟨e, heL⟩, ?_⟩
    simp [t, uH, u]

public theorem a8FusedRange_normal_in_evenTwoBlockWreathPreimage
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (jE : (evenTwoBlockWreathBase 4).comap
        (evenTwoBlockWreathPreimageProjection 4 (by omega) f) →*
      alternatingBlockPreimage 4 4 f)
    (hjE : Function.Surjective jE)
    (hjEval : ∀ x, (jE x : H) =
      ((evenTwoBlockWreathPreimage 4 f).subtype
        (((evenTwoBlockWreathBase 4).comap
          (evenTwoBlockWreathPreimageProjection 4 (by omega) f)).subtype x) : H)) :
    (((a8FusedProductToBlockPreimage f hf hker hkerTwo).range.comap jE).map
      ((evenTwoBlockWreathBase 4).comap
        (evenTwoBlockWreathPreimageProjection 4 (by omega) f)).subtype).Normal := by
  let hd : 2 ≤ 4 := by omega
  let W := evenTwoBlockWreathPreimage 4 f
  let r := evenTwoBlockWreathPreimageProjection 4 hd f
  let A := evenTwoBlockWreathBase 4
  let E : Subgroup W := A.comap r
  let A0 := alternatingBlockPreimage 4 4 f
  let r0 := alternatingBlockPreimageProjection 4 4 f
  let g := a8FusedProductToBlockPreimage f hf hker hkerTwo
  let M : Subgroup E := g.range.comap jE
  change (M.map E.subtype).Normal
  have hEnormal : E.Normal := by
    dsimp [E]
    exact (evenTwoBlockWreathBase_normal 4).comap r
  let : E.Normal := hEnormal
  have hAnormal : A.Normal := evenTwoBlockWreathBase_normal 4
  let : A.Normal := hAnormal
  let s : E →* A :=
    (r.comp E.subtype).codRestrict A (fun x => x.2)
  have hfac (x : W) : evenTwoBlockWreathFinHom 4 (r x) = f x :=
    evenTwoBlockWreathPreimageProjection_fac 4 hd f x
  have hjProjection (x : E) :
      r (E.subtype x) = evenTwoBlockWreathBaseHom 4 (r0 (jE x)) := by
    apply evenTwoBlockWreathFinHom_injective 4
    calc
      evenTwoBlockWreathFinHom 4 (r (E.subtype x)) =
          f (W.subtype (E.subtype x)) := hfac (E.subtype x)
      _ = f (jE x) := congrArg f (hjEval x).symm
      _ = alternatingProdBlockHom 4 4 (r0 (jE x)) :=
        (alternatingBlockPreimageProjection_fac 4 4 f (jE x)).symm
      _ = evenTwoBlockWreathFinHom 4
          (evenTwoBlockWreathBaseHom 4 (r0 (jE x))) :=
        (evenTwoBlockWreathBaseHom_ambient 4 (r0 (jE x))).symm
  have hM : Function.Surjective (s.comp M.subtype) := by
    intro q
    obtain ⟨y, hy⟩ := q.2
    obtain ⟨z, hz⟩ :=
      a8FusedProductToBlockPreimage_projection_surjective
        f hf hker hkerTwo y
    obtain ⟨e, he⟩ := hjE (g z)
    have heM : e ∈ M := by
      change jE e ∈ g.range
      exact ⟨z, he.symm⟩
    let m : M := ⟨e, heM⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change r (E.subtype e) = (q : evenTwoBlockWreathGroup 4)
    rw [hjProjection, he]
    have hz' : r0 (g z) = y := hz
    rw [hz']
    exact hy
  have hsKerToF (x : E) (hx : x ∈ s.ker) :
      (W.subtype (E.subtype x) : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have hsx : s x = 1 := MonoidHom.mem_ker.mp hx
    have hrx : r (E.subtype x) = 1 := congrArg Subtype.val hsx
    calc
      f (W.subtype (E.subtype x)) =
          evenTwoBlockWreathFinHom 4 (r (E.subtype x)) :=
        (hfac (E.subtype x)).symm
      _ = 1 := by rw [hrx, map_one]
  have hsKerCenter : s.ker ≤ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker (hsKerToF x hx))
      (W.subtype (E.subtype y))
  have hsKerTwo : IsPGroup 2 s.ker := by
    let i : s.ker →* f.ker :=
      ((W.subtype.comp (E.subtype.comp s.ker.subtype)).codRestrict f.ker (by
        intro x
        exact hsKerToF x.1 x.2))
    apply hkerTwo.of_injective i
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : H)) hxy
  have hbaseInj : Function.Injective (evenTwoBlockWreathBaseHom 4) := by
    intro x y hxy
    apply alternatingProdBlockHom_injective 4 4
    rw [← evenTwoBlockWreathBaseHom_ambient,
      ← evenTwoBlockWreathBaseHom_ambient, hxy]
  have hprod : ∀ q : A, ∃ a b : A,
      orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = q := by
    intro q
    obtain ⟨z, hz⟩ := q.2
    obtain ⟨a, b, ha, hb, hab⟩ := a4_prod_exists_mul_order_three z
    let aA : A := ⟨evenTwoBlockWreathBaseHom 4 a, ⟨a, rfl⟩⟩
    let bA : A := ⟨evenTwoBlockWreathBaseHom 4 b, ⟨b, rfl⟩⟩
    refine ⟨aA, bA, ?_, ?_, ?_⟩
    · calc
        orderOf aA = orderOf (evenTwoBlockWreathBaseHom 4 a) :=
          (orderOf_submonoid aA).symm
        _ = orderOf a := orderOf_injective _ hbaseInj a
        _ = 3 := ha
    · calc
        orderOf bA = orderOf (evenTwoBlockWreathBaseHom 4 b) :=
          (orderOf_submonoid bA).symm
        _ = orderOf b := orderOf_injective _ hbaseInj b
        _ = 3 := hb
    · apply Subtype.ext
      change evenTwoBlockWreathBaseHom 4 a *
        evenTwoBlockWreathBaseHom 4 b = (q : evenTwoBlockWreathGroup 4)
      rw [← map_mul, hab]
      exact hz
  constructor
  rintro _ ⟨m, hmM, rfl⟩ __ch5_Theorem523Core_w
  let e : E ≃* E := MulAut.conjNormal __ch5_Theorem523Core_w
  let eA : A ≃* A := MulAut.conjNormal (r __ch5_Theorem523Core_w)
  have hse (x : E) : s (e x) = eA (s x) := by
    apply Subtype.ext
    change r (__ch5_Theorem523Core_w * E.subtype x * __ch5_Theorem523Core_w⁻¹) =
      r __ch5_Theorem523Core_w * r (E.subtype x) * (r __ch5_Theorem523Core_w)⁻¹
    simp
  have heKer : ∀ x : E, x ∈ s.ker → e x = x := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    change (W.subtype __ch5_Theorem523Core_w : H) * W.subtype (E.subtype x) *
      (W.subtype __ch5_Theorem523Core_w : H)⁻¹ = W.subtype (E.subtype x)
    have hxcenter := hker (hsKerToF x hx)
    have hcomm : (W.subtype __ch5_Theorem523Core_w : H) * W.subtype (E.subtype x) =
        W.subtype (E.subtype x) * (W.subtype __ch5_Theorem523Core_w : H) :=
      Subgroup.mem_center_iff.mp hxcenter (W.subtype __ch5_Theorem523Core_w)
    rw [hcomm]
    group
  have hMap : Function.Surjective
      (s.comp (M.map e.toMonoidHom).subtype) := by
    intro q
    obtain ⟨m, hm⟩ := hM (eA.symm q)
    let n : M.map e.toMonoidHom :=
      ⟨e m, ⟨m, m.2, rfl⟩⟩
    refine ⟨n, ?_⟩
    change s (e (m : E)) = q
    rw [hse]
    have hm' : s (m : E) = eA.symm q := hm
    rw [hm']
    exact eA.apply_symm_apply q
  have hMeq : M.map e.toMonoidHom = M :=
    subgroup_map_eq_self_of_surjective_of_fixed_two_kernel
      s hsKerCenter hsKerTwo hprod M hM e heKer hMap
  refine ⟨e m, ?_, ?_⟩
  · rw [← hMeq]
    exact ⟨m, hmM, rfl⟩
  · exact MulAut.conjNormal_apply __ch5_Theorem523Core_w m

public theorem natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage_a8
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin 8))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenTwoBlockWreathPreimage 4 f) :
    Nat.card f.ker ≤ 2 := by
  let hd : 2 ≤ 4 := by omega
  let heven : Even 4 := by exact ⟨2, rfl⟩
  let W := evenTwoBlockWreathPreimage 4 f
  let r := evenTwoBlockWreathPreimageProjection 4 hd f
  let A := evenTwoBlockWreathBase 4
  let B := twoWreathKleinFour 4 hd heven
  let E : Subgroup W := A.comap r
  let A0 := alternatingBlockPreimage 4 4 f
  let r0 := alternatingBlockPreimageProjection 4 4 f
  let g := a8FusedProductToBlockPreimage f hf hker hkerTwo
  let K : Subgroup W := f.ker.comap W.subtype
  obtain ⟨jE, hjE, hjEval⟩ := test_wreath_jE 4 hd heven f hf
  let M : Subgroup E := g.range.comap jE
  let L : Subgroup W := M.map E.subtype
  let C : Subgroup W := K ⊓ L
  have hEnormal : E.Normal := by
    dsimp [E]
    exact (evenTwoBlockWreathBase_normal 4).comap r
  have hLnormal : L.Normal := by
    simpa [L, M, g, E, A, r, W, hd] using
      a8FusedRange_normal_in_evenTwoBlockWreathPreimage
        f hf hker hkerTwo jE hjE hjEval
  have hfac (x : W) : evenTwoBlockWreathFinHom 4 (r x) = f x :=
    evenTwoBlockWreathPreimageProjection_fac 4 hd f x
  have hjProjection (x : E) :
      r (E.subtype x) = evenTwoBlockWreathBaseHom 4 (r0 (jE x)) := by
    apply evenTwoBlockWreathFinHom_injective 4
    calc
      evenTwoBlockWreathFinHom 4 (r (E.subtype x)) =
          f (W.subtype (E.subtype x)) := hfac (E.subtype x)
      _ = f (jE x) := congrArg f (hjEval x).symm
      _ = alternatingProdBlockHom 4 4 (r0 (jE x)) :=
        (alternatingBlockPreimageProjection_fac 4 4 f (jE x)).symm
      _ = evenTwoBlockWreathFinHom 4
          (evenTwoBlockWreathBaseHom 4 (r0 (jE x))) :=
        (evenTwoBlockWreathBaseHom_ambient 4 (r0 (jE x))).symm
  have hr0ker : r0.ker ≤ Subgroup.center A0 :=
    alternatingBlockPreimageProjection_ker_le_center 4 4 f hker
  have hcommRange : commutator A0 ≤ g.range :=
    commutator_le_range_of_surjective_comp_of_ker_le_center r0 g
      (a8FusedProductToBlockPreimage_projection_surjective
        f hf hker hkerTwo) hr0ker
  have hmap : (commutator E).map jE = commutator A0 := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hjE, commutator_def]
  have hcommM : commutator E ≤ M := by
    intro x hx
    change jE x ∈ g.range
    apply hcommRange
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  let c : alternatingGroup (Fin 8) :=
    ⟨twoWreathTensorFlip 2,
      twoWreathTensorFlip_mem_alternatingGroup 2 (by exact ⟨1, rfl⟩)⟩
  let t : H := Classical.choose (hf c)
  obtain ⟨_, _, hUraw⟩ := test_exists_wreath_complement_lift_a8 f hf
  let conjComm : (commutator E) →* H :=
    (MulAut.conj t⁻¹).toMonoidHom.comp
      (W.subtype.comp (E.subtype.comp (commutator E).subtype))
  let U : Subgroup W := B.comap r ⊓
    (MonoidHom.range conjComm).comap W.subtype
  have hU (b : B) : ∃ u : U, r u = b := by
    simpa [U, conjComm, t, c, E, W, r, B, A, hd, heven] using hUraw b
  have hUle : U ≤ B.comap r := fun x hx => hx.1
  have hLleE : L ≤ E := by
    rintro x ⟨e, he, rfl⟩
    exact e.2
  have hLleA : L ≤ A.comap r := by
    intro x hx
    exact hLleE hx
  have hKU : K ⊓ U ≤ C := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨l, hxl⟩ := hx.2.2
    have hxlH : t⁻¹ * (W.subtype (E.subtype (l : E))) * t =
        (W.subtype x : H) := by
      simpa [conjComm] using hxl
    have hxkerH : (W.subtype x : H) ∈ f.ker := hx.1
    have hxcenter : (W.subtype x : H) ∈ Subgroup.center H :=
      hker hxkerH
    have hcent : t * (W.subtype x : H) =
        (W.subtype x : H) * t :=
      Subgroup.mem_center_iff.mp hxcenter t
    have hlx : W.subtype (E.subtype (l : E)) = W.subtype x := by
      calc
        W.subtype (E.subtype (l : E)) =
            t * (t⁻¹ * W.subtype (E.subtype (l : E)) * t) * t⁻¹ := by
              group
        _ = t * (W.subtype x : H) * t⁻¹ := by rw [hxlH]
        _ = W.subtype x := by rw [hcent]; group
    have hlM : (l : E) ∈ M := hcommM l.2
    have hlL : (E.subtype (l : E) : W) ∈ L := ⟨l, hlM, rfl⟩
    have hlex : (E.subtype (l : E) : W) = x := by
      apply Subtype.ext
      exact hlx
    rwa [← hlex]
  have hKL : K ⊓ L = C := rfl
  have hdecomp : ∀ x : W, ∃ k : f.ker.comap W.subtype,
      ∃ d0 : ↥(U ⊔ L), (k : W) * (d0 : W) = x := by
    intro x
    obtain ⟨xb, yb, hxy⟩ :=
      exists_twoWreathKleinFour_mul_base 4 hd heven (r x)
    let xb' : B := ⟨twoWreathKleinFourHom 4 hd heven xb, ⟨xb, rfl⟩⟩
    obtain ⟨u, hu⟩ := hU xb'
    have hu' : r (u : W) = twoWreathKleinFourHom 4 hd heven xb := by
      simpa [xb'] using hu
    obtain ⟨z, hz⟩ :=
      a8FusedProductToBlockPreimage_projection_surjective
        f hf hker hkerTwo yb
    obtain ⟨e, he⟩ := hjE (g z)
    have heM : e ∈ M := by
      change jE e ∈ g.range
      exact ⟨z, he.symm⟩
    let m : M := ⟨e, heM⟩
    let v : W := E.subtype m
    have hver : r v = evenTwoBlockWreathBaseHom 4 yb := by
      change r (E.subtype e) = _
      rw [hjProjection, he]
      have hz' : r0 (g z) = yb := hz
      rw [hz']
    have huv : r ((u : W) * v) = r x := by
      rw [map_mul, hu', hver, hxy]
    let k : f.ker.comap W.subtype :=
      ⟨(x : W) * ((u : W) * v)⁻¹, by
        change f (W.subtype ((x : W) * ((u : W) * v)⁻¹)) = 1
        rw [map_mul W.subtype, map_inv W.subtype, map_mul f, map_inv f]
        have hfacx : f (W.subtype x) = evenTwoBlockWreathFinHom 4 (r x) :=
          (hfac x).symm
        have hfacuv : f (W.subtype ((u : W) * v)) =
            evenTwoBlockWreathFinHom 4 (r ((u : W) * v)) :=
          (hfac ((u : W) * v)).symm
        rw [hfacx, hfacuv, huv]
        group⟩
    have hvL : v ∈ L := ⟨m, m.2, rfl⟩
    let d0 : ↥(U ⊔ L) :=
      ⟨(u : W) * v, (U ⊔ L).mul_mem
        (Subgroup.mem_sup_left u.2) (Subgroup.mem_sup_right hvL)⟩
    refine ⟨k, d0, ?_⟩
    change ((x : W) * ((u : W) * v)⁻¹) * ((u : W) * v) = x
    group
  have hKle : K ≤ r.ker := by
    intro x hx
    change W.subtype x ∈ f.ker at hx
    rw [MonoidHom.mem_ker]
    apply evenTwoBlockWreathFinHom_injective 4
    calc
      evenTwoBlockWreathFinHom 4 (r x) = f x := hfac x
      _ = 1 := MonoidHom.mem_ker.mp hx
      _ = evenTwoBlockWreathFinHom 4 1 := by simp
  have hkerK : r.ker ≤ K := by
    intro x hx
    change W.subtype x ∈ f.ker
    rw [MonoidHom.mem_ker]
    apply MonoidHom.mem_ker.mpr
    calc
      f x = evenTwoBlockWreathFinHom 4 (r x) := (hfac x).symm
      _ = evenTwoBlockWreathFinHom 4 1 := congrArg
        (evenTwoBlockWreathFinHom 4) (MonoidHom.mem_ker.mp hx)
      _ = 1 := by simp
  have hinf : K ⊓ (U ⊔ L) = C :=
    kernel_inf_sup_of_map_of_normal r K U L C B A hLnormal hKle hkerK
      hUle hLleA (twoWreathKleinFour_inf_base_eq_bot 4 hd heven) hKU hKL
  have hKeq : f.ker.comap W.subtype = C :=
    kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
      (p := 2) f hker hkerTwo P W hP (U ⊔ L) C hdecomp hinf
  let C0 : Subgroup A0 := r0.ker ⊓ g.range
  let iCE : C →* E :=
    C.subtype.codRestrict E (fun x => hLleE x.2.2)
  have hiCEM (x : C) : iCE x ∈ M := by
    obtain ⟨e, heM, heq⟩ := x.2.2
    have hie : iCE x = e := by
      apply Subtype.ext
      exact heq.symm
    exact hie.symm ▸ heM
  let jC : C →* A0 := jE.comp iCE
  have hjCmem (x : C) : jC x ∈ C0 := by
    constructor
    · change r0 (jC x) = 1
      apply alternatingProdBlockHom_injective 4 4
      calc
        alternatingProdBlockHom 4 4 (r0 (jC x)) = f (jC x) :=
          alternatingBlockPreimageProjection_fac 4 4 f (jC x)
        _ = f (W.subtype (E.subtype (iCE x))) :=
          congrArg f (hjEval (iCE x))
        _ = 1 := by
          apply MonoidHom.mem_ker.mp
          exact x.2.1
        _ = alternatingProdBlockHom 4 4 1 := by simp
    · exact hiCEM x
  let jC0 : C →* C0 := jC.codRestrict C0 hjCmem
  have hjEinj : Function.Injective jE := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    calc
      W.subtype (E.subtype x) = (jE x : H) := (hjEval x).symm
      _ = (jE y : H) := congrArg Subtype.val hxy
      _ = W.subtype (E.subtype y) := hjEval y
  have hjC0inj : Function.Injective jC0 := by
    intro x y hxy
    apply Subtype.ext
    have hxyA0 : jC x = jC y := congrArg Subtype.val hxy
    have hxyE : iCE x = iCE y := hjEinj hxyA0
    exact congrArg (fun z : E => (z : W)) hxyE
  have hC0 : Nat.card C0 ≤ 2 := by
    exact natCard_a8FusedKernelRange_le_two f hf hker hkerTwo
  let eK : f.ker ≃* K :=
    { toFun := fun z => ⟨⟨z, by
          change f z ∈ (evenTwoBlockWreathFinHom 4).range
          rw [MonoidHom.mem_ker.mp z.2]
          exact Subgroup.one_mem _⟩, z.2⟩
      invFun := fun z => ⟨((z : K) : H), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  calc
    Nat.card f.ker = Nat.card K := Nat.card_congr eK.toEquiv
    _ = Nat.card C := by
      change Nat.card (f.ker.comap W.subtype) = Nat.card C
      rw [hKeq]
    _ ≤ Nat.card C0 := Nat.card_le_card_of_injective jC0 hjC0inj
    _ ≤ 2 := hC0

public theorem natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q m : Nat) (hm4 : 4 ≤ m) (hdm : 2 * m = q + 5)
    (hmEven : Even m)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenTwoBlockWreathPreimage (q + 5) f) :
    Nat.card f.ker ≤ 2 := by
  let hd : 2 ≤ q + 5 := by omega
  let heven : Even (q + 5) := by
    obtain ⟨k, hk⟩ := hmEven
    exact ⟨2 * k, by omega⟩
  let W := evenTwoBlockWreathPreimage (q + 5) f
  let r := evenTwoBlockWreathPreimageProjection (q + 5) hd f
  let A := evenTwoBlockWreathBase (q + 5)
  let B := twoWreathKleinFour (q + 5) hd heven
  let E : Subgroup W := A.comap r
  let L : Subgroup W := ⁅E, E⁆
  let K : Subgroup W := f.ker.comap W.subtype
  let C : Subgroup W := K ⊓ L
  have hEnormal : E.Normal := by
    dsimp [E]
    exact (evenTwoBlockWreathBase_normal (q + 5)).comap r
  have hLnormal : L.Normal := by
    dsimp [L]
    infer_instance
  obtain ⟨jE, hjE, hjEval⟩ := test_wreath_jE (q + 5) hd heven f hf
  let c0 : alternatingGroup (Fin ((2 * m) + (2 * m))) :=
    ⟨twoWreathTensorFlip m,
      twoWreathTensorFlip_mem_alternatingGroup m hmEven⟩
  let c : alternatingGroup (Fin ((q + 5) + (q + 5))) := by
    have hsize : (2 * m) + (2 * m) = (q + 5) + (q + 5) := by omega
    exact hsize ▸ c0
  let t : H := Classical.choose (hf c)
  have ht : f t = c := Classical.choose_spec (hf c)
  obtain ⟨_, _, hUraw⟩ :=
    test_exists_wreath_complement_lift q m hm4 hdm hmEven f hf hker
  let conjL : (commutator E) →* H :=
    (MulAut.conj t⁻¹).toMonoidHom.comp
      (W.subtype.comp (E.subtype.comp (commutator E).subtype))
  let U : Subgroup W := B.comap r ⊓
    (MonoidHom.range conjL).comap W.subtype
  have hU (b : B) : ∃ u : U, r u = b := by
    simpa [U, conjL, L, E, W, r, B] using hUraw b
  have hfac (x : W) :
      evenTwoBlockWreathFinHom (q + 5) (r x) = f x :=
    evenTwoBlockWreathPreimageProjection_fac (q + 5) hd f x
  have hUle : U ≤ B.comap r := fun x hx => hx.1
  have hLleE : L ≤ E := by
    exact (Subgroup.commutator_le_inf E E).trans inf_le_left
  have hLleA : L ≤ A.comap r := by
    intro x hx
    exact hLleE hx
  have hKU : K ⊓ U ≤ C := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨l, hxl⟩ := hx.2.2
    have hxlH : t⁻¹ * (W.subtype (E.subtype (l : E))) * t =
        (W.subtype x : H) := by
      simpa [conjL] using hxl
    have hxkerH : (W.subtype x : H) ∈ f.ker := hx.1
    have hxcenter : (W.subtype x : H) ∈ Subgroup.center H :=
      hker hxkerH
    have hcent : t * (W.subtype x : H) =
        (W.subtype x : H) * t :=
      Subgroup.mem_center_iff.mp hxcenter t
    have hlx : W.subtype (E.subtype (l : E)) = W.subtype x := by
      calc
        W.subtype (E.subtype (l : E)) =
            t * (t⁻¹ * W.subtype (E.subtype (l : E)) * t) * t⁻¹ := by
              group
        _ = t * (W.subtype x : H) * t⁻¹ := by rw [hxlH]
        _ = W.subtype x := by
          calc
            t * (W.subtype x : H) * t⁻¹ =
                (W.subtype x : H) * t * t⁻¹ := by
              rw [hcent]
            _ = W.subtype x := by group
    have hlL : (E.subtype (l : E) : W) ∈ L := by
      change (E.subtype (l : E) : W) ∈ ⁅E, E⁆
      rw [← Subgroup.map_subtype_commutator E]
      exact ⟨l, l.2, rfl⟩
    have hlex : (E.subtype (l : E) : W) = x := by
      apply Subtype.ext
      exact hlx
    rw [← hlex]
    exact hlL
  have hKL : K ⊓ L = C := rfl
  have hdecomp : ∀ x : W, ∃ k : f.ker.comap W.subtype,
      ∃ d0 : ↥(U ⊔ L), (k : W) * (d0 : W) = x := by
    intro x
    obtain ⟨xb, yb, hxy⟩ :=
      exists_twoWreathKleinFour_mul_base (q + 5) hd heven (r x)
    let xb' : B :=
      ⟨twoWreathKleinFourHom (q + 5) hd heven xb, ⟨xb, rfl⟩⟩
    obtain ⟨u, hu⟩ := hU xb'
    have hu' : r (u : W) =
        twoWreathKleinFourHom (q + 5) hd heven xb :=
      by simpa [xb'] using hu
    obtain ⟨e, her, hecomm⟩ :=
      test_exists_wreath_base_lift q m hm4 hdm f hf hker yb W r E jE hjE
        (fun z => hfac z) (by
          intro z
          obtain ⟨y, hy⟩ := z.2
          exact ⟨y, by
            calc
              alternatingProdBlockHom (q + 5) (q + 5) y =
                  evenTwoBlockWreathFinHom (q + 5)
                    (evenTwoBlockWreathBaseHom (q + 5) y) :=
                (evenTwoBlockWreathBaseHom_ambient (q + 5) y).symm
              _ = evenTwoBlockWreathFinHom (q + 5) (r z) :=
                congrArg (evenTwoBlockWreathFinHom (q + 5)) hy
              _ = f (W.subtype (E.subtype z)) :=
                hfac (E.subtype z)⟩)
        (fun z => hjEval z)
    let v : W := E.subtype e
    have hver : r v = evenTwoBlockWreathBaseHom (q + 5) yb := by
      exact her
    have huv : r ((u : W) * v) = r x := by
      rw [map_mul, hu', hver, hxy]
    let k : f.ker.comap W.subtype :=
      ⟨(x : W) * ((u : W) * v)⁻¹, by
        change f (W.subtype ((x : W) * ((u : W) * v)⁻¹)) = 1
        rw [map_mul W.subtype, map_inv W.subtype, map_mul f, map_inv f]
        have hfacx : f (W.subtype x) =
            evenTwoBlockWreathFinHom (q + 5) (r x) := (hfac x).symm
        have hfacuv : f (W.subtype ((u : W) * v)) =
            evenTwoBlockWreathFinHom (q + 5) (r ((u : W) * v)) :=
          (hfac ((u : W) * v)).symm
        rw [hfacx, hfacuv, huv]
        group⟩
    have hvL : v ∈ L := by
      change v ∈ ⁅E, E⁆
      rw [← Subgroup.map_subtype_commutator E]
      exact ⟨e, hecomm, rfl⟩
    let d0 : ↥(U ⊔ L) :=
      ⟨(u : W) * v, by
        exact (U ⊔ L).mul_mem (Subgroup.mem_sup_left u.2)
          (Subgroup.mem_sup_right hvL)⟩
    refine ⟨k, d0, ?_⟩
    change ((x : W) * ((u : W) * v)⁻¹) * ((u : W) * v) = x
    group
  have hKle : K ≤ r.ker := by
    intro x hx
    change W.subtype x ∈ f.ker at hx
    rw [MonoidHom.mem_ker]
    apply evenTwoBlockWreathFinHom_injective (q + 5)
    calc
      evenTwoBlockWreathFinHom (q + 5) (r x) = f x := hfac x
      _ = 1 := MonoidHom.mem_ker.mp hx
      _ = evenTwoBlockWreathFinHom (q + 5) 1 := by simp
  have hkerK : r.ker ≤ K := by
    intro x hx
    change W.subtype x ∈ f.ker
    rw [MonoidHom.mem_ker]
    apply MonoidHom.mem_ker.mpr
    calc
      f x = evenTwoBlockWreathFinHom (q + 5) (r x) := (hfac x).symm
      _ = evenTwoBlockWreathFinHom (q + 5) 1 := congrArg
        (evenTwoBlockWreathFinHom (q + 5)) (MonoidHom.mem_ker.mp hx)
      _ = 1 := by simp
  have hinf : K ⊓ (U ⊔ L) = C :=
    kernel_inf_sup_of_map_of_normal r K U L C B A hLnormal hKle hkerK
      hUle hLleA (twoWreathKleinFour_inf_base_eq_bot (q + 5) hd heven)
      hKU hKL
  have hKeq : f.ker.comap W.subtype = C := by
    exact kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
      (p := 2) f hker hkerTwo P W hP (U ⊔ L) C hdecomp hinf
  let A0 := alternatingBlockPreimage (q + 5) (q + 5) f
  let r0 := alternatingBlockPreimageProjection (q + 5) (q + 5) f
  let C0 : Subgroup A0 := r0.ker ⊓ commutator A0
  have hr0 : Function.Surjective r0 :=
    alternatingBlockPreimageProjection_surjective (q + 5) (q + 5) f hf
  have hr0ker : r0.ker ≤ Subgroup.center A0 :=
    alternatingBlockPreimageProjection_ker_le_center
      (q + 5) (q + 5) f hker
  have hglobal :=
    evenBlock_equalComponentDerivedKernel_eq_of_even_of_multiplier_le_two
      q hM heven f hf hker
  have hfusion := evenBlock_derivedKernelInBlock_eq_of_global_eq
    (q + 5) (q + 5) f hglobal
  have hmap : (commutator E).map jE = commutator A0 := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hjE, commutator_def]
  let injC : C → C0 := fun x => by
    let e : E := ⟨x.1, hLleE x.2.2⟩
    have heqE : e = ⟨x.1, hLleE x.2.2⟩ := rfl
    have hecomm : e ∈ commutator E := by
      have hxL : x.1 ∈ L := x.2.2
      change x.1 ∈ ⁅E, E⁆ at hxL
      rw [← Subgroup.map_subtype_commutator E] at hxL
      obtain ⟨e0, he0, heval⟩ := hxL
      have : e = e0 := by
        apply Subtype.ext
        exact heval.symm
      rw [this]
      exact he0
    have hjcomm : jE e ∈ commutator A0 := by
      rw [← hmap]
      exact ⟨e, hecomm, rfl⟩
    have hjker : jE e ∈ r0.ker := by
      rw [MonoidHom.mem_ker]
      apply alternatingProdBlockHom_injective (q + 5) (q + 5)
      calc
        alternatingProdBlockHom (q + 5) (q + 5) (r0 (jE e)) =
            f (jE e) :=
          alternatingBlockPreimageProjection_fac
            (q + 5) (q + 5) f (jE e)
        _ = f (W.subtype (E.subtype e)) := by
          exact congrArg f (hjEval e)
        _ = 1 := by
          apply MonoidHom.mem_ker.mp
          exact x.2.1
        _ = alternatingProdBlockHom (q + 5) (q + 5) 1 := by simp
    exact ⟨jE e, ⟨hjker, hjcomm⟩⟩
  have hinjC : Function.Injective injC := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : (jE
          (⟨x.1, hLleE x.2.2⟩ : E) : H) = (jE
          (⟨y.1, hLleE y.2.2⟩ : E) : H) :=
        congrArg (fun z : C0 => (z : H)) hxy
    have heqW :
        W.subtype (E.subtype (⟨x.1, hLleE x.2.2⟩ : E)) =
          W.subtype (E.subtype (⟨y.1, hLleE y.2.2⟩ : E)) := by
      calc
        W.subtype (E.subtype (⟨x.1, hLleE x.2.2⟩ : E)) =
            (jE (⟨x.1, hLleE x.2.2⟩ : E) : H) := (hjEval _).symm
        _ = (jE (⟨y.1, hLleE y.2.2⟩ : E) : H) := hxy'
        _ = W.subtype (E.subtype (⟨y.1, hLleE y.2.2⟩ : E)) := hjEval _
    have heq : (⟨x.1, hLleE x.2.2⟩ : E) =
        (⟨y.1, hLleE y.2.2⟩ : E) := by
      apply Subtype.ext
      apply Subtype.ext
      exact heqW
    exact congrArg (fun z : E => (z : W)) heq
  have hC0 : Nat.card C0 ≤ 2 := by
    let rL0 := prodLeftPreimageProjection r0
    let rL := prodLeftPreimageDerivedProjection r0
    obtain ⟨hlocal, _, _⟩ :=
      derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
        q hM rL0
        (prodLeftPreimageProjection_surjective r0 hr0)
        (prodLeftPreimageProjection_ker_le_center r0 hr0ker)
    have hC0eq : C0 =
        evenBlockLeftDerivedKernelInBlock (q + 5) (q + 5) f := by
      change r0.ker ⊓ commutator A0 = _
      rw [← evenBlockComponentDerivedProduct_eq_commutator q q f hf hker]
      exact evenBlockComponentDerivedProduct_ker_inf_eq_of_kernel_eq
        q q f hf hker hfusion
    have hiL : Function.Injective
        (evenBlockLeftDerivedEmbeddingToBlock (q + 5) (q + 5) f) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    calc
      Nat.card C0 = Nat.card
          (evenBlockLeftDerivedKernelInBlock (q + 5) (q + 5) f) := by
        rw [hC0eq]
      _ = Nat.card rL.ker := by
        exact Subgroup.card_map_of_injective hiL
      _ ≤ 2 := hlocal
  let eK : f.ker ≃* K :=
    { toFun := fun z => ⟨⟨z, by
          change f z ∈ (evenTwoBlockWreathFinHom (q + 5)).range
          rw [MonoidHom.mem_ker.mp z.2]
          exact Subgroup.one_mem _⟩, z.2⟩
      invFun := fun z => ⟨((z : K) : H), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  calc
    Nat.card f.ker = Nat.card K := Nat.card_congr eK.toEquiv
    _ = Nat.card C := by
      change Nat.card (f.ker.comap W.subtype) = Nat.card C
      rw [hKeq]
    _ ≤ Nat.card C0 := Nat.card_le_card_of_injective injC hinjC
    _ ≤ 2 := hC0

public theorem natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage_of_eq
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q m N : Nat) (hm4 : 4 ≤ m) (hdm : 2 * m = q + 5)
    (hsize : (q + 5) + (q + 5) = N) (hmEven : Even m)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin N))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenTwoBlockWreathPreimage (q + 5) (by
        have h' : N = (q + 5) + (q + 5) := hsize.symm
        exact h' ▸ f)) :
    Nat.card f.ker ≤ 2 := by
  subst N
  exact natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage
    q m hm4 hdm hmEven hM f hf hker hkerTwo P hP

/-- Theorem 5.2.3, universality clause: the double cover `2A_{n+5}` is a
universal covering group of `A_{n+5}` unless `n + 5 = 6` or `7`. -/
public theorem theorem_5_2_3_b_universality (n : Nat) (hn6 : n + 5 ≠ 6)
    (hn7 : n + 5 ≠ 7) :
    Covering.IsUniversal.{0, 0, __ch5_Theorem523Core_w} (schurAlternatingCovering n) := by
  have hbound : Nat.card
        (alternatingFreeCentralCovering n).toMonoidHom.ker ≤ 2 := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn0 : n = 0
        · subst n
          rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two]
        have hn1 : 1 ≤ n := by omega
        let f := alternatingFreeCentralCovering n
        let P : Sylow 2 (AlternatingFreeCentralDerived n) := default
        have hsmall : ∀ d : Nat, 5 ≤ d → d < n + 5 →
            d ≠ 6 → d ≠ 7 →
            Nat.card
              (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker ≤ 2 := by
          intro d hd5 hdlt hd6 hd7
          have hsub : d - 5 + 5 = d := by omega
          apply ih
          · omega
          · intro h
            apply hd6
            rw [← hsub]
            exact h
          · intro h
            apply hd7
            rw [← hsub]
            exact h
        by_cases hodd : Odd (n + 5)
        · exact natCard_ker_alternatingFreeCentralCovering_le_two_of_odd_degree_of_predecessor_le_two
            n hn1 hn6 hn7 hodd (by
              have hpred : n + 4 - 5 = n - 1 := by omega
              apply ih
              · omega
              · intro h
                apply hn6
                rw [hpred] at h
                omega
              · intro h
                have hn3' : n = 3 := by
                  rw [hpred] at h
                  omega
                rw [hn3'] at hodd
                rcases hodd with ⟨k, hk⟩
                omega)
        have hEven : Even (n + 5) := (Nat.even_or_odd (n + 5)).resolve_right hodd
        let Q : Sylow 2 (alternatingGroup (Fin (n + 5))) :=
          P.mapSurjective f.surjective
        by_cases hn3 : n = 3
        · subst n
          obtain ⟨Q0, hQ0⟩ :=
            exists_sylow_two_le_evenTwoBlockWreathFinHom_range 2 (by omega)
          have hkerTwo :=
            isTwoGroup_ker_alternatingFreeCentralCovering 3 (by omega) (by omega)
          let P0 : Sylow 2 (AlternatingFreeCentralDerived 3) :=
            Q0.comapOfKerIsPGroup f.toMonoidHom hkerTwo (by
              rw [MonoidHom.range_eq_top.mpr f.surjective]
              exact le_top)
          have hP0 : (P0 : Subgroup (AlternatingFreeCentralDerived 3)) ≤
              evenTwoBlockWreathPreimage 4 f.toMonoidHom := by
            intro x hx
            exact hQ0 hx
          exact natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage_a8
            f.toMonoidHom f.surjective f.ker_le_center hkerTwo P0 hP0
        have hn4 : 4 ≤ n := by
          by_contra hn4
          have hn3le : n ≤ 3 := by omega
          interval_cases n <;> simp_all
        have hm9 : 9 ≤ n + 5 := by omega
        have hmnot9 : n + 5 ≠ 9 := by
          intro hm9eq
          apply hodd
          rw [hm9eq]
          exact ⟨4, by omega⟩
        have hm10 : 10 ≤ n + 5 := by omega
        by_cases hnotTrans : ¬ MulAction.IsPretransitive Q (Fin (n + 5))
        · exact natCard_ker_le_two_of_even_degree_of_not_pretransitive_sylow
            (n + 5) hm10 hEven f.toMonoidHom f.surjective
            f.ker_le_center
            (isTwoGroup_ker_alternatingFreeCentralCovering n hn6 hn7)
            P hnotTrans hsmall
        let : MulAction.IsPretransitive Q (Fin (n + 5)) := by
          exact Classical.byContradiction hnotTrans
        let y : Fin (n + 5) := ⟨0, by omega⟩
        obtain ⟨s, hs⟩ := Q.isPGroup'.card_orbit y
        have horbit : Nat.card (MulAction.orbit Q y) = n + 5 := by
          rw [MulAction.orbit_eq_univ]
          simp
        have hpow : n + 5 = 2 ^ s := horbit.symm.trans hs
        have hs4 : 4 ≤ s := by
          by_contra hs4
          have hs3 : s ≤ 3 := by omega
          interval_cases s <;> norm_num at hpow <;> omega
        let d := 2 ^ (s - 2)
        let q := 2 * d - 5
        have hd5 : 4 ≤ d := by
          dsimp [d]
          have hpowd : 4 ≤ 2 ^ (s - 2) := by
            rw [show 4 = 2 ^ 2 by norm_num]
            apply Nat.pow_le_pow_right (by decide)
            exact Nat.le_sub_of_add_le (by omega)
          omega
        have hdm : 2 * d = q + 5 := by
          dsimp [q]
          omega
        have hdEven : Even d := by
          rw [even_iff_two_dvd]
          refine ⟨2 ^ (s - 3), ?_⟩
          dsimp [d]
          rw [show s - 2 = (s - 3) + 1 by omega, pow_succ]
          simp [Nat.mul_comm]
        have hblock : q + 5 = 2 ^ (s - 1) := by
          dsimp [q, d]
          rw [show s - 1 = (s - 2) + 1 by omega, pow_succ]
          omega
        have hsize : (q + 5) + (q + 5) = n + 5 := by
          calc
            (q + 5) + (q + 5) = 2 ^ (s - 1) + 2 ^ (s - 1) := by rw [hblock]
            _ = 2 ^ s := by
              calc
                2 ^ (s - 1) + 2 ^ (s - 1) = 2 ^ (s - 1) * 2 := by omega
                _ = 2 ^ s := by
                  rw [← pow_succ]
                  congr 1; omega
            _ = n + 5 := hpow.symm
        let : Nonempty (Fin (q + 5)) :=
          ⟨⟨0, by omega⟩⟩
        let : Finite (twoBlockWreathGroup (q + 5)) :=
          Finite.of_equiv
            ((Fin 2 → Equiv.Perm (Fin (q + 5))) × Equiv.Perm (Fin 2))
            (SemidirectProduct.equivProd
              (φ := permuteCoordinatesHom (Fin 2)
                (Equiv.Perm (Fin (q + 5))))).symm
        let Q0 : Sylow 2 (evenTwoBlockWreathGroup (q + 5)) :=
          Classical.choice Sylow.nonempty
        let H0 : Subgroup
            (alternatingGroup (Fin ((q + 5) + (q + 5)))) :=
          (Q0 : Subgroup (evenTwoBlockWreathGroup (q + 5))).map
            (evenTwoBlockWreathFinHom (q + 5))
        have hfactor :
            (Nat.card (evenTwoBlockWreathGroup (q + 5))).factorization 2 =
              (Nat.card
                (alternatingGroup (Fin ((q + 5) + (q + 5))))).factorization 2 := by
          rw [hblock]
          exact evenTwoBlockWreathGroup_factorization_eq_ambient (s - 1) (by omega)
        have hH0card : Nat.card H0 =
            2 ^ (Nat.card
              (alternatingGroup (Fin ((q + 5) + (q + 5))))).factorization 2 := by
          change Nat.card
            ((Q0 : Subgroup (evenTwoBlockWreathGroup (q + 5))).map
              (evenTwoBlockWreathFinHom (q + 5))) = _
          rw [Subgroup.card_map_of_injective
            (evenTwoBlockWreathFinHom_injective (q + 5)),
            Sylow.card_eq_multiplicity Q0]
          rw [hfactor]
        let P0 : Sylow 2
            (alternatingGroup (Fin ((q + 5) + (q + 5)))) :=
          Sylow.ofCard H0 hH0card
        have hP0 : P0.toSubgroup ≤
            (evenTwoBlockWreathFinHom (q + 5)).range := by
          change H0 ≤ (evenTwoBlockWreathFinHom (q + 5)).range
          exact Subgroup.map_le_range _ _
        let f' : AlternatingFreeCentralDerived n →*
            alternatingGroup (Fin ((q + 5) + (q + 5))) := hsize.symm ▸ f.toMonoidHom
        have hf' : Function.Surjective f' := by
          intro z
          obtain ⟨x, hx⟩ := f.surjective (hsize ▸ z)
          refine ⟨x, ?_⟩
          cases hsize
          simpa [f'] using hx
        have hker' : IsPGroup 2 f'.ker := by
          have hker0 :=
            isTwoGroup_ker_alternatingFreeCentralCovering n hn6 hn7
          dsimp [f']
          cases hsize
          exact hker0
        let P' : Sylow 2 (AlternatingFreeCentralDerived n) :=
          P0.comapOfKerIsPGroup f' hker' (by
            rw [MonoidHom.range_eq_top.mpr hf']
            exact le_top)
        have hP' : (P' : Subgroup (AlternatingFreeCentralDerived n)) ≤
            evenTwoBlockWreathPreimage (q + 5) (by
              have h' : n + 5 = (q + 5) + (q + 5) := hsize.symm
              exact h' ▸ f.toMonoidHom) := by
          intro x hx
          have hxP0 : f' x ∈ P0.toSubgroup := hx
          have hxW := hP0 hxP0
          simpa [evenTwoBlockWreathPreimage] using hxW
        have hMq : Nat.card
            (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2 :=
          ih q (by omega) (by omega) (by omega)
        exact natCard_ker_le_two_of_sylow_le_evenTwoBlockWreathPreimage_of_eq
           q d (n + 5) (by omega) hdm hsize hdEven
           hMq f.toMonoidHom f.surjective f.ker_le_center
          (isTwoGroup_ker_alternatingFreeCentralCovering n hn6 hn7) P' hP'
  have hfree : Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker = 2 :=
    Nat.le_antisymm hbound
      (two_le_natCard_ker_alternatingFreeCentralCovering n)
  exact Covering.isUniversal_of_card_two_of_universal
    (alternatingFreeCentralCovering n)
    (alternatingFreeCentralCovering_isUniversal n)
    (alternatingFreeCentralCovering_isUniversal n)
    hfree (schurAlternatingCovering n) (theorem_5_2_3_a n)

end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523Core -/

/- BEGIN Theory.PrimeCycleRotationCoordinateEvaluation -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_PrimeCycleRotationCoordinateEvaluation_u

/-- A prime-cycle rotation coordinate records the image of the chosen cycle
basis under that rotation. -/
public theorem primeCycleRotationCoordinate_evaluation
    {Ω : Type __ch5_PrimeCycleRotationCoordinateEvaluation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime)
    (a : CycleRotationGroup x) (c : x.cycleFactorsFinset) :
    (cycleCoordinateEquiv x hx c
      (Multiplicative.toAdd ((primeCycleRotationCoordinates x hx) a c))).1 =
      (a c).1 (cycleBasis x c) := by
  let e : Multiplicative (ZMod (orderOf x)) ≃* Subgroup.zpowers c.1 :=
    zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (cycleFactorZPowers_card_of_primeOrder x hx c)
  change ((basisZPowersEquivSupport x c) (e (e.symm (a c)))).1 = _
  rw [e.apply_symm_apply]
  unfold basisZPowersEquivSupport
  let hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
  let b : c.1.support :=
    ⟨cycleBasis x c, (cycleBasis x).mem_support_self c⟩
  change (((a c).1 * (hcycle.zpowersEquivSupport.symm b).1)
    (Classical.choose hcycle)) = (a c).1 (cycleBasis x c)
  rw [Equiv.Perm.mul_apply]
  have hb := congrArg Subtype.val
    (hcycle.zpowersEquivSupport.apply_symm_apply b)
  exact congrArg (fun ω => (a c).1 ω) hb

end GLS3.Chapter5
/- END Theory.PrimeCycleRotationCoordinateEvaluation -/
