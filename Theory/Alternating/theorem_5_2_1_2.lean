module

public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Theory.SpecificGroups.DihedralSolvable

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
public import Theory.Alternating.Aut
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.AlternatingFourThreeCycle -/
noncomputable section

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5

private def __ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private def __ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

private def __ch5_AlternatingFourThreeCycle_alternatingFourThreeCyclePerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

public def alternatingFourRootOne : alternatingGroup (Fin 4) :=
  ⟨__ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

public def alternatingFourRootTwo : alternatingGroup (Fin 4) :=
  ⟨__ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- A fixed three-cycle used with the standard Klein four subgroup of `A₄`. -/
public def alternatingFourThreeCycle : alternatingGroup (Fin 4) :=
  ⟨__ch5_AlternatingFourThreeCycle_alternatingFourThreeCyclePerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

/-- The standard normal Klein four subgroup of `A₄`. -/
@[expose] public def alternatingFourKlein : Subgroup (alternatingGroup (Fin 4)) :=
  { carrier := {1, alternatingFourRootOne, alternatingFourRootTwo,
      alternatingFourRootOne * alternatingFourRootTwo}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        simp [alternatingFourRootOne, alternatingFourRootTwo,
          __ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm, __ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm] <;> decide
    inv_mem' := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp [alternatingFourRootOne, alternatingFourRootTwo,
          __ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm, __ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm] <;> decide }


public theorem alternatingFourRootOne_support :
    alternatingFourRootOne.1.support.card = 4 := by decide

public theorem alternatingFourRootTwo_support :
    alternatingFourRootTwo.1.support.card = 4 := by decide

public theorem alternatingFourRootProduct_support :
    (alternatingFourRootOne * alternatingFourRootTwo).1.support.card = 4 := by decide

public theorem alternatingFourThreeCycle_order :
    orderOf alternatingFourThreeCycle = 3 := by
  apply orderOf_eq_prime <;> decide

public theorem alternatingFourKlein_card : Nat.card alternatingFourKlein = 4 := by
  change Nat.card (alternatingFourKlein : Set (alternatingGroup (Fin 4))) = 4
  rw [Nat.card_coe_set_eq]
  have hset : (alternatingFourKlein : Set (alternatingGroup (Fin 4))) =
      (↑({1, alternatingFourRootOne, alternatingFourRootTwo,
        alternatingFourRootOne * alternatingFourRootTwo} :
          Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))) := by
    ext x
    simp [alternatingFourKlein]
  rw [hset, Set.ncard_coe_finset]
  all_goals decide
public instance : alternatingFourKlein.Normal := by
  constructor
  intro n hn g
  simp only [alternatingFourKlein] at hn ⊢
  rcases hn with rfl | rfl | rfl | rfl <;>
    fin_cases g <;>
    simp [alternatingFourRootOne, alternatingFourRootTwo,
      __ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm, __ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm] <;> decide


public theorem alternatingFourKlein_comm (x y : alternatingFourKlein) :
    x * y = y * x := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  simp only [alternatingFourKlein] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    apply Subtype.ext <;> decide

public theorem alternatingFourThreeCycle_conj_fixed_iff
    (x : alternatingFourKlein) :
    alternatingFourThreeCycle * x.1 * alternatingFourThreeCycle⁻¹ = x.1 ↔
      x.1 = 1 := by
  rcases x with ⟨x, hx⟩
  simp only [alternatingFourKlein] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [alternatingFourThreeCycle, alternatingFourRootOne,
      alternatingFourRootTwo, __ch5_AlternatingFourThreeCycle_alternatingFourThreeCyclePerm,
      __ch5_AlternatingFourThreeCycle_alternatingFourRootOnePerm, __ch5_AlternatingFourThreeCycle_alternatingFourRootTwoPerm] <;> decide

public theorem alternatingFourKlein_sup_threeCycle :
    alternatingFourKlein ⊔ Subgroup.zpowers alternatingFourThreeCycle = ⊤ := by
  let T : Subgroup (alternatingGroup (Fin 4)) :=
    Subgroup.zpowers alternatingFourThreeCycle
  have hTcard : Nat.card T = 3 := by
    simpa [T] using
      (Nat.card_zpowers alternatingFourThreeCycle).trans
        alternatingFourThreeCycle_order
  have hinter : alternatingFourKlein ⊓ T = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [alternatingFourKlein_card, hTcard]
    all_goals decide
  have hrel : alternatingFourKlein.relIndex T = 3 := by
    rw [← Subgroup.inf_relIndex_right, hinter,
      Subgroup.relIndex_bot_left, hTcard]
  have hcard : Nat.card ↥(alternatingFourKlein ⊔ T) = 12 := by
    have hmul := Subgroup.relIndex_mul_relIndex
      (⊥ : Subgroup (alternatingGroup (Fin 4))) alternatingFourKlein
      (alternatingFourKlein ⊔ T) bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, alternatingFourKlein_card,
      Subgroup.relIndex_sup_left, hrel,
      Subgroup.relIndex_bot_left] at hmul
    omega
  change alternatingFourKlein ⊔ T = ⊤
  apply Subgroup.eq_top_of_card_eq
  rw [hcard]
  exact (alternatingGroup.card_of_card_eq_four (by simp)).symm

end GLS3.Chapter5
/- END Theory.AlternatingFourThreeCycle -/

/- BEGIN Theory.AlternatingSupportAtMostTwo -/
noncomputable section

namespace GLS3.Chapter5.PRank

/-- An even permutation supported on at most two points is trivial. -/
public theorem alternating_eq_one_of_support_card_le_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : alternatingGroup α) (hcard : σ.1.support.card ≤ 2) : σ = 1 := by
  by_contra hσ
  have hne : σ.1 ≠ 1 := by
    intro h
    apply hσ
    apply Subtype.ext
    exact h
  have htwo : σ.1.support.card = 2 := by
    exact le_antisymm hcard (Equiv.Perm.two_le_card_support_of_ne_one hne)
  have hsq : σ.1 ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    change σ.1 (σ.1 x) = x
    by_cases hsx : σ.1 x = x
    · simp [hsx]
    · by_contra hne2
      have hxmem : x ∈ σ.1.support := by
        simpa [Equiv.Perm.mem_support] using hsx
      have hymem : σ.1 x ∈ σ.1.support := by
        rw [Equiv.Perm.mem_support]
        exact fun h => hsx (σ.1.injective h)
      have hzmem : σ.1 (σ.1 x) ∈ σ.1.support := by
        rw [Equiv.Perm.mem_support]
        intro h
        have h1 : σ.1 (σ.1 x) = σ.1 x := σ.1.injective h
        exact hsx (σ.1.injective h1)
      have hxy : x ≠ σ.1 x := fun h => hsx h.symm
      have hyz : σ.1 x ≠ σ.1 (σ.1 x) := by
        intro h
        exact hsx (σ.1.injective h.symm)
      have hxz : x ≠ σ.1 (σ.1 x) := fun h => hne2 h.symm
      have hsubset : {x, σ.1 x, σ.1 (σ.1 x)} ⊆ σ.1.support := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hxmem
        · exact hymem
        · exact hzmem
      have hc := Finset.card_le_card hsubset
      have hthree : ({x, σ.1 x, σ.1 (σ.1 x)} : Finset α).card = 3 := by
        simp [hxy, hyz, hxz]
      omega
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hsq
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, htwo] at hsign
  have hle := σ.1.support.card_le_univ
  rw [htwo] at hle
  have hdiff : Fintype.card α - (Fintype.card α - 2) = 2 := by omega
  rw [hdiff] at hsign
  norm_num at hsign
  have heven : Equiv.Perm.sign σ.1 = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp σ.2
  rw [heven] at hsign
  norm_num at hsign

end GLS3.Chapter5.PRank
/- END Theory.AlternatingSupportAtMostTwo -/

/- BEGIN Theory.CenterOfCentralComplement -/
namespace GLS3.Chapter5

/-- If a group is generated by a central subgroup `X` and `R₁`, then the
center of `R₁` is exactly `X ∩ R₁`. -/
public theorem center_eq_subgroupOf_of_center_sup_eq_top
    {P : Type*} [Group P] (X R1 Z : Subgroup P)
    (hX : X = Subgroup.center P) (hsup : X ⊔ R1 = ⊤)
    (hinf : X ⊓ R1 = Z) :
    Subgroup.center R1 = Z.subgroupOf R1 := by
  apply le_antisymm
  · intro z hz
    have hzPcenter : z.1 ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hcentralizerX : X ≤ Subgroup.centralizer ({z.1} : Set P) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxCenter : x ∈ Subgroup.center P := hX ▸ hx
        exact (Subgroup.mem_center_iff.mp hxCenter z.1).symm
      have hcentralizerR : R1 ≤ Subgroup.centralizer ({z.1} : Set P) := by
        intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hz ⟨r, hr⟩)
      have htop : (⊤ : Subgroup P) ≤
          Subgroup.centralizer ({z.1} : Set P) := by
        rw [← hsup]
        exact sup_le hcentralizerX hcentralizerR
      have hg := htop (Subgroup.mem_top g)
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      exact hg
    have hzX : z.1 ∈ X := hX.symm ▸ hzPcenter
    have hzZ : z.1 ∈ Z := by
      rw [← hinf]
      exact ⟨hzX, z.2⟩
    exact hzZ
  · intro z hz
    have hzZ : z.1 ∈ Z := hz
    have hzInf : z.1 ∈ X ⊓ R1 := hinf.symm ▸ hzZ
    have hzCenter : z.1 ∈ Subgroup.center P := hX ▸ hzInf.1
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzCenter r.1

end GLS3.Chapter5
/- END Theory.CenterOfCentralComplement -/

/- BEGIN Theory.CentralCommutatorInversion -/
namespace GLS3.Chapter5

open scoped commutatorElement

/-- Multiplying the left input of a commutator by a central element does not
change the commutator. -/
public theorem commutatorElement_central_mul_left
    {G : Type*} [Group G] (z u v : G)
    (hz : z ∈ Subgroup.center G) :
    ⁅z * u, v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hzv : Commute z v := (Subgroup.mem_center_iff.mp hz v).symm
  have hzc : Commute z ⁅u, v⁆ :=
    (Subgroup.mem_center_iff.mp hz ⁅u, v⁆).symm
  rw [hzv.commutator_eq, hzc.eq]
  group

/-- Multiplying the right input of a commutator by a central element does not
change the commutator. -/
public theorem commutatorElement_central_mul_right
    {G : Type*} [Group G] (u z v : G)
    (hz : z ∈ Subgroup.center G) :
    ⁅u, z * v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have huz : Commute u z := Subgroup.mem_center_iff.mp hz u
  have hzc : Commute z ⁅u, v⁆ :=
    (Subgroup.mem_center_iff.mp hz ⁅u, v⁆).symm
  rw [huz.commutator_eq]
  simp only [one_mul]
  calc
    z * ⁅u, v⁆ * z⁻¹ = ⁅u, v⁆ * z * z⁻¹ := by rw [hzc.eq]
    _ = ⁅u, v⁆ := by group

/-- Inverting the first input inverts a central commutator. -/
public theorem commutatorElement_inv_left_of_mem_center
    {G : Type*} [Group G] (u v : G)
    (hc : ⁅u, v⁆ ∈ Subgroup.center G) :
    ⁅u⁻¹, v⁆ = ⁅u, v⁆⁻¹ := by
  rw [commutatorElement_inv_left, ← commutatorElement_inv]
  have hcomm : Commute u ⁅u, v⁆⁻¹ :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) u
  calc
    u⁻¹ * ⁅u, v⁆⁻¹ * u = u⁻¹ * (⁅u, v⁆⁻¹ * u) := by group
    _ = u⁻¹ * (u * ⁅u, v⁆⁻¹) := by rw [← hcomm.eq]
    _ = ⁅u, v⁆⁻¹ := by group


/-- The determinant-minus-one matrix used by the exceptional `A₆`
involution inverts a central commutator of order three. -/
public theorem commutatorElement_exceptional_matrix
    {G : Type*} [Group G] (u v : G)
    (hc : ⁅u, v⁆ ∈ Subgroup.center G)
    (hc3 : ⁅u, v⁆ ^ 3 = 1) :
    ⁅u⁻¹ * v, u⁻¹ * v⁻¹⁆ = ⁅u, v⁆⁻¹ := by
  let c : G := ⁅u, v⁆
  have hc' : c ∈ Subgroup.center G := hc
  have hcinv : c⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hc'
  have huv : ⁅u⁻¹, v⁆ = c⁻¹ :=
    commutatorElement_inv_left_of_mem_center u v hc
  have hvu : ⁅v, u⁻¹⁆ = c := by
    rw [← commutatorElement_inv, huv]
    simp [c]
  have huvinv : ⁅u⁻¹, v⁻¹⁆ = c := by
    rw [commutatorElement_inv_right, ← commutatorElement_inv, huv]
    simp only [inv_inv]
    have hcomm : Commute v⁻¹ c :=
      (Subgroup.mem_center_iff.mp hc' v⁻¹)
    rw [hcomm.eq]
    group
  have hvright : ⁅v, u⁻¹ * v⁻¹⁆ = c := by
    rw [commutatorElement_mul_right_eq_mul_conj, hvu]
    simp [commutatorElement_def]
  have huright : ⁅u⁻¹, u⁻¹ * v⁻¹⁆ = c := by
    rw [commutatorElement_mul_right_eq_mul_conj, huvinv]
    simp only [commutatorElement_self, one_mul]
    have hcomm : Commute u⁻¹ c :=
      Subgroup.mem_center_iff.mp hc' u⁻¹
    rw [hcomm.eq]
    group
  rw [commutatorElement_mul_left_eq_conj_mul, hvright, huright]
  have hcomm : Commute u⁻¹ c :=
    Subgroup.mem_center_iff.mp hc' u⁻¹
  rw [hcomm.eq]
  simp only [inv_inv]
  have hc2 : c * c = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [pow_succ, c] using hc3
  change c * u⁻¹ * u * c = c⁻¹
  calc
    c * u⁻¹ * u * c = c * c := by group
    _ = c⁻¹ := hc2

/-- Swapping the two inputs inverts their commutator. -/
public theorem commutatorElement_swap
    {G : Type*} [Group G] (u v : G) :
    ⁅v, u⁆ = ⁅u, v⁆⁻¹ := by
  exact (commutatorElement_inv (g₁ := u) (g₂ := v)).symm

end GLS3.Chapter5
/- END Theory.CentralCommutatorInversion -/

/- BEGIN Theory.CentralExtensionFrattini -/
set_option maxHeartbeats 800000

noncomputable section

open scoped IsMulCommutative

namespace GLS3.Chapter5

/-! A small A1 33.11 core.

The full printed proof of A1 33.11 invokes Gaschütz' complement theorem.  The
part used after that invocation is elementary and useful on its own: a central
`p`-subgroup which has a complement in a Sylow `p`-subgroup would be the image
of a perfect group in an abelian group, hence trivial.  We expose that core so
the remaining Frattini step can be formalized separately.
-/

/-- The commutator subgroup of a finite `p`-group is contained in its
Frattini subgroup.  The proof uses that every maximal subgroup of a finite
nilpotent group is normal and that the corresponding nontrivial nilpotent
simple quotient is abelian. -/
public theorem commutator_le_frattini_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : Nat} [Fact p.Prime]
    (hG : IsPGroup p G) : commutator G ≤ frattini G := by
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ?_
  have : Group.IsNilpotent G := hG.isNilpotent
  have hMall : ∀ K : Subgroup G, IsCoatom K → K.Normal :=
    (Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 |>.mp
      (show Group.IsNilpotent G from inferInstance)
  let : M.Normal := hMall M hM
  let q := QuotientGroup.mk' M
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hqker : q.ker = M := by
    dsimp [q]
    exact QuotientGroup.ker_mk' M
  let : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.ne_top
  have hbot : IsCoatom (⊥ : Subgroup (G ⧸ M)) := by
    refine ⟨bot_ne_top, ?_⟩
    intro K hK
    have hcomap : M < K.comap q := by
      exact lt_of_le_of_lt hqker.ge
        ((Subgroup.comap_lt_comap_of_surjective hq).mpr hK)
    have htop : K.comap q = ⊤ := hM.2 _ hcomap
    apply Subgroup.comap_injective hq
    rw [htop, Subgroup.comap_top]
  have hcenter_ne : Subgroup.center (G ⧸ M) ≠ ⊥ :=
    Group.IsNilpotent.center_ne_bot (G ⧸ M)
  have hcenter_top : Subgroup.center (G ⧸ M) = ⊤ :=
    hbot.lt_iff.mp (bot_lt_iff_ne_bot.mpr hcenter_ne)
  have hcomm : commutator (G ⧸ M) = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top (G ⧸ M)).mpr hcenter_top
  have hleker : commutator G ≤ q.ker := by
    change commutator G ≤ (⊥ : Subgroup (G ⧸ M)).comap q
    rw [← Subgroup.map_le_iff_le_comap]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq, ← commutator_def, hcomm]
  exact hleker.trans hqker.le

/-- A central subgroup of a Sylow `p`-subgroup of a finite perfect group lies
in the Frattini subgroup.  This proves the content of A1 33.11 directly by
transfer, without invoking the full Gaschütz complement theorem. -/
public theorem central_subgroup_le_frattini_sylow
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (P : Sylow p H)
    (X : Subgroup P)
    (hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H) :
    X ≤ frattini P := by
  let C := commutator P
  let qC := QuotientGroup.mk' C
  let : IsMulCommutative (P ⧸ C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      dsimp [C]
      exact le_rfl)
  let τ : H →* P ⧸ C := MonoidHom.transfer qC
  have hτone (g : H) : τ g = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker τ
      (Group.IsPerfect.mem_commutator (g := g))
  have hcommFrattini : C ≤ frattini P := by
    dsimp [C]
    exact commutator_le_frattini_of_isPGroup P.isPGroup'
  intro x hx
  let xH : H := (P : Subgroup H).subtype x
  have hxcenter : xH ∈ Subgroup.center H :=
    hXcentral (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hkey : ∀ (k : Nat) (g₀ : H),
      g₀⁻¹ * xH ^ k * g₀ ∈ (P : Subgroup H) →
        g₀⁻¹ * xH ^ k * g₀ = xH ^ k := by
    intro k g₀ _
    have hxpow : xH ^ k ∈ Subgroup.center H :=
      (Subgroup.center H).pow_mem hxcenter k
    have hc := Subgroup.mem_center_iff.mp hxpow g₀
    rw [mul_assoc, hc.symm]
    simp
  have hqCpow : qC (x ^ P.index) = 1 := by
    have hformula := MonoidHom.transfer_eq_pow qC xH hkey
    have harg :
        (⟨xH ^ P.index,
            MonoidHom.transfer_eq_pow_aux xH hkey⟩ : P) = x ^ P.index := by
      apply Subtype.ext
      rfl
    rw [harg] at hformula
    exact hformula.symm.trans (hτone xH)
  have hxpowC : x ^ P.index ∈ C := by
    exact (QuotientGroup.eq_one_iff (x ^ P.index)).mp hqCpow
  have hxpowF : x ^ P.index ∈ frattini P := hcommFrattini hxpowC
  let qF := QuotientGroup.mk' (frattini P)
  let hPF : IsPGroup p (P ⧸ frattini P) :=
    P.isPGroup'.to_quotient (frattini P)
  have hqFpow : qF x ^ P.index = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ P.index)).mpr hxpowF
  have hqFx : qF x = 1 := by
    apply (hPF.powEquiv' P.not_dvd_index).injective
    simpa using hqFpow
  exact (QuotientGroup.eq_one_iff x).mp hqFx

/-- A1 33.11 in kernel form: the part of a central kernel lying in a Sylow
`p`-subgroup belongs to that Sylow subgroup's Frattini subgroup. -/
public theorem ker_comap_le_frattini_sylow
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H] [Group G]
    {p : Nat} [Fact p.Prime] (P : Sylow p H) (f : H →* G)
    (hker : f.ker ≤ Subgroup.center H) :
    f.ker.comap (P : Subgroup H).subtype ≤ frattini P := by
  apply central_subgroup_le_frattini_sylow P
  rintro x ⟨y, hy, rfl⟩
  exact hker hy

/-- A1 33.12 in central-extension form: every prime dividing the kernel of a
finite perfect central extension also divides the order of the quotient. -/
public theorem prime_dvd_card_of_dvd_card_ker
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hpker : p ∣ Nat.card f.ker) :
    p ∣ Nat.card G := by
  by_contra hpG
  let P : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  let Q : Sylow p G := P.mapSurjective hsurj
  have hQcard : Nat.card Q = 1 := by
    rcases Q.isPGroup'.card_eq_or_dvd with hcard | hpQ
    · exact hcard
    · exact False.elim (hpG (hpQ.trans
        (Subgroup.card_subgroup_dvd_card (Q : Subgroup G))))
  have hQbot : (Q : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hQcard
  have hPmapbot : (P : Subgroup H).map f = ⊥ := by
    simpa [Q, Sylow.coe_mapSurjective] using hQbot
  have hPleker : (P : Subgroup H) ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (H := (P : Subgroup H)) (f := f)).mp hPmapbot
  have htopcentral :
      (⊤ : Subgroup P).map (P : Subgroup H).subtype ≤ Subgroup.center H := by
    rintro x ⟨y, _, rfl⟩
    exact hker (hPleker y.2)
  have htopFrattini : (⊤ : Subgroup P) ≤ frattini P :=
    central_subgroup_le_frattini_sylow P (⊤ : Subgroup P) htopcentral
  have hfrattini : frattini P = ⊤ := top_unique htopFrattini
  have hbotTop : (⊥ : Subgroup P) = ⊤ :=
    frattini_nongenerating (K := (⊥ : Subgroup P)) (by simp [hfrattini])
  have hPunique : ∀ x : P, x = 1 := by
    intro x
    apply Subgroup.mem_bot.mp
    rw [hbotTop]
    exact Subgroup.mem_top x
  have hPcard : Nat.card P = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (hPunique a).trans (hPunique b).symm⟩, ⟨1⟩⟩
  have hpH : p ∣ Nat.card H :=
    hpker.trans (Subgroup.card_subgroup_dvd_card f.ker)
  have hpIndex : p ∣ P.index := by
    rw [← P.card_mul_index, hPcard, one_mul] at hpH
    exact hpH
  exact P.not_dvd_index hpIndex

/-- A cyclic Sylow subgroup downstairs lifts to a cyclic Sylow subgroup in a
finite perfect central extension.  The kernel inside the Sylow subgroup lies
in its Frattini subgroup by A1 33.11, so a lift of one generator downstairs
already generates upstairs. -/
public theorem isCyclic_sylow_of_isCyclic_mapSurjective
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (P : Sylow p H) (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcyclic : IsCyclic (P.mapSurjective hsurj)) :
    IsCyclic P := by
  let Q : Sylow p G := P.mapSurjective hsurj
  let : IsCyclic Q := hcyclic
  obtain ⟨q, hqgen⟩ := IsCyclic.exists_generator (α := Q)
  have hqmap : (q : G) ∈ (P : Subgroup H).map f := by
    change (q : G) ∈ (Q : Subgroup G)
    exact q.2
  obtain ⟨xH, hxP, hfx⟩ := Subgroup.mem_map.mp hqmap
  let x : P := ⟨xH, hxP⟩
  have hfxq : f x = q := by
    exact hfx
  let K : Subgroup P := Subgroup.zpowers x
  have hKsup : K ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hyQ : f y ∈ (Q : Subgroup G) := by
      change f (y : H) ∈ (P : Subgroup H).map f
      exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
    let yQ : Q := ⟨f y, hyQ⟩
    obtain ⟨n, hn⟩ := hqgen yQ
    have hfy : f (y * x ^ (-n)) = 1 := by
      rw [map_mul, map_zpow, hfxq]
      change (yQ : G) * (q : G) ^ (-n) = 1
      rw [← hn]
      simp
    have hdiff : y * x ^ (-n) ∈ frattini P := by
      apply ker_comap_le_frattini_sylow P f hker
      exact hfy
    have hxpow : x ^ n ∈ K := by
      exact ⟨n, rfl⟩
    have hdecomp : y = (y * x ^ (-n)) * x ^ n := by
      simp
    rw [hdecomp]
    exact (K ⊔ frattini P).mul_mem
      (show y * x ^ (-n) ∈ K ⊔ frattini P from
        (le_sup_right : frattini P ≤ K ⊔ frattini P) hdiff)
      (show x ^ n ∈ K ⊔ frattini P from
        (le_sup_left : K ≤ K ⊔ frattini P) hxpow)
  have hKtop : K = ⊤ := frattini_nongenerating hKsup
  exact ⟨x, fun y => by
    show y ∈ K
    rw [hKtop]
    exact Subgroup.mem_top y⟩

/-- A central subgroup contained in a cyclic Sylow subgroup of a finite
perfect group is trivial.  Transfer to the cyclic Sylow subgroup is trivial
by perfectness, while on central elements it is the Sylow-index power map. -/
public theorem central_subgroup_eq_bot_of_isCyclic_sylow
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (P : Sylow p H) (hPcyclic : IsCyclic P)
    (X : Subgroup P)
    (hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H) :
    X = ⊥ := by
  let : IsCyclic P := hPcyclic
  let τ : H →* P := MonoidHom.transfer (MonoidHom.id P)
  have hτone (g : H) : τ g = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker τ
      (Group.IsPerfect.mem_commutator (g := g))
  apply le_antisymm
  · intro x hx
    let xH : H := (P : Subgroup H).subtype x
    have hxcenter : xH ∈ Subgroup.center H :=
      hXcentral (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hkey : ∀ (k : Nat) (g₀ : H),
        g₀⁻¹ * xH ^ k * g₀ ∈ (P : Subgroup H) →
          g₀⁻¹ * xH ^ k * g₀ = xH ^ k := by
      intro k g₀ _
      have hxpow : xH ^ k ∈ Subgroup.center H :=
        (Subgroup.center H).pow_mem hxcenter k
      have hc := Subgroup.mem_center_iff.mp hxpow g₀
      rw [mul_assoc, hc.symm]
      simp
    have hxpow : x ^ P.index = 1 := by
      have hformula := MonoidHom.transfer_eq_pow (MonoidHom.id P) xH hkey
      have harg :
          (⟨xH ^ P.index,
              MonoidHom.transfer_eq_pow_aux xH hkey⟩ : P) = x ^ P.index := by
        apply Subtype.ext
        rfl
      rw [harg] at hformula
      exact hformula.symm.trans (hτone xH)
    have hxone : x = 1 := by
      apply (P.isPGroup'.powEquiv' P.not_dvd_index).injective
      simpa using hxpow
    exact Subgroup.mem_bot.mpr hxone
  · exact bot_le

/-- A1 33.14 in central-extension form: a finite perfect central extension
with `p`-group kernel over a group with cyclic Sylow `p`-subgroups has trivial
kernel. -/
public theorem ker_eq_bot_of_isPGroup_of_isCyclic_sylow
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hcyclic : ∀ Q : Sylow p G, IsCyclic Q) :
    f.ker = ⊥ := by
  let P : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  have hkerP : f.ker ≤ (P : Subgroup H) := hkerp.le_sylow_of_normal P
  have hPcyclic : IsCyclic P :=
    isCyclic_sylow_of_isCyclic_mapSurjective
      P f hsurj hker (hcyclic (P.mapSurjective hsurj))
  let X : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  have hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H := by
    rintro x ⟨y, hy, rfl⟩
    exact hker hy
  have hXbot : X = ⊥ :=
    central_subgroup_eq_bot_of_isCyclic_sylow P hPcyclic X hXcentral
  apply le_antisymm
  · intro z hz
    let zP : P := ⟨z, hkerP hz⟩
    have hzX : zP ∈ X := hz
    rw [hXbot] at hzX
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hzX))
  · exact bot_le

/-- A1 33.14 in prime-divisibility form: if all Sylow `p`-subgroups of the
quotient are cyclic, then `p` does not divide the kernel of any finite perfect
central extension. -/
public theorem not_dvd_card_ker_of_isCyclic_sylow
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcyclic : ∀ Q : Sylow p G, IsCyclic Q) :
    ¬ p ∣ Nat.card f.ker := by
  intro hpker
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hpker
  have hzorderH : orderOf (z : H) = p :=
    (Subgroup.orderOf_coe z).trans hzorder
  let Z : Subgroup H := Subgroup.zpowers (z : H)
  have hZcard : Nat.card Z = p := by
    dsimp [Z]
    rw [Nat.card_zpowers, hzorderH]
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    simpa using hZcard
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPcyclic : IsCyclic P :=
    isCyclic_sylow_of_isCyclic_mapSurjective
      P f hsurj hker (hcyclic (P.mapSurjective hsurj))
  let X : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  have hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H := by
    rintro x ⟨y, hy, rfl⟩
    exact hker hy
  have hXbot : X = ⊥ :=
    central_subgroup_eq_bot_of_isCyclic_sylow P hPcyclic X hXcentral
  have hzZ : (z : H) ∈ Z := Subgroup.mem_zpowers (z : H)
  let zP : P := ⟨z, hZP hzZ⟩
  have hzX : zP ∈ X := z.2
  rw [hXbot] at hzX
  have hzPone : zP = 1 := Subgroup.mem_bot.mp hzX
  have hzHone : (z : H) = 1 := congrArg Subtype.val hzPone
  have hzorderOne : orderOf (z : H) = 1 := orderOf_eq_one_iff.mpr hzHone
  exact (Fact.out : Nat.Prime p).ne_one (hzorderH.symm.trans hzorderOne)

/-- Projection onto the first factor of a complement whose first factor is
central.  The centrality hypothesis makes the multiplication decomposition a
direct-product homomorphism. -/
public noncomputable def centralComplementProjection
    {G : Type*} [Group G] (X Y : Subgroup G)
    (hXY : X.IsComplement' Y) (hX : X ≤ Subgroup.center G) : G →* X where
  toFun g := (hXY.equiv g).fst
  map_one' := by
    apply Subtype.ext
    simpa using congrArg (fun z : X × Y => (z.1 : G))
      (hXY.equiv_one X.one_mem Y.one_mem)
  map_mul' a b := by
    let ea := hXY.equiv a
    let eb := hXY.equiv b
    have hxb : (eb.fst : G) * ea.snd = ea.snd * eb.fst :=
      (Subgroup.mem_center_iff.mp (hX eb.fst.2) ea.snd).symm
    have hpairs : hXY.equiv (a * b) =
        (ea.fst * eb.fst, ea.snd * eb.snd) := by
      apply hXY.1
      change ((hXY.equiv (a * b)).fst : G) * (hXY.equiv (a * b)).snd =
        ((ea.fst : G) * eb.fst) * ((ea.snd : G) * eb.snd)
      rw [hXY.equiv_fst_mul_equiv_snd]
      rw [← hXY.equiv_fst_mul_equiv_snd a, ← hXY.equiv_fst_mul_equiv_snd b]
      calc
        (((ea.fst : G) * ea.snd) * ((eb.fst : G) * eb.snd)) =
            ea.fst * (ea.snd * eb.fst) * eb.snd := by simp [mul_assoc]
        _ = ea.fst * (eb.fst * ea.snd) * eb.snd := by rw [hxb.symm]
        _ = ((ea.fst : G) * eb.fst) * (ea.snd * eb.snd) := by simp [mul_assoc]
    exact congrArg Prod.fst hpairs

@[simp]
public theorem centralComplementProjection_apply_left
    {G : Type*} [Group G] (X Y : Subgroup G)
    (hXY : X.IsComplement' Y) (hX : X ≤ Subgroup.center G) (x : X) :
    centralComplementProjection X Y hXY hX x = x := by
  exact hXY.equiv_fst_eq_self_of_mem_of_one_mem Y.one_mem x.2

/-- A central `p`-subgroup with a complement in a Sylow `p`-subgroup is
trivial when the ambient finite group is perfect.  This is the transfer core
of the Gaschütz step in A1 33.11. -/
public theorem central_subgroup_eq_bot_of_isComplement_sylow
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (P : Sylow p H)
    (X Y : Subgroup P)
    (hXcentral : X.map (P : Subgroup H).subtype ≤ Subgroup.center H)
    (hXY : X.IsComplement' Y) : X = ⊥ := by
  have hXPcenter : X ≤ Subgroup.center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hXcentral (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)) y
  let : IsMulCommutative X :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hXPcenter a.2) b.1).symm⟩⟩
  let φ : P →* X := centralComplementProjection X Y hXY hXPcenter
  let τ : H →* X := MonoidHom.transfer φ
  have hτ (x : X) : τ ((P : Subgroup H).subtype x.1) = x ^ P.index := by
    change MonoidHom.transfer φ ((P : Subgroup H).subtype x.1) = _
    rw [MonoidHom.transfer_eq_pow φ ((P : Subgroup H).subtype x.1)]
    · have harg :
          (⟨((P : Subgroup H).subtype x.1 : H) ^ P.index,
              MonoidHom.transfer_eq_pow_aux ((P : Subgroup H).subtype x.1) (by
                intro k g₀ _
                have hxcenter : ((P : Subgroup H).subtype x.1 : H) ∈
                    Subgroup.center H :=
                  hXcentral (Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
                have hxpow : ((P : Subgroup H).subtype x.1 : H) ^ k ∈
                    Subgroup.center H := (Subgroup.center H).pow_mem hxcenter k
                have hc := Subgroup.mem_center_iff.mp hxpow g₀
                rw [mul_assoc, hc.symm]
                simp)⟩ : P) = (x ^ P.index : X).1 := by
            apply Subtype.ext
            rfl
      rw [harg]
      exact centralComplementProjection_apply_left X Y hXY hXPcenter (x ^ P.index)
    · intro k g₀ _
      have hxcenter : ((P : Subgroup H).subtype x.1 : H) ∈ Subgroup.center H :=
        hXcentral (Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
      have hxpow : ((P : Subgroup H).subtype x.1 : H) ^ k ∈ Subgroup.center H :=
        (Subgroup.center H).pow_mem hxcenter k
      have hc := Subgroup.mem_center_iff.mp hxpow g₀
      rw [mul_assoc, hc.symm]
      simp
  have hτsurj : Function.Surjective τ := by
    intro z
    let hPX : IsPGroup p X := P.isPGroup'.to_subgroup X
    obtain ⟨x, hx⟩ := (hPX.powEquiv' P.not_dvd_index).surjective z
    refine ⟨(P : Subgroup H).subtype x.1, ?_⟩
    rw [hτ x]
    exact hx
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective hτsurj
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : X) (1 : X))
  · exact bot_le

end GLS3.Chapter5
/- END Theory.CentralExtensionFrattini -/

/- BEGIN Theory.CentralizerNormalAbelianSemidirect -/
namespace GLS3.Chapter5

/-- In an internal semidirect product, if the complement acts faithfully on
the normal abelian factor, then that factor is its own centralizer. -/
public theorem centralizer_inf_sup_eq_left_of_disjoint_complement
    {G : Type*} [Group G] (R L : Subgroup G)
    [IsMulCommutative R]
    (hnormal : L ≤ Subgroup.normalizer R)
    (hfaithful : Disjoint L (Subgroup.centralizer (R : Set G))) :
    Subgroup.centralizer (R : Set G) ⊓ (R ⊔ L) = R := by
  apply le_antisymm
  · intro g hg
    have hgprod : g ∈ (↑(R ⊔ L) : Set G) := hg.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hnormal] at hgprod
    rcases hgprod with ⟨r, hr, l, hl, rfl⟩
    have hrcentral : r ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R)
          ⟨s, hs⟩ ⟨r, hr⟩)
    have hlcentral : l ∈ Subgroup.centralizer (R : Set G) := by
      have hprod := hg.1
      have heq : l = r⁻¹ * (r * l) := by group
      rw [heq]
      exact (Subgroup.centralizer (R : Set G)).mul_mem
        ((Subgroup.centralizer (R : Set G)).inv_mem hrcentral) hprod
    have hlbot : l ∈ (⊥ : Subgroup G) := by
      rw [← hfaithful.eq_bot]
      exact ⟨hl, hlcentral⟩
    have hlone : l = 1 := by simpa using hlbot
    simpa [hlone] using hr
  · intro r hr
    have hrcentral : r ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R)
          ⟨s, hs⟩ ⟨r, hr⟩)
    exact ⟨hrcentral, (show R ≤ R ⊔ L from le_sup_left) hr⟩

end GLS3.Chapter5
/- END Theory.CentralizerNormalAbelianSemidirect -/

/- BEGIN Theory.CyclicFourFrattini -/
noncomputable section

namespace GLS3.Chapter5

/-- In a cyclic group of order four, the subgroup of order two is the
Frattini subgroup. -/
public theorem frattini_eq_of_isCyclic_card_four
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (Z : Subgroup G) (hGcard : Nat.card G = 4) (hZcard : Nat.card Z = 2) :
    frattini G = Z := by
  classical
  have subgroup_eq_of_card_eq_two
      (H K : Subgroup G) (hHcard : Nat.card H = 2)
      (hKcard : Nat.card K = 2) : H = K := by
    let : Fintype G := Fintype.ofFinite G
    obtain ⟨h, hh, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hHcard
    obtain ⟨k, hk, kuniq⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hKcard
    have hhpowH : h ^ 2 = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have hkpowK : k ^ 2 = 1 := by
      rw [← hKcard]
      exact pow_card_eq_one'
    have hhpow : (h.1 : G) ^ 2 = 1 := congrArg Subtype.val hhpowH
    have hkpow : (k.1 : G) ^ 2 = 1 := congrArg Subtype.val hkpowK
    have hhne : (h.1 : G) ≠ 1 := fun e => hh (Subtype.ext e)
    have hkne : (k.1 : G) ≠ 1 := fun e => hk (Subtype.ext e)
    have hhk : (h.1 : G) = k.1 := by
      by_contra hne
      let roots : Finset G := {g | g ^ 2 = 1}
      have hsub : ({1, h.1, k.1} : Finset G) ⊆ roots := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simp [roots]
        · simpa [roots] using hhpow
        · simpa [roots] using hkpow
      have hthree : ({1, h.1, k.1} : Finset G).card = 3 := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simpa using hne
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hhne, Ne.symm hkne⟩
      have hle : 3 ≤ roots.card := by
        rw [← hthree]
        exact Finset.card_le_card hsub
      have hrootle : roots.card ≤ 2 := by
        simpa [roots] using
          (IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by omega))
      omega
    apply le_antisymm
    · intro x hx
      by_cases hxone : (⟨x, hx⟩ : H) = 1
      · rw [show x = 1 from congrArg Subtype.val hxone]
        exact K.one_mem
      · have hx_h : (⟨x, hx⟩ : H) = h := huniq _ hxone
        rw [show x = h.1 from congrArg Subtype.val hx_h, hhk]
        exact k.2
    · intro x hx
      by_cases hxone : (⟨x, hx⟩ : K) = 1
      · rw [show x = 1 from congrArg Subtype.val hxone]
        exact H.one_mem
      · have hx_k : (⟨x, hx⟩ : K) = k := kuniq _ hxone
        rw [show x = k.1 from congrArg Subtype.val hx_k, ← hhk]
        exact h.2
  have card_eq_two_of_isCoatom (M : Subgroup G) (hM : IsCoatom M) :
      Nat.card M = 2 := by
    have hdvd : Nat.card M ∣ 2 ^ 2 := by
      simpa [hGcard] using Subgroup.card_subgroup_dvd_card M
    obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · have hMbot : M = ⊥ :=
        (Subgroup.eq_bot_iff_card M).mpr (by simpa using hkcard)
      have hZneBot : Z ≠ ⊥ := by
        intro hZbot
        have : Nat.card Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hZbot
        omega
      have hZneTop : Z ≠ ⊤ := by
        intro hZtop
        have : Nat.card Z = Nat.card G :=
          (Subgroup.card_eq_iff_eq_top Z).mpr hZtop
        omega
      have hbotZ : (⊥ : Subgroup G) < Z :=
        lt_of_le_of_ne bot_le (Ne.symm hZneBot)
      have := hM.2 Z (hMbot ▸ hbotZ)
      exact (hZneTop this).elim
    · simpa using hkcard
    · have hMtop : M = ⊤ := Subgroup.eq_top_of_card_eq M (by omega)
      exact (hM.1 hMtop).elim
  have hZcoatom : IsCoatom Z := by
    rw [isCoatom_iff_ge_of_le]
    constructor
    · intro hZtop
      have : Nat.card Z = Nat.card G :=
        (Subgroup.card_eq_iff_eq_top Z).mpr hZtop
      omega
    · intro K hKneTop hZK
      have hdvd : Nat.card K ∣ 2 ^ 2 := by
        simpa [hGcard] using Subgroup.card_subgroup_dvd_card K
      obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      interval_cases k
      · have hKcard : Nat.card K = 1 := by simpa using hkcard
        have hlecard : Nat.card Z ≤ Nat.card K :=
          Nat.card_le_card_of_injective
            (fun z : Z => (⟨z.1, hZK z.2⟩ : K))
            (fun _ _ h => Subtype.ext (congrArg (fun x : K => x.1) h))
        omega
      · have hKcard : Nat.card K = 2 := by simpa using hkcard
        exact (Subgroup.eq_of_le_of_card_ge hZK (by omega)).ge
      · have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K (by omega)
        exact (hKneTop hKtop).elim
  apply le_antisymm
  · exact frattini_le_coatom hZcoatom
  · rw [frattini, Order.radical]
    refine le_iInf fun M => le_iInf fun hM => ?_
    rw [subgroup_eq_of_card_eq_two Z M hZcard
      (card_eq_two_of_isCoatom M hM)]

end GLS3.Chapter5
/- END Theory.CyclicFourFrattini -/

/- BEGIN Theory.DirectProductSubgroupMulEquiv -/
open scoped Pointwise

namespace GLS3.Chapter5

/-- Elementwise commuting disjoint subgroups form an internal direct product. -/
public theorem exists_mulEquiv_prod_sup_of_disjoint_of_commute
    {G : Type*} [Group G] (A B : Subgroup G)
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1) :
    Nonempty ((A × B) ≃* ↥(A ⊔ B)) := by
  let f : A × B →* ↥(A ⊔ B) :=
    { toFun := fun x =>
        ⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
          (x.1.1 * x.2.1) * (y.1.1 * y.2.1)
        calc
          (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
              x.1.1 * (y.1.1 * x.2.1) * y.2.1 := by simp [mul_assoc]
          _ = x.1.1 * (x.2.1 * y.1.1) * y.2.1 := by
            rw [(hcommute y.1 x.2).eq]
          _ = (x.1.1 * x.2.1) * (y.1.1 * y.2.1) := by simp [mul_assoc] }
  have hcentralizer : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcommute ⟨a, ha⟩ ⟨b, hb⟩).eq.symm
  have hnormalizer : A ≤ Subgroup.normalizer B :=
    hcentralizer.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hsurjective : Function.Surjective f := by
    intro x
    have hxset : x.1 ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnormalizer]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hxset
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact hab
  have hinjective : Function.Injective f := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  exact ⟨MulEquiv.ofBijective f ⟨hinjective, hsurjective⟩⟩

end GLS3.Chapter5
/- END Theory.DirectProductSubgroupMulEquiv -/

/- BEGIN Theory.ElementaryAbelianFrattini -/
noncomputable section

namespace GLS3.Chapter5

/-- The Frattini subgroup of the multiplicative group underlying an
`F₂`-vector space is trivial. -/
public theorem frattini_multiplicative_zmod_two_module_eq_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    frattini (Multiplicative V) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    by_contra hxone
    have hv : x.toAdd ≠ 0 := by
      simpa using hxone
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
    let phi : Multiplicative V →* Multiplicative (ZMod 2) :=
      AddMonoidHom.toMultiplicative f.toAddMonoidHom
    have hsurj : Function.Surjective phi := by
      intro y
      refine Multiplicative.rec ?_ y
      intro a
      refine ⟨Multiplicative.ofAdd (a • x.toAdd), ?_⟩
      exact congrArg Multiplicative.ofAdd (by simp [hf])
    have hbotCoatom : IsCoatom (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
      constructor
      · exact (show (⊥ : Subgroup (Multiplicative (ZMod 2))) ≠ ⊤ from bot_ne_top)
      · intro K hK
        have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
          rw [Nat.card_congr Multiplicative.ofAdd]
          exact Nat.card_zmod 2
        have hp : (Nat.card (Multiplicative (ZMod 2))).Prime :=
          hcard.symm ▸ Nat.prime_two
        let : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨hp⟩
        exact K.eq_bot_or_eq_top_of_prime_card |>.resolve_left hK.ne'
    have hkerCoatom : IsCoatom phi.ker := by
      change IsCoatom (Subgroup.comap phi ⊥)
      exact Subgroup.isCoatom_comap_of_surjective hsurj hbotCoatom
    have hxker : x ∈ phi.ker := frattini_le_coatom hkerCoatom hx
    have hfx0 : f x.toAdd = 0 := by
      exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hxker)
    exact one_ne_zero (hf.symm.trans hfx0)
  · exact bot_le

/-- Every homomorphism to the multiplicative group of an `F₂`-vector space
kills the Frattini subgroup. -/
public theorem frattini_le_ker_of_hom_to_multiplicative_zmod_two_module
    {P V : Type*} [Group P] [AddCommGroup V] [Module (ZMod 2) V]
    (q : P →* Multiplicative V) : frattini P ≤ q.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  by_contra hqx
  have hv : (q x).toAdd ≠ 0 := by
    intro hv
    apply hqx
    exact congrArg Multiplicative.ofAdd hv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  let phi : P →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp q
  have hsurj : Function.Surjective phi := by
    intro y
    refine Multiplicative.rec ?_ y
    intro a
    fin_cases a
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact congrArg Multiplicative.ofAdd rfl
    · refine ⟨x, ?_⟩
      exact congrArg Multiplicative.ofAdd hf
  have hbotCoatom : IsCoatom (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
    constructor
    · exact (show (⊥ : Subgroup (Multiplicative (ZMod 2))) ≠ ⊤ from bot_ne_top)
    · intro K hK
      have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_congr Multiplicative.ofAdd]
        exact Nat.card_zmod 2
      have hp : (Nat.card (Multiplicative (ZMod 2))).Prime :=
        hcard.symm ▸ Nat.prime_two
      let : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨hp⟩
      exact K.eq_bot_or_eq_top_of_prime_card |>.resolve_left hK.ne'
  have hkerCoatom : IsCoatom phi.ker := by
    change IsCoatom (Subgroup.comap phi ⊥)
    exact Subgroup.isCoatom_comap_of_surjective hsurj hbotCoatom
  have hxker : x ∈ phi.ker := frattini_le_coatom hkerCoatom hx
  have hfx0 : f (q x).toAdd = 0 := by
    exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hxker)
  exact one_ne_zero (hf.symm.trans hfx0)

end GLS3.Chapter5
/- END Theory.ElementaryAbelianFrattini -/

/- BEGIN Theory.EqualSquareRootFourNoncommuting -/
namespace GLS3.Chapter5

/-- Three elements with the same nontrivial involutory square cannot form a commuting pair when the product has that square as well. -/
public theorem not_commute_of_equal_nontrivial_squares
    {G : Type*} [Group G] (u v z : G)
    (hz2 : z ^ 2 = 1) (hzne : z ≠ 1)
    (hu2 : u ^ 2 = z) (hv2 : v ^ 2 = z)
    (huv2 : (u * v) ^ 2 = z) :
    ¬ Commute u v := by
  intro huv
  have hsq : (u * v) ^ 2 = u ^ 2 * v ^ 2 := huv.mul_pow 2
  rw [hu2, hv2, ← pow_two, hz2] at hsq
  exact hzne (huv2.symm.trans hsq)

end GLS3.Chapter5
/- END Theory.EqualSquareRootFourNoncommuting -/

/- BEGIN Theory.FreeCentralExtension -/
namespace GLS3.Chapter5.FreeCentralExtension
universe __ch5_FreeCentralExtension_u

variable {F : Type __ch5_FreeCentralExtension_u} [Group F]

/-! ## Suzuki's free central extension attached to a presentation

For a presentation `G ≅ F / K`, Suzuki [Su1, Chapter 2, §9, (9.2)] sets
`N = [F,K]`, the subgroup generated by all commutators `[x,k]` with
`x ∈ F` and `k ∈ K`.  The natural map `F/N → F/K` is then a central
extension whose kernel is the image of `K` in `F/N`.

This module formalizes precisely that presentation-level construction.  The
freeness of `F` is not needed for assertions (9.2)(1)--(3); it enters only in
the lifting property (9.2)(4), which will be added when the alternating-group
presentation is connected to arbitrary central extensions.
-/

/-- Suzuki's subgroup `N = [F,K]` used to form the free central extension of
the presented group `F/K`. -/
@[expose]
public def freeCentralKernel (K : Subgroup F) : Subgroup F :=
  ⁅(⊤ : Subgroup F), K⁆

public instance freeCentralKernelNormal (K : Subgroup F) [K.Normal] :
    (freeCentralKernel K).Normal := by
  dsimp [freeCentralKernel]
  infer_instance

/-- Suzuki (9.2)(1): `[F,K]` is contained in the relator subgroup `K`. -/
public theorem freeCentralKernel_le (K : Subgroup F) [K.Normal] :
    freeCentralKernel K ≤ K := by
  exact Subgroup.commutator_le_right (⊤ : Subgroup F) K

/-- The natural quotient map `F/[F,K] → F/K`. -/
@[expose]
public def freeCentralProjection (K : Subgroup F) [K.Normal] :
    F ⧸ freeCentralKernel K →* F ⧸ K :=
  QuotientGroup.map (freeCentralKernel K) K (MonoidHom.id F) (by
    intro x hx
    simpa using freeCentralKernel_le K hx)

@[simp]
public theorem freeCentralProjection_mk (K : Subgroup F) [K.Normal] (x : F) :
    freeCentralProjection K (QuotientGroup.mk' (freeCentralKernel K) x) =
      QuotientGroup.mk' K x :=
  rfl

/-- The natural map `F/[F,K] → F/K` is surjective. -/
public theorem freeCentralProjection_surjective (K : Subgroup F) [K.Normal] :
    Function.Surjective (freeCentralProjection K) := by
  apply QuotientGroup.map_surjective_of_surjective
  simpa [Function.comp_def] using QuotientGroup.mk'_surjective K

/-- The kernel of `F/[F,K] → F/K` is the image of `K`, namely `K/[F,K]`. -/
public theorem freeCentralProjection_ker (K : Subgroup F) [K.Normal] :
    (freeCentralProjection K).ker =
      K.map (QuotientGroup.mk' (freeCentralKernel K)) := by
  simpa [freeCentralProjection] using
    (QuotientGroup.ker_map (N := freeCentralKernel K) K (MonoidHom.id F)
      (by
        intro x hx
        simpa using freeCentralKernel_le K hx))

/-- Suzuki (9.2)(2): the image `K/[F,K]` is central in `F/[F,K]`. -/
public theorem map_le_center_freeCentralKernel (K : Subgroup F) [K.Normal] :
    K.map (QuotientGroup.mk' (freeCentralKernel K)) ≤
      Subgroup.center (F ⧸ freeCentralKernel K) := by
  rw [← Subgroup.commutator_top_left_eq_bot_iff_le_center]
  let q := QuotientGroup.mk' (freeCentralKernel K)
  calc
    ⁅(⊤ : Subgroup (F ⧸ freeCentralKernel K)), K.map q⁆ =
        ⁅(⊤ : Subgroup F).map q, K.map q⁆ := by
      rw [Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective (freeCentralKernel K))]
    _ = (freeCentralKernel K).map q := by
      exact (Subgroup.map_commutator (⊤ : Subgroup F) K q).symm
    _ = ⊥ := by
      simp [q]

/-- Suzuki (9.2)(3), kernel form: the natural quotient map is a central
extension. -/
public theorem freeCentralProjection_ker_le_center (K : Subgroup F) [K.Normal] :
    (freeCentralProjection K).ker ≤
      Subgroup.center (F ⧸ freeCentralKernel K) := by
  rw [freeCentralProjection_ker]
  exact map_le_center_freeCentralKernel K

end GLS3.Chapter5.FreeCentralExtension
/- END Theory.FreeCentralExtension -/

/- BEGIN Theory.PcoreDefinition -/
namespace GLS3.Chapter5

/-- A concrete formulation of `O_p(G)`: `O` is a normal `p`-subgroup
containing every normal `p`-subgroup of `G`. -/
@[expose]
public def IsPCore {G : Type*} [Group G] (p : Nat) (O : Subgroup G) : Prop :=
  O.Normal ∧ IsPGroup p O ∧
    ∀ P : Subgroup G, P.Normal → IsPGroup p P → P ≤ O

public theorem IsPCore.normal {G : Type*} [Group G] {p : Nat}
    {O : Subgroup G} (h : IsPCore p O) : O.Normal := h.1

public theorem IsPCore.isPGroup {G : Type*} [Group G] {p : Nat}
    {O : Subgroup G} (h : IsPCore p O) : IsPGroup p O := h.2.1

public theorem IsPCore.maximal {G : Type*} [Group G] {p : Nat}
    {O : Subgroup G} (h : IsPCore p O) :
    ∀ P : Subgroup G, P.Normal → IsPGroup p P → P ≤ O := h.2.2

end GLS3.Chapter5
/- END Theory.PcoreDefinition -/

/- BEGIN Theory.PerfectSubgroupLeAmbientCommutator -/
namespace GLS3.Chapter5

/-- Every perfect subgroup lies in the derived subgroup of its ambient group. -/
public theorem perfect_subgroup_le_ambient_commutator
    {G : Type*} [Group G] (I : Subgroup G) [Group.IsPerfect I] :
    I ≤ _root_.commutator G := by
  intro i hi
  have hcomm : (⟨i, hi⟩ : I) ∈ _root_.commutator I :=
    Group.IsPerfect.mem_commutator
  have hmap : i ∈ Subgroup.map I.subtype (_root_.commutator I) :=
    Subgroup.mem_map_of_mem I.subtype hcomm
  rw [Subgroup.map_subtype_commutator] at hmap
  exact Subgroup.commutator_mono le_top le_top hmap

end GLS3.Chapter5
/- END Theory.PerfectSubgroupLeAmbientCommutator -/

/- BEGIN Theory.PermCongrSupportCard -/
namespace GLS3.Chapter5

public theorem card_support_permCongr
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  have hsupport : (e.permCongr σ).support =
      σ.support.map e.toEmbedding := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp [Equiv.Perm.mem_support]
  rw [hsupport, Finset.card_map]

end GLS3.Chapter5
/- END Theory.PermCongrSupportCard -/

/- BEGIN Theory.PermutationFiberAction -/
noncomputable section

namespace FiberAction

variable {α β : Type*} (f : α → β)

@[expose] public def PreservesFibers (g : Equiv.Perm α) : Prop :=
  ∃ q : Equiv.Perm β, ∀ x, f (g x) = q (f x)

@[expose] public def subgroup : Subgroup (Equiv.Perm α) where
  carrier := {g | PreservesFibers f g}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨qg, hqg⟩ ⟨qh, hqh⟩
    refine ⟨qg * qh, ?_⟩
    intro x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hqg, hqh]
  inv_mem' := by
    rintro g ⟨q, hq⟩
    refine ⟨q⁻¹, ?_⟩
    intro x
    have h := congrArg (fun y => q⁻¹ y) (hq (g⁻¹ x))
    simpa using h.symm

variable (hf : Function.Surjective f)

public theorem quotient_unique (hf : Function.Surjective f) {g : Equiv.Perm α} {q r : Equiv.Perm β}
    (hq : ∀ x, f (g x) = q (f x)) (hr : ∀ x, f (g x) = r (f x)) : q = r := by
  ext y
  obtain ⟨x, rfl⟩ := hf y
  exact (hq x).symm.trans (hr x)

@[expose] public noncomputable def quotientPerm (g : subgroup f) : Equiv.Perm β :=
  Classical.choose g.property

public theorem quotientPerm_spec (g : subgroup f) (x : α) :
    f ((g : Equiv.Perm α) x) = quotientPerm f g (f x) :=
  (Classical.choose_spec g.property) x

@[expose] public noncomputable def quotientHom : subgroup f →* Equiv.Perm β where
  toFun := quotientPerm f
  map_one' := by
    apply quotient_unique f hf (g := 1)
    · exact quotientPerm_spec f 1
    · simp
  map_mul' g h := by
    apply quotient_unique f hf (g := g * h)
    · exact quotientPerm_spec f (g * h)
    · intro x
      change f ((g : Equiv.Perm α) ((h : Equiv.Perm α) x)) = _
      rw [quotientPerm_spec f g, quotientPerm_spec f h]
      rfl

end FiberAction
/- END Theory.PermutationFiberAction -/

/- BEGIN Theory.PreimageSupComplementAssembly -/
noncomputable section

namespace GLS3.Chapter5

open scoped Pointwise

/-- A complement to the restricted kernel over the right factor of a quotient
semidirect product assembles to a complement of the left-factor preimage. -/
public theorem preimageSup_isComplement'_of_rightPreimage_kernel_isComplement'
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (A B : Subgroup Q) :
    let Hbar := A ⊔ B
    let H := Hbar.comap f
    let R := A.comap f
    let E := B.comap f
    let iE : E →* H := E.subtype.codRestrict H
      (fun z => (le_sup_right : B ≤ A ⊔ B) z.2)
    ∀ C : Subgroup E,
      (A.subgroupOf Hbar).IsComplement' (B.subgroupOf Hbar) →
      (f.ker.comap E.subtype).IsComplement' C →
      (R.subgroupOf H).IsComplement' (C.map iE) := by
  dsimp only
  let Hbar := A ⊔ B
  let H := Hbar.comap f
  let R := A.comap f
  let E := B.comap f
  let iE : E →* H := E.subtype.codRestrict H
    (fun z => (le_sup_right : B ≤ A ⊔ B) z.2)
  intro C hbarComp hC
  have hABDisjoint : Disjoint A B := by
    rw [Subgroup.disjoint_def]
    intro q hqA hqB
    let qH : Hbar := ⟨q, (le_sup_left : A ≤ A ⊔ B) hqA⟩
    have hqBot : qH ∈ (⊥ : Subgroup Hbar) := by
      rw [← hbarComp.disjoint.eq_bot]
      exact ⟨hqA, hqB⟩
    have hqOne : qH = 1 := by simpa using hqBot
    exact congrArg Subtype.val hqOne
  have hdisj : Disjoint (R.subgroupOf H) (C.map iE) := by
    rw [Subgroup.disjoint_def]
    intro z hzR hzC
    rcases hzC with ⟨c, hcC, hcz⟩
    have hfcA : f c.1 ∈ A := by
      have hzRA : f z.1 ∈ A := hzR
      have hczG : c.1 = z.1 := congrArg (fun y : H => (y : G)) hcz
      rw [← hczG] at hzRA
      exact hzRA
    have hfcBot : f c.1 ∈ A ⊓ B := ⟨hfcA, c.2⟩
    have hfcOne : f c.1 = 1 := by
      have : f c.1 ∈ (⊥ : Subgroup Q) := by
        rw [← hABDisjoint.eq_bot]
        exact hfcBot
      simpa using this
    have hcKer : c ∈ f.ker.comap E.subtype :=
      MonoidHom.mem_ker.mpr hfcOne
    have hcBot : c ∈ (⊥ : Subgroup E) := by
      rw [← hC.disjoint.eq_bot]
      exact ⟨hcKer, hcC⟩
    have hcOne : c = 1 := by simpa using hcBot
    rw [← hcz, hcOne, map_one]
  have hmul : ((R.subgroupOf H : Subgroup H) : Set H) *
      ((C.map iE : Subgroup H) : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    let zbar : Hbar := ⟨f z.1, z.2⟩
    obtain ⟨ab, hab⟩ := hbarComp.2 zbar
    let abar : A.subgroupOf Hbar := ab.1
    let bbar : B.subgroupOf Hbar := ab.2
    obtain ⟨g, hg⟩ := hf bbar.1.1
    let gE : E := ⟨g, by
      change f g ∈ B
      rw [hg]
      exact bbar.2⟩
    obtain ⟨kc, hkc⟩ := hC.2 gE
    let k : f.ker.comap E.subtype := kc.1
    let c : C := kc.2
    have hfc : f c.1.1 = bbar.1.1 := by
      have hkcE : (k : E) * (c : E) = gE := by
        simpa [k, c] using hkc
      have hkOne : f k.1.1 = 1 := MonoidHom.mem_ker.mp k.2
      have hkcG := congrArg (fun y : E => (y : G)) hkcE
      change k.1.1 * c.1.1 = gE.1 at hkcG
      have h := congrArg f hkcG
      rw [map_mul] at h
      rw [hkOne, one_mul, hg] at h
      exact h
    let cH : H := iE c.1
    let rH : H := z * cH⁻¹
    have hrA : f rH.1 ∈ A := by
      have habQ := congrArg (fun y : Hbar => (y : Q)) hab
      change abar.1.1 * bbar.1.1 = f z.1 at habQ
      change f (z.1 * cH.1⁻¹) ∈ A
      rw [map_mul, map_inv]
      change f z.1 * (f c.1.1)⁻¹ ∈ A
      rw [hfc, ← habQ]
      simpa using A.mul_mem abar.2 (A.one_mem)
    have hrR : rH ∈ R.subgroupOf H := hrA
    have hcMap : cH ∈ C.map iE := ⟨c.1, c.2, rfl⟩
    refine Set.mem_mul.mpr ⟨rH, hrR, cH, hcMap, ?_⟩
    simp [rH]
  exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul

end GLS3.Chapter5
/- END Theory.PreimageSupComplementAssembly -/

/- BEGIN Theory.PrimeOrderFrattini -/
noncomputable section

namespace GLS3.Chapter5

/-- The Frattini subgroup of a finite group of prime order is trivial. -/
public theorem frattini_eq_bot_of_prime_card
    {G : Type*} [Group G] [Finite G] {p : Nat} [Fact p.Prime]
    (hcard : Nat.card G = p) :
    frattini G = ⊥ := by
  let : Fact (Nat.card G).Prime :=
    ⟨hcard ▸ (Fact.out : p.Prime)⟩
  have hbotCoatom : IsCoatom (⊥ : Subgroup G) := by
    rw [isCoatom_iff_ge_of_le]
    constructor
    · intro hbotTop
      have hcardOne : Nat.card G = 1 := by
        rw [← Subgroup.card_top (G := G), ← hbotTop]
        exact (Subgroup.eq_bot_iff_card (⊥ : Subgroup G)).mp rfl
      exact (Fact.out : p.Prime).ne_one (hcard.symm.trans hcardOne)
    · intro K hKneTop _
      rcases K.eq_bot_or_eq_top_of_prime_card with hKbot | hKtop
      · exact hKbot.le
      · exact (hKneTop hKtop).elim
  exact le_antisymm (frattini_le_coatom hbotCoatom) bot_le

end GLS3.Chapter5
/- END Theory.PrimeOrderFrattini -/

/- BEGIN Theory.SubgroupSupZpowersMapEquiv -/
namespace GLS3.Chapter5

/-- An injective homomorphism transports a subgroup enlarged by one cyclic
subgroup to the corresponding enlarged image subgroup. -/
public noncomputable def subgroupSupZpowersMapEquivOfInjective
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (t : G) (φ : G →* K)
    (hφ : Function.Injective φ) :
    ↥(H ⊔ Subgroup.zpowers t) ≃*
      ↥(H.map φ ⊔ Subgroup.zpowers (φ t)) := by
  let e := Subgroup.equivMapOfInjective (H ⊔ Subgroup.zpowers t) φ hφ
  have hmap : (H ⊔ Subgroup.zpowers t).map φ =
      H.map φ ⊔ Subgroup.zpowers (φ t) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  exact e.trans (MulEquiv.subgroupCongr hmap)

end GLS3.Chapter5
/- END Theory.SubgroupSupZpowersMapEquiv -/

/- BEGIN Theory.SubnormalAbsorbsStableCommutator -/
namespace GLS3.Chapter5

/-- If `M` is generated by its commutators with a subnormal subgroup `I`,
then `M` is contained in `I`. -/
public theorem le_of_isSubnormal_of_le_commutator
    {G : Type*} [Group G] (M I : Subgroup G)
    (hI : I.IsSubnormal) (hstable : M ≤ ⁅M, I⁆) :
    M ≤ I :=
  Subgroup.le_of_isSubnormal_of_le_commutator M I hI hstable

end GLS3.Chapter5
/- END Theory.SubnormalAbsorbsStableCommutator -/

/- BEGIN Theory.SubnormalNormalClosureTop -/
namespace GLS3.Chapter5

/-- A subnormal subgroup whose normal closure is the ambient group is the
ambient group. -/
public theorem eq_top_of_isSubnormal_of_normalClosure_eq_top
    {G : Type*} [Group G] (H : Subgroup G)
    (hH : H.IsSubnormal)
    (hclosure : Subgroup.normalClosure (H : Set G) = ⊤) :
    H = ⊤ := by
  rcases hH.lt_normal with htop | ⟨N, hNnormal, hHN, hNlt⟩
  · exact htop
  · let : N.Normal := hNnormal
    have hclosure_le : Subgroup.normalClosure (H : Set G) ≤ N :=
      Subgroup.normalClosure_le_normal hHN
    rw [hclosure] at hclosure_le
    exact False.elim ((not_le_of_gt hNlt) hclosure_le)

end GLS3.Chapter5
/- END Theory.SubnormalNormalClosureTop -/

/- BEGIN Theory.SubnormalThroughNormalIntermediate -/
namespace GLS3.Chapter5

/-- Subnormality in a normal intermediate subgroup lifts to the larger
ambient subgroup. -/
public theorem subnormal_subgroupOf_of_subnormal_of_normal
    {G : Type*} [Group G] (I H C : Subgroup G)
    (hIH : I ≤ H) (hHC : H ≤ C)
    (hIsubnormal : (I.subgroupOf H).IsSubnormal)
    (hHnormal : (H.subgroupOf C).Normal) :
    (I.subgroupOf C).IsSubnormal := by
  let Hc : Subgroup C := H.subgroupOf C
  let Ic : Subgroup C := I.subgroupOf C
  let eH : H ≃* Hc :=
    { toFun := fun h => ⟨⟨h.1, hHC h.2⟩, h.2⟩
      invFun := fun h => ⟨h.1.1, h.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hmap : Subgroup.map eH.toMonoidHom (I.subgroupOf H) =
      Ic.subgroupOf Hc := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      refine ⟨eH.symm x, ?_, eH.apply_symm_apply x⟩
      exact hx
  have hsubnormalHc : (Ic.subgroupOf Hc).IsSubnormal := by
    rw [← hmap]
    exact hIsubnormal.map eH.surjective
  have hlift := hsubnormalHc.trans' hHnormal.isSubnormal
  have hIcHc : Ic ≤ Hc := by
    intro i hi
    exact hIH hi
  rw [Subgroup.map_subgroupOf_eq_of_le hIcHc] at hlift
  exact hlift

end GLS3.Chapter5
/- END Theory.SubnormalThroughNormalIntermediate -/

/- BEGIN Theory.TraceZeroPermutationModule -/
noncomputable section

namespace GLS3.Chapter5

/-- The coefficient-sum-zero subgroup of the natural permutation module over
`ZMod 2`. -/
public def traceZeroTwoSubgroup (r : Nat) : AddSubgroup (Fin r → ZMod 2) where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Pi.add_apply, Finset.sum_add_distrib, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [Pi.neg_apply, ha]

@[simp]
public theorem mem_traceZeroTwoSubgroup {r : Nat} (v : Fin r → ZMod 2) :
    v ∈ traceZeroTwoSubgroup r ↔ ∑ i, v i = 0 := Iff.rfl

/-- The derived subgroup of `H`, transported back to the ambient group. -/
public def derivedSubgroupIn {G : Type*} [Group G]
    (H : Subgroup G) : Subgroup G :=
  (_root_.commutator ↥H).map H.subtype

/-- `R ⋊ L` carries the natural trace-zero permutation-module structure:
`L ≅ S_r`, `R` is the multiplicative form of the coefficient-sum-zero
submodule, and conjugation by `L` permutes the coordinates. -/
@[expose]
public def IsTraceZeroPermutationModule {G : Type*} [Group G]
    (R L : Subgroup G) (r : Nat) : Prop :=
  ∃ (eR : R ≃* Multiplicative ↥(traceZeroTwoSubgroup r))
    (eL : L ≃* Equiv.Perm (Fin r)),
    ∀ l : L, ∀ v : R, ∃ w : R,
      w.1 = l.1 * v.1 * l.1⁻¹ ∧
        (Multiplicative.toAdd (eR w)).1 =
          fun i => (Multiplicative.toAdd (eR v)).1 ((eL l).symm i)

/-- A finite `2`-subgroup is extraspecial when its center, derived subgroup,
and Frattini subgroup coincide and have order two. -/
@[expose]
public def IsExtraspecialTwoSubgroup {G : Type*} [Group G]
    (P : Subgroup G) : Prop :=
  IsPGroup 2 P ∧
    _root_.commutator P = Subgroup.center P ∧
    frattini P = Subgroup.center P ∧
    Nat.card (Subgroup.center P) = 2

end GLS3.Chapter5
/- END Theory.TraceZeroPermutationModule -/

/- BEGIN Theory.VectorQuotientCentralComplement -/
noncomputable section

namespace GLS3.Chapter5

/-- The inverse image of a linear complement to the image of `X` complements
`X` modulo the kernel of a homomorphism to an `F₂`-vector group. -/
public theorem exists_sup_eq_top_inf_eq_ker_of_vector_quotient
    {P V : Type*} [Group P] [AddCommGroup V] [Module (ZMod 2) V]
    (q : P →* Multiplicative V) (X : Subgroup P) (hkerX : q.ker ≤ X) :
    ∃ R1 : Subgroup P, X ⊔ R1 = ⊤ ∧ X ⊓ R1 = q.ker := by
  let U : Submodule (ZMod 2) V :=
    AddSubgroup.toZModSubmodule 2 (X.map q).toAddSubgroup'
  obtain ⟨W, hUW⟩ := U.exists_isCompl
  let Wm : Subgroup (Multiplicative V) := W.toAddSubgroup.toSubgroup
  let R1 : Subgroup P := Wm.comap q
  refine ⟨R1, ?_, ?_⟩
  · apply top_unique
    intro g _
    have htop : U ⊔ W = ⊤ := hUW.codisjoint.eq_top
    have hv : (q g).toAdd ∈ U ⊔ W := by
      rw [htop]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hv with ⟨u, hu, w, hw, huw⟩
    have huX : Multiplicative.ofAdd u ∈ X.map q := hu
    rcases huX with ⟨x, hx, hqx⟩
    have hwR : Multiplicative.ofAdd w ∈ Wm := hw
    have hdiff : x⁻¹ * g ∈ R1 := by
      change q (x⁻¹ * g) ∈ Wm
      rw [map_mul, map_inv, hqx]
      have heq : q g = Multiplicative.ofAdd u * Multiplicative.ofAdd w := by
        exact congrArg Multiplicative.ofAdd huw.symm
      rw [heq]
      simp
      exact hwR
    have hxSup : x ∈ X ⊔ R1 := (le_sup_left : X ≤ X ⊔ R1) hx
    have hdSup : x⁻¹ * g ∈ X ⊔ R1 :=
      (le_sup_right : R1 ≤ X ⊔ R1) hdiff
    simpa using (X ⊔ R1).mul_mem hxSup hdSup
  · apply le_antisymm
    · intro g hg
      have hgX : g ∈ X := hg.1
      have hgW : q g ∈ Wm := hg.2
      have hqgU : q g ∈ X.map q := ⟨g, hgX, rfl⟩
      have hzero : q g = 1 := by
        have hadd : (q g).toAdd ∈ U ⊓ W := ⟨hqgU, hgW⟩
        rw [hUW.disjoint.eq_bot] at hadd
        exact congrArg Multiplicative.ofAdd
          (show (q g).toAdd = 0 from hadd)
      exact MonoidHom.mem_ker.mpr hzero
    · intro g hg
      exact ⟨hkerX hg, by
        change q g ∈ Wm
        rw [MonoidHom.mem_ker.mp hg]
        exact Wm.one_mem⟩

end GLS3.Chapter5
/- END Theory.VectorQuotientCentralComplement -/

/- BEGIN Theory.EvenInvolutionSupportFour -/
noncomputable section
namespace GLS3.Chapter5

/-- A nontrivial even involution supported on at most four points moves exactly four points. -/
public theorem evenInvolution_support_card_eq_four_of_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : alternatingGroup α) (hsq : σ.1 ^ 2 = 1)
    (hne : σ ≠ 1) (hle : σ.1.support.card ≤ 4) :
    σ.1.support.card = 4 := by
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hsq
  have hsupport : σ.1.support.card = 2 * σ.1.cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hct]
    simp [Nat.mul_comm]
  have hsign : Equiv.Perm.sign σ.1 = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp σ.2
  have heven : Even (σ.1.cycleType.sum + σ.1.cycleType.card) := by
    apply (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hsum : σ.1.cycleType.sum = 2 * σ.1.cycleType.card := by
    rw [hct]
    simp [Nat.mul_comm]
  have hpos : 0 < σ.1.support.card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hne
    apply Subtype.ext
    exact Equiv.Perm.card_support_eq_zero.mp hzero
  rcases heven with ⟨k, hk⟩
  omega

end GLS3.Chapter5
/- END Theory.EvenInvolutionSupportFour -/

/- BEGIN Theory.AlternatingCenterQuotientCovering -/
noncomputable section

namespace GLS3.Chapter5

/-- An identification of the quotient by the center with an alternating group
is represented by a covering whose kernel is exactly the center. -/
public theorem exists_alternatingCenterQuotientCovering
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) [IsQuasisimple (alternatingGroup (Fin n))]
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    ∃ f : Covering K (alternatingGroup (Fin n)),
      f.toMonoidHom.ker = Subgroup.center K := by
  let f : K →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hsurj : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  let c : Covering K (alternatingGroup (Fin n)) := {
    toMonoidHom := f
    surjective := hsurj
  }
  refine ⟨c, ?_⟩
  change f.ker = Subgroup.center K
  rw [show f = e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center K)) by rfl,
    MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' (Subgroup.center K)) e.toMonoidHom e.injective,
    QuotientGroup.ker_mk']

end GLS3.Chapter5
/- END Theory.AlternatingCenterQuotientCovering -/

/- BEGIN Theory.Automorphism -/
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Automorphism_u

namespace GLS3.Chapter5

/-- The subgroup fixed pointwise by a group automorphism. -/
@[expose]
public def automorphismFixedSubgroup {G : Type*} [Group G]
    (x : MulAut G) : Subgroup G where
  carrier := {g | x g = g}
  one_mem' := x.map_one
  mul_mem' := by
    intro a b ha hb
    change x a = a at ha
    change x b = b at hb
    simp [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change x a = a at ha
    simp [map_inv, ha]

public theorem commonThreeCycle_rotate
    {Ω : Type*} [DecidableEq Ω] {x y z : Ω}
    (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Equiv.swap x y * Equiv.swap x z =
      Equiv.swap y z * Equiv.swap y x := by
  have hconj :
      Equiv.swap x y * Equiv.swap x z * Equiv.swap x y =
        Equiv.swap y z := by
    simpa [Equiv.swap_comm] using
      (Equiv.swap_mul_swap_mul_swap
        (x := z) (y := x) (z := y) hxz.symm hyz.symm)
  calc
    Equiv.swap x y * Equiv.swap x z =
        (Equiv.swap x y * Equiv.swap x z * Equiv.swap x y) *
          Equiv.swap x y := by simp [mul_assoc]
    _ = Equiv.swap y z * Equiv.swap x y := by rw [hconj]
    _ = Equiv.swap y z * Equiv.swap y x := by rw [Equiv.swap_comm x y]

public theorem adjacentThreeCycle_eq_common
    {Ω : Type*} [DecidableEq Ω] {x y z : Ω}
    (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Equiv.swap x y * Equiv.swap y z =
      Equiv.swap x z * Equiv.swap x y := by
  have hconj :
      Equiv.swap x y * Equiv.swap y z * Equiv.swap x y =
        Equiv.swap x z := by
    simpa [Equiv.swap_comm] using
      (Equiv.swap_mul_swap_mul_swap
        (x := z) (y := y) (z := x) hyz.symm hxz.symm)
  calc
    Equiv.swap x y * Equiv.swap y z =
        (Equiv.swap x y * Equiv.swap y z * Equiv.swap x y) *
          Equiv.swap x y := by simp [mul_assoc]
    _ = Equiv.swap x z * Equiv.swap x y := by rw [hconj]

public theorem commonThreeCycle_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {x y z : Ω}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (Equiv.swap x y * Equiv.swap x z).support = {x, y, z} := by
  rw [Equiv.swap_comm x y]
  calc
    (Equiv.swap y x * Equiv.swap x z).support = {y, x, z} :=
      Equiv.Perm.support_swap_mul_swap
        (by simp [hxz, hyz, Ne.symm hxy])
    _ = {x, y, z} := by ext; simp [or_left_comm]

public theorem commonThreeCycle_apply_first
    {Ω : Type*} [DecidableEq Ω] {x y z : Ω}
    (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (Equiv.swap x y * Equiv.swap x z) x = z := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hxz.symm hyz.symm]

public theorem commonThreeCycle_apply_second
    {Ω : Type*} [DecidableEq Ω] {x y z : Ω}
    (hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z) :
    (Equiv.swap x y * Equiv.swap x z) y = x := by
  rw [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hxy.symm hyz,
    Equiv.swap_apply_right]

public theorem commonThreeCycle_apply_third
    {Ω : Type*} [DecidableEq Ω] {x y z : Ω}
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z) :
    (Equiv.swap x y * Equiv.swap x z) z = y := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_left]

public theorem commonThreeCycle_eq_cyclic
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {a b c x y z : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Equiv.swap a b * Equiv.swap a c =
      Equiv.swap x y * Equiv.swap x z) :
    (x = a ∧ y = b ∧ z = c) ∨
      (x = b ∧ y = c ∧ z = a) ∨
      (x = c ∧ y = a ∧ z = b) := by
  have hsupp := congrArg Equiv.Perm.support h
  rw [commonThreeCycle_support hab hac hbc,
    commonThreeCycle_support hxy hxz hyz] at hsupp
  have hxmem : x ∈ ({a, b, c} : Finset Ω) := by
    rw [hsupp]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with hxa | hxb | hxc
  · subst x
    have heval := congrArg (fun p : Equiv.Perm Ω ↦ p a) h
    rw [commonThreeCycle_apply_first hab hac hbc,
      commonThreeCycle_apply_first hxy hxz hyz] at heval
    have hz : z = c := heval.symm
    subst z
    have hymem : y ∈ ({a, b, c} : Finset Ω) := by
      rw [hsupp]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
    exact Or.inl ⟨rfl, by aesop, rfl⟩
  · subst x
    have heval := congrArg (fun p : Equiv.Perm Ω ↦ p b) h
    rw [commonThreeCycle_apply_second hab hac hbc,
      commonThreeCycle_apply_first hxy hxz hyz] at heval
    have hz : z = a := heval.symm
    subst z
    have hymem : y ∈ ({a, b, c} : Finset Ω) := by
      rw [hsupp]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
    exact Or.inr (Or.inl ⟨rfl, by aesop, rfl⟩)
  · subst x
    have heval := congrArg (fun p : Equiv.Perm Ω ↦ p c) h
    rw [commonThreeCycle_apply_third hab hac hbc,
      commonThreeCycle_apply_first hxy hxz hyz] at heval
    have hz : z = b := heval.symm
    subst z
    have hymem : y ∈ ({a, b, c} : Finset Ω) := by
      rw [hsupp]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
    exact Or.inr (Or.inr ⟨rfl, by aesop, rfl⟩)

@[expose]
public def starThreeCycles
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a b : Ω) :
    Set (alternatingGroup Ω) :=
  {g | ∃ c : Ω, c ≠ a ∧ c ≠ b ∧
    (g : Equiv.Perm Ω) = Equiv.swap a b * Equiv.swap a c}

public theorem starThreeCycles_closure_eq_top
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {a b : Ω} (hab : a ≠ b) :
    Subgroup.closure (starThreeCycles a b) = ⊤ := by
  let H := Subgroup.closure (starThreeCycles a b)
  have hu (c : Ω) (hca : c ≠ a) (hcb : c ≠ b) :
      (⟨Equiv.swap a b * Equiv.swap a c,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          hab (Ne.symm hca) (Ne.symm hcb)).mem_alternatingGroup⟩ :
        alternatingGroup Ω) ∈ H := by
    exact Subgroup.subset_closure ⟨c, hca, hcb, rfl⟩
  have hroot (i j : Ω) (hai : a ≠ i) (haj : a ≠ j) (hij : i ≠ j) :
      (⟨Equiv.swap a i * Equiv.swap a j,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          hai haj hij).mem_alternatingGroup⟩ :
        alternatingGroup Ω) ∈ H := by
    by_cases hib : i = b
    · subst i
      exact hu j (Ne.symm haj) (Ne.symm hij)
    by_cases hjb : j = b
    · subst j
      have hi := H.inv_mem (hu i (Ne.symm hai) hib)
      convert hi using 1
      apply Subtype.ext
      simp
    · have hi := H.inv_mem (hu i (Ne.symm hai) hib)
      have hj := hu j (Ne.symm haj) hjb
      have hijmem := H.mul_mem hi hj
      convert hijmem using 1
      apply Subtype.ext
      simp [mul_assoc]
  have hcycle (x y z : Ω) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (⟨Equiv.swap x y * Equiv.swap x z,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          hxy hxz hyz).mem_alternatingGroup⟩ :
        alternatingGroup Ω) ∈ H := by
    by_cases hxa : x = a
    · subst x
      exact hroot y z hxy hxz hyz
    by_cases hya : y = a
    · subst y
      have h := hroot z x hyz (Ne.symm hxy) hxz.symm
      convert h using 1
      apply Subtype.ext
      exact commonThreeCycle_rotate hxy hxz hyz
    by_cases hza : z = a
    · subst z
      have h := hroot x y hxz.symm hyz.symm hxy
      convert h using 1
      apply Subtype.ext
      exact (commonThreeCycle_rotate hxy hxz hyz).trans
        (commonThreeCycle_rotate hyz hxy.symm hxz.symm)
    · have hxy' := hroot x y (Ne.symm hxa) (Ne.symm hya) hxy
      have hxz' := H.inv_mem (hroot x z (Ne.symm hxa) (Ne.symm hza) hxz)
      have h := H.mul_mem hxy' hxz'
      convert h using 1
      apply Subtype.ext
      change Equiv.swap x y * Equiv.swap x z =
        (Equiv.swap a x * Equiv.swap a y) *
          (Equiv.swap a x * Equiv.swap a z)⁻¹
      rw [mul_inv_rev]
      simp only [Equiv.swap_inv]
      have hconjy :
          Equiv.swap a x * Equiv.swap a y * Equiv.swap a x =
            Equiv.swap x y := by
        simpa [Equiv.swap_comm] using
          (Equiv.swap_mul_swap_mul_swap
            (x := y) (y := a) (z := x) hya hxy.symm)
      have hconjz :
          Equiv.swap a x * Equiv.swap a z * Equiv.swap a x =
            Equiv.swap x z := by
        simpa [Equiv.swap_comm] using
          (Equiv.swap_mul_swap_mul_swap
            (x := z) (y := a) (z := x) hza hxz.symm)
      calc
        Equiv.swap x y * Equiv.swap x z =
            (Equiv.swap a x * Equiv.swap a y * Equiv.swap a x) *
              (Equiv.swap a x * Equiv.swap a z * Equiv.swap a x) := by
                rw [hconjy, hconjz]
        _ = (Equiv.swap a x * Equiv.swap a y) *
              (Equiv.swap a z * Equiv.swap a x) := by
                simp [mul_assoc]
  rw [eq_top_iff]
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨x, hx⟩ := hg.isCycle.nonempty_support
  have hxy : x ≠ (g : Equiv.Perm Ω) x := by
    exact Ne.symm (by simpa [Equiv.Perm.mem_support] using hx)
  have hxz : x ≠ (g : Equiv.Perm Ω) ((g : Equiv.Perm Ω) x) := by
    have := hg.nodup_iff_mem_support.2 hx
    grind
  have hyz :
      (g : Equiv.Perm Ω) x ≠
        (g : Equiv.Perm Ω) ((g : Equiv.Perm Ω) x) := by
    have := hg.nodup_iff_mem_support.2 hx
    grind
  have hrepr := hg.eq_swap_mul_swap_iff_mem_support.2 hx
  have hc := hcycle x ((g : Equiv.Perm Ω) ((g : Equiv.Perm Ω) x))
    ((g : Equiv.Perm Ω) x) hxz hxy hyz.symm
  have heq :
      g = (⟨Equiv.swap x ((g : Equiv.Perm Ω) ((g : Equiv.Perm Ω) x)) *
          Equiv.swap x ((g : Equiv.Perm Ω) x),
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          hxz hxy hyz.symm).mem_alternatingGroup⟩ : alternatingGroup Ω) := by
    apply Subtype.ext
    change (g : Equiv.Perm Ω) =
      Equiv.swap x ((g : Equiv.Perm Ω) ((g : Equiv.Perm Ω) x)) *
        Equiv.swap x ((g : Equiv.Perm Ω) x)
    exact hrepr.trans (adjacentThreeCycle_eq_common hxy hxz hyz)
  rw [heq]
  exact hc

public theorem support_sdiff_subset_support_mul
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f g : Equiv.Perm Ω) :
    f.support \ g.support ⊆ (f * g).support := by
  intro x hx
  rw [Equiv.Perm.mem_support]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Equiv.Perm.notMem_support.mp (Finset.mem_sdiff.mp hx).2]
  exact Equiv.Perm.mem_support.mp (Finset.mem_sdiff.mp hx).1

public theorem threeCycle_product_involution_support_card
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {f g : Equiv.Perm Ω} (hf : f.IsThreeCycle) (hg : g.IsThreeCycle)
    (hpow : (f * g) ^ 2 = 1) (hne : f * g ≠ 1) :
    (f * g).support.card = 4 := by
  have hle : (f * g).support.card ≤ (f.support ∪ g.support).card :=
    Finset.card_le_card (Equiv.Perm.support_mul_le f g)
  have hunion : (f.support ∪ g.support).card ≤ 6 := by
    have hcard := Finset.card_union_add_card_inter f.support g.support
    rw [hf.card_support, hg.card_support] at hcard
    omega
  have hsupport_pos : 0 < (f * g).support.card := by
    exact Nat.pos_of_ne_zero fun hzero ↦
      hne (Equiv.Perm.card_support_eq_zero.mp hzero)
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsupport :
      (f * g).support.card = 2 * (f * g).cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hct]
    simp [Nat.mul_comm]
  have hsign : Equiv.Perm.sign (f * g) = 1 := by
    rw [map_mul, hf.sign, hg.sign, one_mul]
  have heven : Even ((f * g).cycleType.sum + (f * g).cycleType.card) := by
    apply (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hsum :
      (f * g).cycleType.sum = 2 * (f * g).cycleType.card := by
    rw [hct]
    simp [Nat.mul_comm]
  rcases heven with ⟨k, hk⟩
  omega

public theorem threeCycle_product_involution_inter_support_card
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {f g : Equiv.Perm Ω} (hf : f.IsThreeCycle) (hg : g.IsThreeCycle)
    (hpow : (f * g) ^ 2 = 1) (hne : f * g ≠ 1) :
    (f.support ∩ g.support).card = 2 := by
  have hprod := threeCycle_product_involution_support_card hf hg hpow hne
  have hprod_le_union :
      (f * g).support.card ≤ (f.support ∪ g.support).card :=
    Finset.card_le_card (Equiv.Perm.support_mul_le f g)
  have hcard := Finset.card_union_add_card_inter f.support g.support
  rw [hf.card_support, hg.card_support] at hcard
  have hinter_le : (f.support ∩ g.support).card ≤ 2 := by omega
  by_contra hinter_ne
  have hinter_cases :
      (f.support ∩ g.support).card = 0 ∨
        (f.support ∩ g.support).card = 1 := by omega
  rcases hinter_cases with hinter_zero | hinter_one
  · have hdisj_support : Disjoint f.support g.support := by
      rw [Finset.disjoint_iff_inter_eq_empty,
        Finset.card_eq_zero.mp hinter_zero]
    have hdisj : Equiv.Perm.Disjoint f g :=
      Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisj_support
    have hmulcard := hdisj.card_support_mul
    rw [hf.card_support, hg.card_support, hprod] at hmulcard
    omega
  · obtain ⟨t, hinter⟩ := Finset.card_eq_one.mp hinter_one
    have htinter : t ∈ f.support ∩ g.support := by rw [hinter]; simp
    have htf : t ∈ f.support := (Finset.mem_inter.mp htinter).1
    have htg : t ∈ g.support := (Finset.mem_inter.mp htinter).2
    have hgt : g t ≠ t := Equiv.Perm.mem_support.mp htg
    have hgtg : g t ∈ g.support := Equiv.Perm.apply_mem_support.mpr htg
    have hgtf : g t ∉ f.support := by
      intro h
      have hmem : g t ∈ f.support ∩ g.support := Finset.mem_inter.mpr ⟨h, hgtg⟩
      rw [hinter] at hmem
      exact hgt (Finset.mem_singleton.mp hmem)
    have htprod : t ∈ (f * g).support := by
      rw [Equiv.Perm.mem_support]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.Perm.notMem_support.mp hgtf]
      exact hgt
    have hunion_subset : f.support ∪ g.support ⊆ (f * g).support := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxf | hxg
      · by_cases hxg' : x ∈ g.support
        · have hxinter : x ∈ f.support ∩ g.support :=
            Finset.mem_inter.mpr ⟨hxf, hxg'⟩
          rw [hinter] at hxinter
          simpa [Finset.mem_singleton.mp hxinter] using htprod
        · exact support_sdiff_subset_support_mul f g
            (Finset.mem_sdiff.mpr ⟨hxf, hxg'⟩)
      · by_cases hxf' : x ∈ f.support
        · have hxinter : x ∈ f.support ∩ g.support :=
            Finset.mem_inter.mpr ⟨hxf', hxg⟩
          rw [hinter] at hxinter
          simpa [Finset.mem_singleton.mp hxinter] using htprod
        · have hxinv : x ∈ g⁻¹.support \ f⁻¹.support := by
            simpa only [Equiv.Perm.support_inv] using
              (Finset.mem_sdiff.mpr ⟨hxg, hxf'⟩)
          have hxsupport := support_sdiff_subset_support_mul g⁻¹ f⁻¹ hxinv
          simpa only [← mul_inv_rev, Equiv.Perm.support_inv] using hxsupport
    have hunion_le : (f.support ∪ g.support).card ≤ (f * g).support.card :=
      Finset.card_le_card hunion_subset
    omega

public theorem threeCycle_eq_common_or_swap
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {f : Equiv.Perm Ω} (hf : f.IsThreeCycle)
    {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupport : f.support = {a, b, c}) :
    f = Equiv.swap a b * Equiv.swap a c ∨
      f = Equiv.swap b a * Equiv.swap b c := by
  have ha : a ∈ f.support := by rw [hsupport]; simp
  have hfa_mem : f a ∈ ({a, b, c} : Finset Ω) := by
    rw [← hsupport]
    exact Equiv.Perm.apply_mem_support.mpr ha
  have hfaa : f a ≠ a := Equiv.Perm.mem_support.mp ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfa_mem
  rcases hfa_mem with hfa | hfa | hfa
  · exact (hfaa hfa).elim
  · right
    have hnodup := hf.nodup_iff_mem_support.mpr ha
    have hfb_mem : f b ∈ ({a, b, c} : Finset Ω) := by
      rw [← hsupport]
      exact Equiv.Perm.apply_mem_support.mpr (by rw [hsupport]; simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfb_mem
    have hfb : f b = c := by
      simp only [hfa] at hnodup
      grind
    have hrepr := hf.eq_swap_mul_swap_iff_mem_support.mpr ha
    rw [hfa, hfb] at hrepr
    simpa [Equiv.swap_comm a b] using hrepr
  · left
    have hnodup := hf.nodup_iff_mem_support.mpr ha
    have hfc_mem : f c ∈ ({a, b, c} : Finset Ω) := by
      rw [← hsupport]
      exact Equiv.Perm.apply_mem_support.mpr (by rw [hsupport]; simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfc_mem
    have hfc : f c = b := by
      simp only [hfa] at hnodup
      grind
    have hrepr := hf.eq_swap_mul_swap_iff_mem_support.mpr ha
    rw [hfa, hfc] at hrepr
    exact hrepr.trans (adjacentThreeCycle_eq_common hac hab hbc.symm)

public theorem threeCycle_product_involution_common_edge
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {f g : Equiv.Perm Ω} (hf : f.IsThreeCycle) (hg : g.IsThreeCycle)
    (hpow : (f * g) ^ 2 = 1) (hne : f * g ≠ 1) :
    ∃ a b c d : Ω, [a, b, c, d].Nodup ∧
      f = Equiv.swap a b * Equiv.swap a c ∧
      g = Equiv.swap a b * Equiv.swap a d := by
  have hinter_card :=
    threeCycle_product_involution_inter_support_card hf hg hpow hne
  obtain ⟨a, b, hab, hinter⟩ := Finset.card_eq_two.mp hinter_card
  have ha_inter : a ∈ f.support ∩ g.support := by rw [hinter]; simp
  have hb_inter : b ∈ f.support ∩ g.support := by rw [hinter]; simp
  have haf : a ∈ f.support := (Finset.mem_inter.mp ha_inter).1
  have hag : a ∈ g.support := (Finset.mem_inter.mp ha_inter).2
  have hbf : b ∈ f.support := (Finset.mem_inter.mp hb_inter).1
  have hbg : b ∈ g.support := (Finset.mem_inter.mp hb_inter).2
  have hpair_card : ({a, b} : Finset Ω).card = 2 := by simp [hab]
  obtain ⟨c, hc⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (s := ({a, b} : Finset Ω)) (t := f.support) (by
      rw [hpair_card, hf.card_support]
      omega)
  have hcf := (Finset.mem_sdiff.mp hc).1
  have hcpair := (Finset.mem_sdiff.mp hc).2
  obtain ⟨d, hd⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (s := ({a, b} : Finset Ω)) (t := g.support) (by
      rw [hpair_card, hg.card_support]
      omega)
  have hdg := (Finset.mem_sdiff.mp hd).1
  have hdpair := (Finset.mem_sdiff.mp hd).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcpair hdpair
  have hca : c ≠ a := hcpair.1
  have hcb : c ≠ b := hcpair.2
  have hda : d ≠ a := hdpair.1
  have hdb : d ≠ b := hdpair.2
  have hcd : c ≠ d := by
    intro h
    subst d
    have hcinter : c ∈ f.support ∩ g.support :=
      Finset.mem_inter.mpr ⟨hcf, hdg⟩
    rw [hinter] at hcinter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcinter
    exact hcinter.elim hca hcb
  have hfsupport : f.support = {a, b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact haf
      · exact hbf
      · exact hcf
    · rw [hf.card_support]
      simp [hab, hca.symm, hcb.symm]
  have hgsupport : g.support = {a, b, d} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hag
      · exact hbg
      · exact hdg
    · rw [hg.card_support]
      simp [hab, hda.symm, hdb.symm]
  have hprod := threeCycle_product_involution_support_card hf hg hpow hne
  have finish (a b c d : Ω)
      (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
      (hf_eq : f = Equiv.swap a b * Equiv.swap a c)
      (hg_support : g.support = {a, b, d}) :
      ∃ a b c d : Ω, [a, b, c, d].Nodup ∧
        f = Equiv.swap a b * Equiv.swap a c ∧
        g = Equiv.swap a b * Equiv.swap a d := by
    rcases threeCycle_eq_common_or_swap hg hab had hbd hg_support with
      hg_eq | hg_eq
    · exact ⟨a, b, c, d,
        by simp [hab, hac, had, hbc, hbd, hcd],
        hf_eq, hg_eq⟩
    · have hconj :
          Equiv.swap a b * Equiv.swap a c * Equiv.swap a b =
            Equiv.swap b c := by
        simpa [Equiv.swap_comm] using
          (Equiv.swap_mul_swap_mul_swap
            (x := c) (y := a) (z := b) hac.symm hbc.symm)
      have hfg : f * g = Equiv.swap b c * Equiv.swap b d := by
        rw [hf_eq, hg_eq, Equiv.swap_comm b a]
        calc
          (Equiv.swap a b * Equiv.swap a c) *
              (Equiv.swap a b * Equiv.swap b d) =
              (Equiv.swap a b * Equiv.swap a c * Equiv.swap a b) *
                Equiv.swap b d := by simp [mul_assoc]
          _ = Equiv.swap b c * Equiv.swap b d := by rw [hconj]
      have hfg_three : (f * g).IsThreeCycle := by
        rw [hfg]
        exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hbc hbd hcd
      have := hfg_three.card_support
      rw [hprod] at this
      omega
  rcases threeCycle_eq_common_or_swap hf hab hca.symm hcb.symm hfsupport with
    hf_eq | hf_eq
  · exact finish a b c d hab hca.symm hda.symm hcb.symm hdb.symm hcd
      hf_eq hgsupport
  · have hgsupport' : g.support = {b, a, d} := by
      rw [hgsupport]
      ext x
      simp [or_left_comm]
    exact finish b a c d hab.symm hcb.symm hdb.symm hca.symm hda.symm hcd
      hf_eq hgsupport'

public theorem commonThreeCycles_mul_eq_disjointSwaps
    {Ω : Type*} [DecidableEq Ω] {a b c d : Ω}
    (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap a c) *
        (Equiv.swap a b * Equiv.swap a d) =
      Equiv.swap b c * Equiv.swap a d := by
  have hconj :
      Equiv.swap a b * Equiv.swap a c * Equiv.swap a b =
        Equiv.swap b c := by
    simpa [Equiv.swap_comm] using
      (Equiv.swap_mul_swap_mul_swap
        (x := c) (y := a) (z := b) hac.symm hbc.symm)
  calc
    (Equiv.swap a b * Equiv.swap a c) *
        (Equiv.swap a b * Equiv.swap a d) =
        (Equiv.swap a b * Equiv.swap a c * Equiv.swap a b) *
          Equiv.swap a d := by simp [mul_assoc]
    _ = Equiv.swap b c * Equiv.swap a d := by rw [hconj]

public theorem commonThreeCycles_mul_involution
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {a b c d : Ω} (hnod : [a, b, c, d].Nodup) :
    ((Equiv.swap a b * Equiv.swap a c) *
        (Equiv.swap a b * Equiv.swap a d)) ^ 2 = 1 ∧
      (Equiv.swap a b * Equiv.swap a c) *
        (Equiv.swap a b * Equiv.swap a d) ≠ 1 := by
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hbc : b ≠ c := by grind
  have hba : b ≠ a := hab.symm
  have hbd : b ≠ d := by grind
  rw [commonThreeCycles_mul_eq_disjointSwaps hac hbc]
  constructor
  · rw [pow_two]
    have hcomm : Commute (Equiv.swap b c) (Equiv.swap a d) :=
      (Equiv.Perm.disjoint_swap_swap (by grind)).commute
    calc
      (Equiv.swap b c * Equiv.swap a d) *
          (Equiv.swap b c * Equiv.swap a d) =
          Equiv.swap b c * (Equiv.swap a d * Equiv.swap b c) *
            Equiv.swap a d := by simp only [mul_assoc]
      _ = Equiv.swap b c * (Equiv.swap b c * Equiv.swap a d) *
            Equiv.swap a d := by rw [hcomm.eq.symm]
      _ = (Equiv.swap b c * Equiv.swap b c) *
            (Equiv.swap a d * Equiv.swap a d) := by simp only [mul_assoc]
      _ = 1 := by simp
  · intro h
    have heval := congrArg (fun q : Equiv.Perm Ω ↦ q b) h
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hba hbd,
      Equiv.swap_apply_left] at heval
    have hcb : c = b := by
      simpa using heval
    exact hbc hcb.symm

public theorem threeCycle_pair_common_edge_rigid
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {a b c d : Ω} (hnod : [a, b, c, d].Nodup)
    {h : Equiv.Perm Ω} (hh : h.IsThreeCycle)
    (hpowc : ((Equiv.swap a b * Equiv.swap a c) * h) ^ 2 = 1)
    (hnec : (Equiv.swap a b * Equiv.swap a c) * h ≠ 1)
    (hpowd : ((Equiv.swap a b * Equiv.swap a d) * h) ^ 2 = 1)
    (hned : (Equiv.swap a b * Equiv.swap a d) * h ≠ 1) :
    ∃ e : Ω, e ≠ a ∧ e ≠ b ∧
      h = Equiv.swap a b * Equiv.swap a e := by
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have had : a ≠ d := by grind
  have hbc : b ≠ c := by grind
  have hbd : b ≠ d := by grind
  have hcd : c ≠ d := by grind
  have hfc : (Equiv.swap a b * Equiv.swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hfd : (Equiv.swap a b * Equiv.swap a d).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab had hbd
  obtain ⟨x, y, z, e, hnodc, hfc_eq, hh_eq⟩ :=
    threeCycle_product_involution_common_edge hfc hh hpowc hnec
  rcases commonThreeCycle_eq_cyclic hab hac hbc
    (by grind) (by grind) (by grind) hfc_eq with hcase | hcase | hcase
  · rcases hcase with ⟨hx, hy, hz⟩
    subst x
    subst y
    subst z
    exact ⟨e, by grind, by grind, hh_eq⟩
  · rcases hcase with ⟨hx, hy, hz⟩
    subst x
    subst y
    subst z
    obtain ⟨x, y, z, e', hnodd, hfd_eq, hh_eq'⟩ :=
      threeCycle_product_involution_common_edge hfd hh hpowd hned
    rcases commonThreeCycle_eq_cyclic hab had hbd
      (by grind) (by grind) (by grind) hfd_eq with hdcase | hdcase | hdcase
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := b) (b := c) (c := e) (x := a) (y := b) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := b) (b := c) (c := e) (x := b) (y := d) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := b) (b := c) (c := e) (x := d) (y := a) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind
  · rcases hcase with ⟨hx, hy, hz⟩
    subst x
    subst y
    subst z
    obtain ⟨x, y, z, e', hnodd, hfd_eq, hh_eq'⟩ :=
      threeCycle_product_involution_common_edge hfd hh hpowd hned
    rcases commonThreeCycle_eq_cyclic hab had hbd
      (by grind) (by grind) (by grind) hfd_eq with hdcase | hdcase | hdcase
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := c) (b := a) (c := e) (x := a) (y := b) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := c) (b := a) (c := e) (x := b) (y := d) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind
    · rcases hdcase with ⟨hx, hy, hz⟩
      subst x
      subst y
      subst z
      have hcyc := commonThreeCycle_eq_cyclic
        (a := c) (b := a) (c := e) (x := d) (y := a) (z := e')
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
        (hh_eq.symm.trans hh_eq')
      rcases hcyc with h | h | h <;> grind

public theorem automorphism_eq_conjNormal_of_maps_threeCycles
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h4 : 4 ≤ Fintype.card Ω) (φ : MulAut (alternatingGroup Ω))
    (hφ : ∀ g : alternatingGroup Ω,
      (g.1 : Equiv.Perm Ω).IsThreeCycle →
        ((φ g).1 : Equiv.Perm Ω).IsThreeCycle) :
    ∃ p : Equiv.Perm Ω, φ = MulAut.conjNormal p := by
  have hcard : 3 < (Finset.univ : Finset Ω).card := by
    simpa only [Finset.card_univ]
  obtain ⟨a, b, c, d, -, -, -, -, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp hcard
  let P := {e : Ω // e ≠ a ∧ e ≠ b}
  let __ch5_Automorphism_u : P → alternatingGroup Ω := fun e ↦
    ⟨Equiv.swap a b * Equiv.swap a e.1,
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same
        hab e.2.1.symm e.2.2.symm).mem_alternatingGroup⟩
  let cP : P := ⟨c, hac.symm, hbc.symm⟩
  let dP : P := ⟨d, had.symm, hbd.symm⟩
  have hu_three (e : P) : (__ch5_Automorphism_u e).1.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      hab e.2.1.symm e.2.2.symm
  have imageRelation (x y : P)
      (hrel : (((__ch5_Automorphism_u x).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u y).1) ^ 2 = 1 ∧
        ((__ch5_Automorphism_u x).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u y).1 ≠ 1) :
      ((((φ (__ch5_Automorphism_u x)).1 : Equiv.Perm Ω) * (φ (__ch5_Automorphism_u y)).1) ^ 2 = 1 ∧
        ((φ (__ch5_Automorphism_u x)).1 : Equiv.Perm Ω) * (φ (__ch5_Automorphism_u y)).1 ≠ 1) := by
    constructor
    · have hsub : (__ch5_Automorphism_u x * __ch5_Automorphism_u y) ^ 2 = 1 := by
        apply Subtype.ext
        exact hrel.1
      have himg := congrArg φ hsub
      exact congrArg Subtype.val (by simpa only [map_pow, map_mul, map_one] using himg)
    · intro himg
      have hsub : φ (__ch5_Automorphism_u x) * φ (__ch5_Automorphism_u y) = 1 := by
        apply Subtype.ext
        exact himg
      have hpre : __ch5_Automorphism_u x * __ch5_Automorphism_u y = 1 := by
        apply φ.injective
        simpa only [map_mul, map_one] using hsub
      exact hrel.2 (congrArg Subtype.val hpre)
  have hrel_cd :
      (((__ch5_Automorphism_u cP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u dP).1) ^ 2 = 1 ∧
        ((__ch5_Automorphism_u cP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u dP).1 ≠ 1 := by
    simpa only [__ch5_Automorphism_u, cP, dP] using
      (commonThreeCycles_mul_involution
        (Ω := Ω) (a := a) (b := b) (c := c) (d := d) (by
          simp [hab, hac, had, hbc, hbd, hcd]))
  have himg_cd := imageRelation cP dP hrel_cd
  obtain ⟨A, B, C, D, hABCD, huc, hud⟩ :=
    threeCycle_product_involution_common_edge
      (hφ (__ch5_Automorphism_u cP) (hu_three cP)) (hφ (__ch5_Automorphism_u dP) (hu_three dP))
      himg_cd.1 himg_cd.2
  have hstar (e : P) :
      ∃ E : Ω, E ≠ A ∧ E ≠ B ∧
        ((φ (__ch5_Automorphism_u e)).1 : Equiv.Perm Ω) =
          Equiv.swap A B * Equiv.swap A E := by
    by_cases hec : e.1 = c
    · have he : e = cP := Subtype.ext hec
      subst e
      exact ⟨C, by grind, by grind, huc⟩
    by_cases hed : e.1 = d
    · have he : e = dP := Subtype.ext hed
      subst e
      exact ⟨D, by grind, by grind, hud⟩
    have hrel_ce :
        (((__ch5_Automorphism_u cP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u e).1) ^ 2 = 1 ∧
          ((__ch5_Automorphism_u cP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u e).1 ≠ 1 := by
      simpa only [__ch5_Automorphism_u, cP] using
        (commonThreeCycles_mul_involution
          (Ω := Ω) (a := a) (b := b) (c := c) (d := e.1) (by
            simp [hab, hac, hbc, e.2.1.symm, e.2.2.symm,
              Ne.symm hec]))
    have hrel_de :
        (((__ch5_Automorphism_u dP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u e).1) ^ 2 = 1 ∧
          ((__ch5_Automorphism_u dP).1 : Equiv.Perm Ω) * (__ch5_Automorphism_u e).1 ≠ 1 := by
      simpa only [__ch5_Automorphism_u, dP] using
        (commonThreeCycles_mul_involution
          (Ω := Ω) (a := a) (b := b) (c := d) (d := e.1) (by
            simp [hab, had, hbd, e.2.1.symm, e.2.2.symm,
              Ne.symm hed]))
    have himg_ce := imageRelation cP e hrel_ce
    have himg_de := imageRelation dP e hrel_de
    apply threeCycle_pair_common_edge_rigid hABCD (hφ (__ch5_Automorphism_u e) (hu_three e))
    · rw [← huc]
      exact himg_ce.1
    · rw [← huc]
      exact himg_ce.2
    · rw [← hud]
      exact himg_de.1
    · rw [← hud]
      exact himg_de.2
  let E : P → Ω := fun e ↦ Classical.choose (hstar e)
  have hEneA (e : P) : E e ≠ A := (Classical.choose_spec (hstar e)).1
  have hEneB (e : P) : E e ≠ B := (Classical.choose_spec (hstar e)).2.1
  have hEeq (e : P) :
      ((φ (__ch5_Automorphism_u e)).1 : Equiv.Perm Ω) =
        Equiv.swap A B * Equiv.swap A (E e) :=
    (Classical.choose_spec (hstar e)).2.2
  have hEinj : Function.Injective E := by
    intro e f hef
    have hφeq : φ (__ch5_Automorphism_u e) = φ (__ch5_Automorphism_u f) := by
      apply Subtype.ext
      rw [hEeq e, hEeq f, hef]
    have hueq : __ch5_Automorphism_u e = __ch5_Automorphism_u f := φ.injective hφeq
    apply Subtype.ext
    have heval := congrArg
      (fun g : alternatingGroup Ω ↦ (g.1 : Equiv.Perm Ω) a) hueq
    simpa only [__ch5_Automorphism_u,
      commonThreeCycle_apply_first hab e.2.1.symm e.2.2.symm,
      commonThreeCycle_apply_first hab f.2.1.symm f.2.2.symm] using heval
  let pMap : Ω → Ω := fun x ↦
    if hxa : x = a then A
    else if hxb : x = b then B
    else E ⟨x, hxa, hxb⟩
  have hpMap_a : pMap a = A := by simp [pMap]
  have hpMap_b : pMap b = B := by simp [pMap, hab.symm]
  have hpMap_other (e : P) : pMap e.1 = E e := by
    simp [pMap, e.2.1, e.2.2]
  have hAB : A ≠ B := by grind
  have hpMap_inj : Function.Injective pMap := by
    intro x y hxy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      by_cases hyb : y = b
      · subst y
        rw [hpMap_a, hpMap_b] at hxy
        exact (hAB hxy).elim
      · have hcontra : A = E (⟨y, hya, hyb⟩ : P) := by
          rw [hpMap_a, hpMap_other (⟨y, hya, hyb⟩ : P)] at hxy
          exact hxy
        exact (hEneA (⟨y, hya, hyb⟩ : P) hcontra.symm).elim
    by_cases hxb : x = b
    · subst x
      by_cases hya : y = a
      · subst y
        rw [hpMap_b, hpMap_a] at hxy
        exact (hAB hxy.symm).elim
      by_cases hyb : y = b
      · exact hyb.symm
      · have hcontra : B = E (⟨y, hya, hyb⟩ : P) := by
          rw [hpMap_b, hpMap_other (⟨y, hya, hyb⟩ : P)] at hxy
          exact hxy
        exact (hEneB (⟨y, hya, hyb⟩ : P) hcontra.symm).elim
    by_cases hya : y = a
    · subst y
      have hcontra : E (⟨x, hxa, hxb⟩ : P) = A := by
        rw [hpMap_other (⟨x, hxa, hxb⟩ : P), hpMap_a] at hxy
        exact hxy
      exact (hEneA (⟨x, hxa, hxb⟩ : P) hcontra).elim
    by_cases hyb : y = b
    · subst y
      have hcontra : E (⟨x, hxa, hxb⟩ : P) = B := by
        rw [hpMap_other (⟨x, hxa, hxb⟩ : P), hpMap_b] at hxy
        exact hxy
      exact (hEneB (⟨x, hxa, hxb⟩ : P) hcontra).elim
    have hEf : E (⟨x, hxa, hxb⟩ : P) = E (⟨y, hya, hyb⟩ : P) := by
      rw [hpMap_other (⟨x, hxa, hxb⟩ : P),
        hpMap_other (⟨y, hya, hyb⟩ : P)] at hxy
      exact hxy
    exact congrArg Subtype.val (hEinj hEf)
  let p : Equiv.Perm Ω := Equiv.ofBijective pMap
    ⟨hpMap_inj, Finite.injective_iff_surjective.mp hpMap_inj⟩
  have hpa : p a = A := hpMap_a
  have hpb : p b = B := hpMap_b
  have hpe (e : P) : p e.1 = E e := hpMap_other e
  have hconjSwap (x y : Ω) :
      p * Equiv.swap x y * p⁻¹ = Equiv.swap (p x) (p y) := by
    change (p.symm.trans (Equiv.swap x y)).trans p =
      Equiv.swap (p x) (p y)
    exact Equiv.symm_trans_swap_trans x y p
  refine ⟨p, ?_⟩
  apply DFunLike.ext _ _
  intro g
  have hg : g ∈ Subgroup.closure (starThreeCycles a b) := by
    rw [starThreeCycles_closure_eq_top hab]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases hg with ⟨e, hea, heb, hge⟩
      let eP : P := ⟨e, hea, heb⟩
      have hgu : g = __ch5_Automorphism_u eP := by
        apply Subtype.ext
        exact hge
      subst g
      apply Subtype.ext
      rw [hEeq eP, MulAut.conjNormal_apply]
      change Equiv.swap A B * Equiv.swap A (E eP) =
        p * (Equiv.swap a b * Equiv.swap a e) * p⁻¹
      symm
      calc
        p * (Equiv.swap a b * Equiv.swap a e) * p⁻¹ =
            (p * Equiv.swap a b * p⁻¹) *
              (p * Equiv.swap a e * p⁻¹) := by group
        _ = Equiv.swap (p a) (p b) * Equiv.swap (p a) (p e) := by
          rw [hconjSwap, hconjSwap]
        _ = Equiv.swap A B * Equiv.swap A (E eP) := by
          rw [hpa, hpb, hpe eP]
  | one => simp
  | mul x y hx hy ihx ihy =>
      simpa only [map_mul] using congrArg₂ (· * ·) ihx ihy
  | inv x hx ih =>
      rw [map_inv, map_inv, ih]

public theorem alternatingConjHom_injective
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h4 : 4 ≤ Fintype.card Ω) :
    Function.Injective
      (MulAut.conjNormal :
        Equiv.Perm Ω →* MulAut (alternatingGroup Ω)) := by
  intro p q hpq
  apply Equiv.ext
  intro a
  let s : Finset Ω := Finset.univ.erase a
  have hs : 2 < s.card := by
    simp only [s, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ]
    omega
  obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ :=
    Finset.two_lt_card_iff.mp hs
  have hab : a ≠ b := Ne.symm (by simpa [s] using hb)
  have hac : a ≠ c := Ne.symm (by simpa [s] using hc)
  have had : a ≠ d := Ne.symm (by simpa [s] using hd)
  let g₁ : Equiv.Perm Ω := Equiv.swap a b * Equiv.swap a c
  let g₂ : Equiv.Perm Ω := Equiv.swap a b * Equiv.swap a d
  let g₃ : Equiv.Perm Ω := Equiv.swap a c * Equiv.swap a d
  have hg₁ : g₁.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hg₂ : g₂.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab had hbd
  have hg₃ : g₃.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hac had hcd
  have hcomm (g : alternatingGroup Ω) :
      Commute (q⁻¹ * p) (g : Equiv.Perm Ω) := by
    have hpg :
        (MulAut.conjNormal p) g = (MulAut.conjNormal q) g :=
      DFunLike.congr_fun hpq g
    have hval := congrArg Subtype.val hpg
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply] at hval
    change q⁻¹ * p * (g : Equiv.Perm Ω) =
      (g : Equiv.Perm Ω) * (q⁻¹ * p)
    calc
      q⁻¹ * p * (g : Equiv.Perm Ω) =
          q⁻¹ * (p * (g : Equiv.Perm Ω) * p⁻¹) * p := by group
      _ = q⁻¹ * (q * (g : Equiv.Perm Ω) * q⁻¹) * p := by rw [hval]
      _ = (g : Equiv.Perm Ω) * (q⁻¹ * p) := by group
  have hs₁ : (Equiv.swap a b * Equiv.swap a c).support = {a, b, c} := by
    rw [Equiv.swap_comm a b]
    calc
      (Equiv.swap b a * Equiv.swap a c).support = {b, a, c} :=
        Equiv.Perm.support_swap_mul_swap
          (by simp [hac, hbc, Ne.symm hab])
      _ = {a, b, c} := by ext; simp [or_left_comm]
  have hs₂ : (Equiv.swap a b * Equiv.swap a d).support = {a, b, d} := by
    rw [Equiv.swap_comm a b]
    calc
      (Equiv.swap b a * Equiv.swap a d).support = {b, a, d} :=
        Equiv.Perm.support_swap_mul_swap
          (by simp [had, hbd, Ne.symm hab])
      _ = {a, b, d} := by ext; simp [or_left_comm]
  have hs₃ : (Equiv.swap a c * Equiv.swap a d).support = {a, c, d} := by
    rw [Equiv.swap_comm a c]
    calc
      (Equiv.swap c a * Equiv.swap a d).support = {c, a, d} :=
        Equiv.Perm.support_swap_mul_swap
          (by simp [had, hcd, Ne.symm hac])
      _ = {a, c, d} := by ext; simp [or_left_comm]
  have hmem (g : Equiv.Perm Ω) (hg : g.IsThreeCycle)
      (ha : a ∈ g.support) :
      (q⁻¹ * p) a ∈ g.support :=
    (Equiv.Perm.mem_support_iff_of_commute
      (hcomm ⟨g, hg.mem_alternatingGroup⟩) a).2 ha
  have ha₁ : a ∈ g₁.support := by simp [g₁, hs₁]
  have ha₂ : a ∈ g₂.support := by simp [g₂, hs₂]
  have ha₃ : a ∈ g₃.support := by simp [g₃, hs₃]
  have hr₁ := hmem g₁ hg₁ ha₁
  have hr₂ := hmem g₂ hg₂ ha₂
  have hr₃ := hmem g₃ hg₃ ha₃
  simp only [g₁, g₂, g₃] at hr₁ hr₂ hr₃
  rw [hs₁] at hr₁
  rw [hs₂] at hr₂
  rw [hs₃] at hr₃
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr₁ hr₂ hr₃
  have hra : (q⁻¹ * p) a = a := by aesop
  simpa using congrArg (fun z ↦ q z) hra

public theorem multipleThreeCycle_centralizer_lt
    {n k : ℕ} (hn : 7 ≤ n) (hk : 2 ≤ k) (hkn : 3 * k ≤ n) :
    2 * (Nat.factorial (n - 3 * k) * 3 ^ k * Nat.factorial k) <
      3 * Nat.factorial (n - 3) := by
  let s := n - 3 * k
  have hns : n = s + 3 * k := by
    dsimp only [s]
    omega
  have hspos_of_k2 (hk2 : k = 2) : 1 ≤ s := by
    subst k
    omega
  have hcore :
      2 * 3 ^ (k - 1) * Nat.factorial k * Nat.factorial s <
        Nat.factorial (s + 3 * k - 3) := by
    rcases hk.eq_or_lt with hk2 | hk3
    · subst k
      have hs : 1 ≤ s := hspos_of_k2 rfl
      have hcoeff : 12 < (s + 1) * (s + 2) * (s + 3) := by
        have hprod : 24 ≤ (s + 1) * (s + 2) * (s + 3) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul (show 2 ≤ s + 1 by omega)
              (show 3 ≤ s + 2 by omega))
            (show 4 ≤ s + 3 by omega)
        omega
      have hmul := Nat.mul_lt_mul_of_pos_right hcoeff (Nat.factorial_pos s)
      calc
        2 * 3 ^ (2 - 1) * Nat.factorial 2 * Nat.factorial s =
            12 * Nat.factorial s := by norm_num [Nat.factorial]
        _ < ((s + 1) * (s + 2) * (s + 3)) * Nat.factorial s := hmul
        _ = Nat.factorial (s + 3 * 2 - 3) := by
          rw [show s + 3 * 2 - 3 = s + 3 by omega,
            show s + 3 = (s + 2) + 1 by omega,
            show s + 2 = (s + 1) + 1 by omega,
            show s + 1 = s + 1 by rfl,
            Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
          ring
    · obtain ⟨m, hkm⟩ := Nat.exists_eq_add_of_le (show 3 ≤ k by omega)
      rw [hkm, show 3 + m = m + 3 by omega]
      have h34 : 3 ^ (m + 2) ≤ 4 ^ (m + 2) := by
        gcongr
        norm_num
      have hfirst : 2 * 3 ^ (m + 2) < 4 ^ (m + 3) := by
        calc
          2 * 3 ^ (m + 2) ≤ 2 * 4 ^ (m + 2) :=
            Nat.mul_le_mul_left 2 h34
          _ < 4 * 4 ^ (m + 2) :=
            Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
          _ = 4 ^ (m + 3) := by
            rw [show m + 3 = (m + 2) + 1 by omega, pow_succ]
            ring
      have hpow_right : 4 ^ (m + 3) ≤ 4 ^ (2 * m + 3) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hbase : 2 * 3 ^ (m + 2) < (m + 4) ^ (2 * m + 3) :=
        hfirst.trans_le (hpow_right.trans (by
          gcongr
          omega))
      have hmul := Nat.mul_lt_mul_of_pos_left hbase
        (Nat.factorial_pos (m + 3))
      have hfac := Nat.factorial_mul_pow_le_factorial
        (m := m + 3) (n := 2 * m + 3)
      calc
        2 * 3 ^ (m + 3 - 1) * Nat.factorial (m + 3) * Nat.factorial s =
            Nat.factorial s *
              (Nat.factorial (m + 3) * (2 * 3 ^ (m + 2))) := by
              rw [show m + 3 - 1 = m + 2 by omega]
              ring
        _ < Nat.factorial s *
            (Nat.factorial (m + 3) * (m + 4) ^ (2 * m + 3)) :=
          Nat.mul_lt_mul_of_pos_left (by simpa [Nat.mul_comm] using hmul)
            (Nat.factorial_pos s)
        _ ≤ Nat.factorial s * Nat.factorial (3 * (m + 3) - 3) := by
          apply Nat.mul_le_mul_left
          simpa only [show m + 3 + 1 = m + 4 by omega,
            show m + 3 + (2 * m + 3) = 3 * (m + 3) - 3 by omega]
            using hfac
        _ ≤ Nat.factorial (s + 3 * (m + 3) - 3) := by
          have hdiv := Nat.factorial_mul_factorial_dvd_factorial_add
            s (3 * (m + 3) - 3)
          rw [show s + 3 * (m + 3) - 3 =
            s + (3 * (m + 3) - 3) by omega]
          exact Nat.le_of_dvd (Nat.factorial_pos _) hdiv
  calc
    2 * (Nat.factorial (n - 3 * k) * 3 ^ k * Nat.factorial k) =
        3 * (2 * 3 ^ (k - 1) * Nat.factorial k * Nat.factorial s) := by
      rw [hns]
      have hkpos : 0 < k := by omega
      rw [show 3 ^ k = 3 ^ (k - 1) * 3 by
        nth_rewrite 1 [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
        rw [pow_succ]]
      rw [Nat.add_sub_cancel_right]
      ring
    _ < 3 * Nat.factorial (s + 3 * k - 3) :=
      Nat.mul_lt_mul_of_pos_left hcore (by norm_num)
    _ = 3 * Nat.factorial (n - 3) := by rw [hns]

public def centralizerMulEquivOfMulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃*
      Subgroup.centralizer ({e g} : Set H) where
  toFun x := ⟨e x.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp x.2)⟩
  invFun y := ⟨e.symm y.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul, MulEquiv.symm_apply_apply] using
      congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp y.2)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp
  map_mul' _ _ := by apply Subtype.ext; exact map_mul e _ _

public noncomputable def alternatingCentralizerMulEquivSignKer
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (g : alternatingGroup Ω) :
    Subgroup.centralizer ({g} : Set (alternatingGroup Ω)) ≃*
      (Equiv.Perm.sign.comp
        (Subgroup.subtype (Subgroup.centralizer
          ({g.1} : Set (Equiv.Perm Ω))))).ker where
  toFun x := ⟨⟨x.1.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2
    exact congrArg Subtype.val h⟩, by
      change Equiv.Perm.sign x.1.1 = 1
      exact Equiv.Perm.mem_alternatingGroup.mp x.1.2⟩
  invFun y := ⟨⟨y.1.1,
    Equiv.Perm.mem_alternatingGroup.mpr (by exact y.2)⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp y.1.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

public theorem twice_natCard_centralizer_alternating_of_threeCycle
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (g : alternatingGroup Ω) (hg : (g.1 : Equiv.Perm Ω).IsThreeCycle)
    (h5 : 5 ≤ Fintype.card Ω) :
    2 * Nat.card (Subgroup.centralizer
      ({g} : Set (alternatingGroup Ω))) =
        3 * Nat.factorial (Fintype.card Ω - 3) := by
  let C := Subgroup.centralizer ({g.1} : Set (Equiv.Perm Ω))
  let f : C →* ℤˣ := Equiv.Perm.sign.comp (Subgroup.subtype C)
  let fixedComplement : Finset Ω := Finset.univ \ g.1.support
  have hfixed_card : fixedComplement.card = Fintype.card Ω - 3 := by
    dsimp only [fixedComplement]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hg.card_support]
  have hfixed_two : 1 < fixedComplement.card := by
    rw [hfixed_card]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hfixed_two
  have hxfix : g.1 x = x := Equiv.Perm.notMem_support.mp
    (by simpa [fixedComplement] using hx)
  have hyfix : g.1 y = y := Equiv.Perm.notMem_support.mp
    (by simpa [fixedComplement] using hy)
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap x y) g.1 := by
    intro z
    by_cases hzx : z = x
    · subst z
      exact Or.inr hxfix
    by_cases hzy : z = y
    · subst z
      exact Or.inr hyfix
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hzx hzy)
  let t : C := ⟨Equiv.swap x y, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hdisj.commute⟩
  have hft : f t = -1 := by
    exact Equiv.Perm.sign_swap hxy
  have hrange : f.range = ⊤ := by
    ext z
    simp only [Subgroup.mem_top, iff_true]
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨t, hft⟩
  have hker := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange] at hker
  have htop : Nat.card (↥(⊤ : Subgroup ℤˣ)) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hker' : Nat.card f.ker * 2 = Nat.card C := by
    rw [htop] at hker
    exact hker
  have hcentralizer :
      Nat.card C = Nat.factorial (Fintype.card Ω - 3) * 3 := by
    dsimp only [C]
    rw [Equiv.Perm.nat_card_centralizer, hg.cycleType]
    norm_num
  have hequiv := Nat.card_congr
    (alternatingCentralizerMulEquivSignKer g).toEquiv
  rw [hequiv, Nat.mul_comm 2, hker', hcentralizer]
  ring

public theorem natCard_centralizer_of_cycleType_replicate_three
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (g : Equiv.Perm Ω) (k : ℕ) (hk : 0 < k)
    (hg : g.cycleType = Multiset.replicate k 3) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm Ω))) =
      Nat.factorial (Fintype.card Ω - 3 * k) * 3 ^ k *
        Nat.factorial k := by
  rw [Equiv.Perm.nat_card_centralizer, hg]
  simp [Multiset.sum_replicate, Multiset.prod_replicate, hk.ne', Nat.mul_comm]

public theorem automorphism_maps_threeCycles
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h7 : 7 ≤ Fintype.card Ω) (φ : MulAut (alternatingGroup Ω))
    (g : alternatingGroup Ω) (hg : (g.1 : Equiv.Perm Ω).IsThreeCycle) :
    (((φ g).1 : Equiv.Perm Ω).IsThreeCycle) := by
  let h := φ g
  have horder : orderOf (h.1 : Equiv.Perm Ω) = 3 := by
    calc
      orderOf (h.1 : Equiv.Perm Ω) = orderOf h := Subgroup.orderOf_coe h
      _ = orderOf g := φ.orderOf_eq g
      _ = orderOf (g.1 : Equiv.Perm Ω) := (Subgroup.orderOf_coe g).symm
      _ = 3 := hg.orderOf
  have hprime : (orderOf (h.1 : Equiv.Perm Ω)).Prime := by
    rw [horder]
    exact Nat.prime_three
  obtain ⟨m, hct⟩ := Equiv.Perm.cycleType_prime_order hprime
  let k := m + 1
  have hkpos : 0 < k := by simp [k]
  have hct3 : (h.1 : Equiv.Perm Ω).cycleType = Multiset.replicate k 3 := by
    simpa only [k, horder] using hct
  by_cases hk1 : k = 1
  · change (h.1 : Equiv.Perm Ω).cycleType = {3}
    simpa [hk1] using hct3
  have hk2 : 2 ≤ k := by omega
  have hkn : 3 * k ≤ Fintype.card Ω := by
    have hsupp : (h.1 : Equiv.Perm Ω).support.card ≤ Fintype.card Ω :=
      Finset.card_le_univ _
    rw [← Equiv.Perm.sum_cycleType, hct3,
      Multiset.sum_replicate, nsmul_eq_mul] at hsupp
    simpa [Nat.mul_comm] using hsupp
  let CAh := Subgroup.centralizer ({h} : Set (alternatingGroup Ω))
  let CPh := Subgroup.centralizer ({h.1} : Set (Equiv.Perm Ω))
  let inc : CAh → CPh := fun x ↦ ⟨x.1.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)⟩
  have hinc : Function.Injective inc := by
    intro x y hxy
    have hperm : (inc x).1 = (inc y).1 :=
      congrArg (fun z : CPh ↦ z.1) hxy
    have halt : x.1 = y.1 := Subtype.ext hperm
    exact Subtype.ext halt
  have hcard_le : Nat.card CAh ≤ Nat.card CPh :=
    Nat.card_le_card_of_injective inc hinc
  have hcard_perm : Nat.card CPh =
      Nat.factorial (Fintype.card Ω - 3 * k) * 3 ^ k *
        Nat.factorial k := by
    exact natCard_centralizer_of_cycleType_replicate_three h.1 k hkpos hct3
  have hcard_aut :
      Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup Ω))) =
        Nat.card CAh := by
    exact Nat.card_congr (centralizerMulEquivOfMulEquiv φ g).toEquiv
  have hcard_three := twice_natCard_centralizer_alternating_of_threeCycle
    g hg (by omega)
  have hupper : 2 * Nat.card CAh ≤ 2 * Nat.card CPh :=
    Nat.mul_le_mul_left 2 hcard_le
  have hstrict := multipleThreeCycle_centralizer_lt h7 hk2 hkn
  rw [← hcard_perm] at hstrict
  rw [← hcard_aut] at hupper
  omega

/-- Theorem 5.2.1(a): outside degree six, every automorphism of an alternating
group of degree greater than five is induced by a point permutation. -/
@[expose]
public noncomputable def theorem_5_2_1_a
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 < Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6) :
    MulAut (alternatingGroup Ω) ≃* Equiv.Perm Ω := by
  have h7 : 7 ≤ Fintype.card Ω := by omega
  have h4 : 4 ≤ Fintype.card Ω := by omega
  let c : Equiv.Perm Ω →* MulAut (alternatingGroup Ω) :=
    MulAut.conjNormal
  have hc_surjective : Function.Surjective c := by
    intro φ
    obtain ⟨p, hp⟩ := automorphism_eq_conjNormal_of_maps_threeCycles h4 φ
      (fun g hg ↦ automorphism_maps_threeCycles h7 φ g hg)
    exact ⟨p, hp.symm⟩
  exact (MulEquiv.ofBijective c
    ⟨alternatingConjHom_injective h4, hc_surjective⟩).symm

public abbrev PentadData := Finset (Finset (Finset (Fin 6)))

@[reducible, expose]
public def pentadAt : Fin 6 → PentadData
  | 0 => { { {0, 1}, {2, 4}, {3, 5} }, { {0, 2}, {1, 5}, {3, 4} },
      { {0, 3}, {1, 2}, {4, 5} }, { {0, 4}, {1, 3}, {2, 5} },
      { {0, 5}, {1, 4}, {2, 3} } }
  | 1 => { { {0, 1}, {2, 5}, {3, 4} }, { {0, 2}, {1, 4}, {3, 5} },
      { {0, 3}, {1, 2}, {4, 5} }, { {0, 4}, {1, 5}, {2, 3} },
      { {0, 5}, {1, 3}, {2, 4} } }
  | 2 => { { {0, 1}, {2, 3}, {4, 5} }, { {0, 2}, {1, 5}, {3, 4} },
      { {0, 3}, {1, 4}, {2, 5} }, { {0, 4}, {1, 2}, {3, 5} },
      { {0, 5}, {1, 3}, {2, 4} } }
  | 3 => { { {0, 1}, {2, 5}, {3, 4} }, { {0, 2}, {1, 3}, {4, 5} },
      { {0, 3}, {1, 5}, {2, 4} }, { {0, 4}, {1, 2}, {3, 5} },
      { {0, 5}, {1, 4}, {2, 3} } }
  | 4 => { { {0, 1}, {2, 3}, {4, 5} }, { {0, 2}, {1, 4}, {3, 5} },
      { {0, 3}, {1, 5}, {2, 4} }, { {0, 4}, {1, 3}, {2, 5} },
      { {0, 5}, {1, 2}, {3, 4} } }
  | 5 => { { {0, 1}, {2, 4}, {3, 5} }, { {0, 2}, {1, 3}, {4, 5} },
      { {0, 3}, {1, 4}, {2, 5} }, { {0, 4}, {1, 5}, {2, 3} },
      { {0, 5}, {1, 2}, {3, 4} } }

@[reducible, expose]
public def pentadEquiv (g : Equiv.Perm (Fin 6)) : PentadData ≃ PentadData :=
  g.finsetCongr.finsetCongr.finsetCongr

public theorem pentadEquiv_one : pentadEquiv 1 = Equiv.refl PentadData := by
  change (Equiv.refl (Fin 6)).finsetCongr.finsetCongr.finsetCongr = _
  simp only [Equiv.finsetCongr_refl]

public theorem pentadEquiv_mul (g h : Equiv.Perm (Fin 6)) :
    pentadEquiv (g * h) = (pentadEquiv h).trans (pentadEquiv g) := by
  have h₁ := Equiv.finsetCongr_trans h g
  have h₂ := Equiv.finsetCongr_trans h.finsetCongr g.finsetCongr
  have h₃ := Equiv.finsetCongr_trans
    h.finsetCongr.finsetCongr g.finsetCongr.finsetCongr
  rw [h₂, h₁] at h₃
  change (h.trans g).finsetCongr.finsetCongr.finsetCongr = _
  exact h₃.symm

@[reducible, expose]
public def pentadMap (g : Equiv.Perm (Fin 6)) (P : PentadData) : PentadData :=
  pentadEquiv g P

public theorem pentadMap_one (P : PentadData) : pentadMap 1 P = P := by
  rw [pentadMap, pentadEquiv_one]
  rfl

public theorem pentadMap_mul (g h : Equiv.Perm (Fin 6)) (P : PentadData) :
    pentadMap (g * h) P = pentadMap g (pentadMap h P) := by
  rw [pentadMap, pentadEquiv_mul]
  rfl

@[reducible]
public instance : MulAction (Equiv.Perm (Fin 6)) PentadData where
  smul := pentadMap
  one_smul := pentadMap_one
  mul_smul := pentadMap_mul

@[reducible]
public def pentadCollectionEquiv (g : Equiv.Perm (Fin 6)) :
    Finset PentadData ≃ Finset PentadData :=
  (pentadEquiv g).finsetCongr

public theorem pentadCollectionEquiv_one :
    pentadCollectionEquiv 1 = Equiv.refl (Finset PentadData) := by
  rw [pentadCollectionEquiv, pentadEquiv_one]
  exact Equiv.finsetCongr_refl

public theorem pentadCollectionEquiv_mul (g h : Equiv.Perm (Fin 6)) :
    pentadCollectionEquiv (g * h) =
      (pentadCollectionEquiv h).trans (pentadCollectionEquiv g) := by
  rw [pentadCollectionEquiv, pentadEquiv_mul]
  exact (Equiv.finsetCongr_trans (pentadEquiv h) (pentadEquiv g)).symm

@[reducible]
public instance : MulAction (Equiv.Perm (Fin 6)) (Finset PentadData) where
  smul g S := pentadCollectionEquiv g S
  one_smul S := by
    change pentadCollectionEquiv 1 S = S
    rw [pentadCollectionEquiv_one]
    rfl
  mul_smul g h S := by
    change pentadCollectionEquiv (g * h) S =
      pentadCollectionEquiv g (pentadCollectionEquiv h S)
    rw [pentadCollectionEquiv_mul]
    rfl

public theorem pentadAt_injective : Function.Injective pentadAt := by
  all_goals decide
@[reducible]
public def pentadCollection : Finset PentadData :=
  Finset.univ.image pentadAt

public theorem finRotate_mem_pentadCollection_stabilizer :
    finRotate 6 ∈ MulAction.stabilizer (Equiv.Perm (Fin 6)) pentadCollection := by
  rw [MulAction.mem_stabilizer_iff]
  all_goals decide
public theorem adjacentSwap_mem_pentadCollection_stabilizer :
    Equiv.swap 0 (finRotate 6 0) ∈
      MulAction.stabilizer (Equiv.Perm (Fin 6)) pentadCollection := by
  rw [MulAction.mem_stabilizer_iff]
  all_goals decide
public theorem top_le_pentadCollection_stabilizer :
    (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≤
      MulAction.stabilizer (Equiv.Perm (Fin 6)) pentadCollection := by
  rw [← Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate_of_le (by decide))
    (support_finRotate_of_le (by decide)) 0,
    Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact finRotate_mem_pentadCollection_stabilizer
  · exact adjacentSwap_mem_pentadCollection_stabilizer

public theorem pentad_closed
    (g : Equiv.Perm (Fin 6)) (i : Fin 6) :
    ∃ j : Fin 6, pentadAt j = pentadMap g (pentadAt i) := by
  have hg := top_le_pentadCollection_stabilizer (Subgroup.mem_top g)
  rw [MulAction.mem_stabilizer_iff] at hg
  have hi : pentadAt i ∈ pentadCollection := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hgi : pentadMap g (pentadAt i) ∈ pentadCollection := by
    rw [← hg]
    change pentadMap g (pentadAt i) ∈
      (pentadEquiv g).finsetCongr pentadCollection
    exact Finset.mem_map.mpr ⟨pentadAt i, hi, rfl⟩
  rcases Finset.mem_image.mp hgi with ⟨j, -, hj⟩
  exact ⟨j, hj⟩

@[reducible, expose]
public def outerAct (g : Equiv.Perm (Fin 6)) (i : Fin 6) : Fin 6 :=
  (Fin.find? fun j ↦ decide (pentadAt j = pentadMap g (pentadAt i))).getD 0

public theorem outerAct_spec (g : Equiv.Perm (Fin 6)) (i : Fin 6) :
    pentadAt (outerAct g i) = pentadMap g (pentadAt i) := by
  let p : Fin 6 → Bool := fun j ↦ decide (pentadAt j = pentadMap g (pentadAt i))
  have hp : ∃ j, p j := by
    rcases pentad_closed g i with ⟨j, hj⟩
    exact ⟨j, by simp only [p, hj, decide_true]⟩
  change pentadAt ((Fin.find? p).getD 0) = pentadMap g (pentadAt i)
  rw [Fin.find?_eq_some_find_of_exists hp]
  simp only [Option.getD_some]
  have hfind := Fin.find_spec hp
  simpa only [p, decide_eq_true_eq] using hfind

public theorem outerAct_one (i : Fin 6) : outerAct 1 i = i := by
  apply pentadAt_injective
  rw [outerAct_spec]
  exact pentadMap_one (pentadAt i)

public theorem outerAct_mul (g h : Equiv.Perm (Fin 6)) (i : Fin 6) :
    outerAct (g * h) i = outerAct g (outerAct h i) := by
  apply pentadAt_injective
  rw [outerAct_spec, outerAct_spec, outerAct_spec]
  exact pentadMap_mul g h (pentadAt i)

@[reducible, expose]
public def outerPerm (g : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 6) where
  toFun := outerAct g
  invFun := outerAct g⁻¹
  left_inv i := by
    rw [← outerAct_mul]
    simpa using outerAct_one i
  right_inv i := by
    rw [← outerAct_mul]
    simpa using outerAct_one i

@[reducible, expose]
public def outerHom : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) where
  toFun := outerPerm
  map_one' := by
    apply Equiv.ext
    intro i
    exact outerAct_one i
  map_mul' g h := by
    apply Equiv.ext
    intro i
    exact outerAct_mul g h i

@[reducible, expose]
public def threeCyclePerm : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 0 2

public theorem threeCyclePerm_mem_alternating :
    threeCyclePerm ∈ alternatingGroup (Fin 6) := by
  exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (by decide) (by decide) (by decide)).mem_alternatingGroup

public theorem threeCyclePerm_not_mem_outerHom_ker :
    threeCyclePerm ∉ outerHom.ker := by
  intro h
  rw [MonoidHom.mem_ker] at h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 6) ↦ p 0) h
  have hout : outerHom threeCyclePerm 0 = 4 := by
    change outerAct threeCyclePerm 0 = 4
    apply pentadAt_injective
    rw [outerAct_spec]
    simp [pentadMap, pentadEquiv, pentadAt,
      threeCyclePerm, Equiv.finsetCongr_apply]
    all_goals decide
  rw [hout] at h0
  simp at h0

public theorem outerHom_injective : Function.Injective outerHom := by
  apply outerHom.ker_eq_bot_iff.mp
  by_contra hker
  let : Nontrivial outerHom.ker :=
    (Subgroup.nontrivial_iff_ne_bot outerHom.ker).2 hker
  exact threeCyclePerm_not_mem_outerHom_ker
    (Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (N := outerHom.ker)
      (by norm_num) inferInstance threeCyclePerm_mem_alternating)

public theorem outerHom_bijective : Function.Bijective outerHom :=
  ⟨outerHom_injective, Finite.surjective_of_injective outerHom_injective⟩

@[expose]
public noncomputable def outerAut : MulAut (Equiv.Perm (Fin 6)) :=
  MulEquiv.ofBijective outerHom outerHom_bijective

public theorem outerAut_preserves_alternating
    (g : alternatingGroup (Fin 6)) :
    outerAut (g : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by norm_num
  have hcomm := alternatingGroup.commutator_perm_eq h5
  have hg : (g : Equiv.Perm (Fin 6)) ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [hcomm]
    exact g.2
  have hout := (Subgroup.characteristic_iff_le_comap.mp inferInstance outerAut) hg
  rw [hcomm] at hout
  exact hout

public theorem outerAut_symm_preserves_alternating
    (g : alternatingGroup (Fin 6)) :
    outerAut.symm (g : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by norm_num
  have hcomm := alternatingGroup.commutator_perm_eq h5
  have hg : (g : Equiv.Perm (Fin 6)) ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [hcomm]
    exact g.2
  have hout := (Subgroup.characteristic_iff_le_comap.mp inferInstance outerAut.symm) hg
  rw [hcomm] at hout
  exact hout

@[expose]
public noncomputable def outerAltAut : MulAut (alternatingGroup (Fin 6)) where
  toFun g := ⟨outerAut g.1, outerAut_preserves_alternating g⟩
  invFun g := ⟨outerAut.symm g.1, outerAut_symm_preserves_alternating g⟩
  left_inv g := Subtype.ext (outerAut.left_inv g.1)
  right_inv g := Subtype.ext (outerAut.right_inv g.1)
  map_mul' g h := Subtype.ext (map_mul outerAut g.1 h.1)

@[expose]
public def baseThreeCycle : alternatingGroup (Fin 6) :=
  ⟨threeCyclePerm, threeCyclePerm_mem_alternating⟩

public theorem baseThreeCycle_isThreeCycle :
    (baseThreeCycle.1 : Equiv.Perm (Fin 6)).IsThreeCycle := by
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

@[reducible]
public def doubleThreeCyclePerm : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 3 * Equiv.swap 0 4) *
    (Equiv.swap 1 5 * Equiv.swap 1 2)

public theorem outerHom_threeCyclePerm_eq_doubleThreeCyclePerm :
    outerHom threeCyclePerm = doubleThreeCyclePerm := by
  apply Equiv.ext
  intro i
  change outerAct threeCyclePerm i = doubleThreeCyclePerm i
  apply pentadAt_injective
  rw [outerAct_spec]
  fin_cases i <;>
    simp [pentadMap, pentadEquiv, pentadAt,
      threeCyclePerm, doubleThreeCyclePerm, Equiv.finsetCongr_apply] <;>
    all_goals decide
public theorem doubleThreeCyclePerm_cycleType :
    doubleThreeCyclePerm.cycleType = {3, 3} := by
  let c₁ : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 0 4
  let c₂ : Equiv.Perm (Fin 6) := Equiv.swap 1 5 * Equiv.swap 1 2
  have hc₁ : c₁.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hc₂ : c₂.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hd : Equiv.Perm.Disjoint c₁ c₂ := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    all_goals decide
  change (c₁ * c₂).cycleType = {3, 3}
  rw [hd.cycleType_mul, hc₁, hc₂]
  rfl

public theorem doubleThreeCyclePerm_mem_alternating :
    doubleThreeCyclePerm ∈ alternatingGroup (Fin 6) := by
  have hc₁ := (Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (a := (0 : Fin 6)) (b := 3) (c := 4) (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hc₂ := (Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (a := (1 : Fin 6)) (b := 5) (c := 2) (by decide) (by decide) (by decide)).mem_alternatingGroup
  exact Subgroup.mul_mem _ hc₁ hc₂

public def doubleThreeCycle : alternatingGroup (Fin 6) :=
  ⟨doubleThreeCyclePerm, doubleThreeCyclePerm_mem_alternating⟩

@[reducible]
public def doubleThreeCycleOddCentralizer : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 4 2 * Equiv.swap 3 5

public theorem doubleThreeCycleOddCentralizer_sign :
    Equiv.Perm.sign doubleThreeCycleOddCentralizer = -1 := by
  rw [doubleThreeCycleOddCentralizer, map_mul, map_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

public theorem doubleThreeCycleOddCentralizer_commute :
    Commute doubleThreeCycleOddCentralizer doubleThreeCyclePerm := by
  change doubleThreeCycleOddCentralizer * doubleThreeCyclePerm =
    doubleThreeCyclePerm * doubleThreeCycleOddCentralizer
  apply Equiv.ext
  intro i
  fin_cases i <;>
    simp [doubleThreeCycleOddCentralizer, doubleThreeCyclePerm,
      Equiv.Perm.mul_apply] <;>
    all_goals decide
public theorem doubleThreeCycle_isConj
    (g : alternatingGroup (Fin 6))
    (hg : (g.1 : Equiv.Perm (Fin 6)).cycleType = {3, 3}) :
    IsConj doubleThreeCycle g := by
  have hperm : IsConj doubleThreeCyclePerm (g.1 : Equiv.Perm (Fin 6)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.2
      (doubleThreeCyclePerm_cycleType.trans hg.symm)
  rcases isConj_iff.mp hperm with ⟨π, hπ⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hsign | hsign
  · rw [isConj_iff]
    refine ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mp hsign⟩, ?_⟩
    apply Subtype.ext
    exact hπ
  · let s := doubleThreeCycleOddCentralizer
    have hs : Equiv.Perm.sign s = -1 := doubleThreeCycleOddCentralizer_sign
    have hπs : π * s ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, hsign, hs]
      norm_num
    have hsconj : s * doubleThreeCyclePerm * s⁻¹ = doubleThreeCyclePerm := by
      calc
        s * doubleThreeCyclePerm * s⁻¹ = doubleThreeCyclePerm * s * s⁻¹ := by
          rw [doubleThreeCycleOddCentralizer_commute.eq]
        _ = doubleThreeCyclePerm := by simp
    rw [isConj_iff]
    refine ⟨⟨π * s, hπs⟩, ?_⟩
    apply Subtype.ext
    change (π * s) * doubleThreeCyclePerm * (π * s)⁻¹ = g.1
    calc
      (π * s) * doubleThreeCyclePerm * (π * s)⁻¹ =
          π * (s * doubleThreeCyclePerm * s⁻¹) * π⁻¹ := by group
      _ = π * doubleThreeCyclePerm * π⁻¹ := by rw [hsconj]
      _ = g.1 := hπ

@[reducible]
public def outerDoubleImagePerm : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 1 4

public theorem outerHom_doubleThreeCyclePerm_eq_outerDoubleImagePerm :
    outerHom doubleThreeCyclePerm = outerDoubleImagePerm := by
  apply Equiv.ext
  intro i
  change outerAct doubleThreeCyclePerm i = outerDoubleImagePerm i
  apply pentadAt_injective
  rw [outerAct_spec]
  fin_cases i <;>
    simp [pentadMap, pentadEquiv, pentadAt, doubleThreeCyclePerm,
      outerDoubleImagePerm, Equiv.finsetCongr_apply] <;>
    all_goals decide
public theorem outerDoubleImagePerm_isThreeCycle :
    outerDoubleImagePerm.IsThreeCycle := by
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (a := (1 : Fin 6)) (b := 2) (c := 4) (by decide) (by decide) (by decide)

public theorem outerAltAut_doubleThreeCycle_isThreeCycle :
    ((outerAltAut doubleThreeCycle).1 : Equiv.Perm (Fin 6)).IsThreeCycle := by
  change (outerHom doubleThreeCyclePerm).IsThreeCycle
  rw [outerHom_doubleThreeCyclePerm_eq_outerDoubleImagePerm]
  exact outerDoubleImagePerm_isThreeCycle

public theorem outerAltAut_double_to_three
    (g : alternatingGroup (Fin 6))
    (hg : (g.1 : Equiv.Perm (Fin 6)).cycleType = {3, 3}) :
    ((outerAltAut g).1 : Equiv.Perm (Fin 6)).IsThreeCycle := by
  have hconj := doubleThreeCycle_isConj g hg
  have hconj' := outerAltAut.toMonoidHom.map_isConj hconj
  have hperm := (Subgroup.subtype (alternatingGroup (Fin 6))).map_isConj hconj'
  have hct := Equiv.Perm.isConj_iff_cycleType_eq.mp hperm
  calc
    ((outerAltAut g).1 : Equiv.Perm (Fin 6)).cycleType =
        ((outerAltAut doubleThreeCycle).1 : Equiv.Perm (Fin 6)).cycleType := hct.symm
    _ = {3} := outerAltAut_doubleThreeCycle_isThreeCycle

public theorem outerAltAut_base_cycleType :
    ((outerAltAut baseThreeCycle).1 : Equiv.Perm (Fin 6)).cycleType = {3, 3} := by
  change (outerHom threeCyclePerm).cycleType = {3, 3}
  rw [outerHom_threeCyclePerm_eq_doubleThreeCyclePerm]
  exact doubleThreeCyclePerm_cycleType

public theorem alternatingSix_cycleType_of_order_three
    (g : alternatingGroup (Fin 6)) (hg : orderOf g = 3) :
    (g.1 : Equiv.Perm (Fin 6)).IsThreeCycle ∨
      (g.1 : Equiv.Perm (Fin 6)).cycleType = {3, 3} := by
  have horder : orderOf (g.1 : Equiv.Perm (Fin 6)) = 3 :=
    (Subgroup.orderOf_coe g).trans hg
  have hprime : (orderOf (g.1 : Equiv.Perm (Fin 6))).Prime := by
    rw [horder]
    exact Nat.prime_three
  obtain ⟨m, hct⟩ := Equiv.Perm.cycleType_prime_order hprime
  let k := m + 1
  have hkpos : 0 < k := by simp [k]
  have hct3 : (g.1 : Equiv.Perm (Fin 6)).cycleType =
      Multiset.replicate k 3 := by
    simpa only [k, horder] using hct
  have hsupport : 3 * k ≤ 6 := by
    have hle : (g.1 : Equiv.Perm (Fin 6)).support.card ≤ 6 := by
      simpa using Finset.card_le_univ (g.1 : Equiv.Perm (Fin 6)).support
    rw [← Equiv.Perm.sum_cycleType, hct3, Multiset.sum_replicate,
      nsmul_eq_mul] at hle
    simpa [Nat.mul_comm] using hle
  have hk : k = 1 ∨ k = 2 := by omega
  rcases hk with hk | hk
  · left
    change (g.1 : Equiv.Perm (Fin 6)).cycleType = {3}
    simpa [hk] using hct3
  · right
    simpa [hk] using hct3

@[expose]
public def naturalAlternatingAutomorphismSubgroup :
    Subgroup (MulAut (alternatingGroup (Fin 6))) :=
  (MulAut.conjNormal : Equiv.Perm (Fin 6) →*
    MulAut (alternatingGroup (Fin 6))).range

public noncomputable def permSixMulEquivNaturalAlternatingAutomorphisms :
    Equiv.Perm (Fin 6) ≃* naturalAlternatingAutomorphismSubgroup :=
  MonoidHom.ofInjective (GLS3.Chapter5.alternatingConjHom_injective (by norm_num))

public theorem naturalAlternatingAutomorphismSubgroup_index :
    naturalAlternatingAutomorphismSubgroup.index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  refine ⟨outerAltAut, ?_, ?_⟩
  · intro hout
    rcases hout with ⟨p, hp⟩
    have hconjThree :
        ((((MulAut.conjNormal p) baseThreeCycle).1 :
          Equiv.Perm (Fin 6))).IsThreeCycle := by
      change (p * threeCyclePerm * p⁻¹).cycleType = {3}
      rw [Equiv.Perm.cycleType_conj]
      exact baseThreeCycle_isThreeCycle
    have houtThree :
        (((outerAltAut baseThreeCycle).1 :
          Equiv.Perm (Fin 6))).IsThreeCycle := by
      rw [← hp]
      exact hconjThree
    change ((outerAltAut baseThreeCycle).1 :
      Equiv.Perm (Fin 6)).cycleType = {3} at houtThree
    have hbad := (outerAltAut_base_cycleType).symm.trans houtThree
    have hcard := congrArg Multiset.card hbad
    norm_num at hcard
  · intro φ
    have hbaseOrder : orderOf baseThreeCycle = 3 := by
      calc
        orderOf baseThreeCycle = orderOf threeCyclePerm :=
          (Subgroup.orderOf_coe baseThreeCycle).symm
        _ = 3 := baseThreeCycle_isThreeCycle.orderOf
    have himageOrder : orderOf (φ baseThreeCycle) = 3 :=
      (φ.orderOf_eq baseThreeCycle).trans hbaseOrder
    rcases alternatingSix_cycleType_of_order_three (φ baseThreeCycle) himageOrder with
      hsingle | hdouble
    · right
      have hmaps : ∀ g : alternatingGroup (Fin 6),
          (g.1 : Equiv.Perm (Fin 6)).IsThreeCycle →
            ((φ g).1 : Equiv.Perm (Fin 6)).IsThreeCycle := by
        intro g hg
        have hc := alternatingGroup.isThreeCycle_isConj (α := Fin 6)
          (by norm_num) baseThreeCycle_isThreeCycle hg
        have hcφ := φ.toMonoidHom.map_isConj hc
        have hpφ := (Subgroup.subtype (alternatingGroup (Fin 6))).map_isConj hcφ
        have hct := Equiv.Perm.isConj_iff_cycleType_eq.mp hpφ
        exact hct.symm.trans hsingle
      obtain ⟨p, hp⟩ :=
        GLS3.Chapter5.automorphism_eq_conjNormal_of_maps_threeCycles
          (by norm_num) φ hmaps
      exact ⟨p, hp.symm⟩
    · left
      have hmaps : ∀ g : alternatingGroup (Fin 6),
          (g.1 : Equiv.Perm (Fin 6)).IsThreeCycle →
            ((((outerAltAut * φ) g).1 : Equiv.Perm (Fin 6))).IsThreeCycle := by
        intro g hg
        have hc := alternatingGroup.isThreeCycle_isConj (α := Fin 6)
          (by norm_num) baseThreeCycle_isThreeCycle hg
        have hcφ := φ.toMonoidHom.map_isConj hc
        have hpφ := (Subgroup.subtype (alternatingGroup (Fin 6))).map_isConj hcφ
        have hct := Equiv.Perm.isConj_iff_cycleType_eq.mp hpφ
        have hφg : ((φ g).1 : Equiv.Perm (Fin 6)).cycleType = {3, 3} :=
          hct.symm.trans hdouble
        change (((outerAltAut (φ g)).1 : Equiv.Perm (Fin 6))).IsThreeCycle
        exact outerAltAut_double_to_three (φ g) hφg
      obtain ⟨p, hp⟩ :=
        GLS3.Chapter5.automorphism_eq_conjNormal_of_maps_threeCycles
          (by norm_num) (outerAltAut * φ) hmaps
      exact ⟨p, hp.symm⟩

/-- Theorem 5.2.1(b): `Aut(A₆)` contains a subgroup isomorphic to `S₆`
of index two. -/
public theorem theorem_5_2_1_b :
    ∃ H : Subgroup (MulAut (alternatingGroup (Fin 6))),
      H.index = 2 ∧ Nonempty (H ≃* Equiv.Perm (Fin 6)) := by
  exact ⟨naturalAlternatingAutomorphismSubgroup,
    naturalAlternatingAutomorphismSubgroup_index,
    ⟨permSixMulEquivNaturalAlternatingAutomorphisms.symm⟩⟩

end GLS3.Chapter5
/- END Theory.Automorphism -/

/- BEGIN Theory.CentralKernelLiftReplacement -/
namespace GLS3.Chapter5

/-- Replacing a lift by a product with the same image modulo a central kernel
preserves a noncommuting factor witness. -/
public theorem not_commute_of_image_eq_mul_of_central_kernel
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hkerCenter : f.ker ≤ Subgroup.center G)
    (y a b v : G) (hy : f y = f (a * b))
    (hbv : Commute b v) (hav : ¬ Commute a v) :
    ¬ Commute y v := by
  let k := y * (a * b)⁻¹
  have hkKer : k ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simp [k, hy]
  have hkv : Commute k v :=
    (Subgroup.mem_center_iff.mp (hkerCenter hkKer) v).symm
  intro hyv
  have habv : Commute (a * b) v := by
    have hkyv : Commute (k⁻¹ * y) v := Commute.mul_left hkv.inv_left hyv
    simpa [k, mul_assoc] using hkyv
  apply hav
  have habbv : Commute ((a * b) * b⁻¹) v :=
    Commute.mul_left habv hbv.inv_left
  simpa [mul_assoc] using habbv

end GLS3.Chapter5
/- END Theory.CentralKernelLiftReplacement -/

/- BEGIN Theory.CentralKernelProductCommute -/
namespace GLS3.Chapter5

/-- A lift with the same image as a commuting product also commutes when the
homomorphism kernel is central. -/
public theorem commute_of_image_eq_mul_of_central_kernel
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hkerCenter : f.ker ≤ Subgroup.center G)
    (y a b v : G) (hy : f y = f (a * b))
    (hav : Commute a v) (hbv : Commute b v) :
    Commute y v := by
  let k := y * (a * b)⁻¹
  have hkKer : k ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simp [k, hy]
  have hkv : Commute k v :=
    (Subgroup.mem_center_iff.mp (hkerCenter hkKer) v).symm
  have habv : Commute (a * b) v := Commute.mul_left hav hbv
  have hprod : Commute (k * (a * b)) v := Commute.mul_left hkv habv
  simpa [k, mul_assoc] using hprod

end GLS3.Chapter5
/- END Theory.CentralKernelProductCommute -/

/- BEGIN Theory.QuasisimpleImageOfCentralKernel -/
namespace GLS3.Chapter5

/-- A nontrivial surjective image of a quasisimple group is quasisimple when
the kernel is central. -/
public theorem isQuasisimple_of_surjective_of_ker_le_center
    {G H : Type*} [Group G] [Group H]
    [IsQuasisimple G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f)
    (_hker : f.ker ≤ Subgroup.center G) :
    IsQuasisimple H := by
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective hf
  have hcenter : Subgroup.center G ≤
      (Subgroup.center H).comap f := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    simpa only [map_mul] using
      congrArg f (Subgroup.mem_center_iff.mp hz x)
  let q : G ⧸ Subgroup.center G →*
      H ⧸ Subgroup.center H :=
    QuotientGroup.map (Subgroup.center G) (Subgroup.center H) f hcenter
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective
      (Subgroup.center G) (Subgroup.center H) f
      ((QuotientGroup.mk'_surjective (Subgroup.center H)).comp hf) hcenter
  let : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    (inferInstance : IsQuasisimple G).simple
  have : Nontrivial (H ⧸ Subgroup.center H) := by
    rw [QuotientGroup.nontrivial_iff]
    intro hcenterTop
    let : IsMulCommutative H := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center H := by
        rw [hcenterTop]
        trivial
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact Group.IsPerfect.not_isSolvable H
      (inferInstance : Group.IsSolvable H)
  let : IsSimpleGroup (H ⧸ Subgroup.center H) :=
    IsSimpleGroup.isSimpleGroup_of_surjective q hq
  exact { toIsPerfect := inferInstance, simple := inferInstance }

end GLS3.Chapter5
/- END Theory.QuasisimpleImageOfCentralKernel -/

/- BEGIN Theory.QuasisimpleNormalSubgroupDichotomy -/
namespace GLS3.Chapter5

/-- A normal subgroup of a quasisimple group is either the whole group or is
contained in the center. -/
public theorem normal_eq_top_or_le_center_of_isQuasisimple
    {G : Type*} [Group G] [IsQuasisimple G]
    (N : Subgroup G) [N.Normal] :
    N = ⊤ ∨ N ≤ Subgroup.center G := by
  let q : G →* G ⧸ Subgroup.center G :=
    QuotientGroup.mk' (Subgroup.center G)
  let : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    (inferInstance : IsQuasisimple G).simple
  have : (N.map q).Normal :=
    (inferInstance : N.Normal).map q
      (QuotientGroup.mk'_surjective (Subgroup.center G))
  rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hbot | htop
  · right
    intro n hn
    have hqn : q n ∈ N.map q := ⟨n, hn, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hqn
    exact QuotientGroup.eq_one_iff n |>.mp hqn
  · left
    have hsup : N ⊔ Subgroup.center G = ⊤ := by
      apply le_antisymm le_top
      intro g _
      have hqg : q g ∈ N.map q := by rw [htop]; trivial
      obtain ⟨n, hn, hng⟩ := hqg
      have hz : n⁻¹ * g ∈ Subgroup.center G := by
        apply QuotientGroup.eq_one_iff (n⁻¹ * g) |>.mp
        change q n⁻¹ * q g = 1
        rw [map_inv, hng, inv_mul_cancel]
      have hmem := (N ⊔ Subgroup.center G).mul_mem
        ((show N ≤ N ⊔ Subgroup.center G from le_sup_left) hn)
        ((show Subgroup.center G ≤ N ⊔ Subgroup.center G from le_sup_right) hz)
      simpa only [mul_assoc, mul_inv_cancel_left] using hmem
    apply top_unique
    have hcomm : _root_.commutator G ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        hsup inferInstance
    simpa using hcomm

end GLS3.Chapter5
/- END Theory.QuasisimpleNormalSubgroupDichotomy -/

/- BEGIN Theory.SchurMultiplier -/
namespace GLS3.Chapter5.Covering
universe __ch5_SchurMultiplier_u __ch5_SchurMultiplier_v

/-! ## Schur multiplier infrastructure (Theorem 5.2.3, source skeleton)

The remaining clauses of the printed Theorem 5.2.3 (Schur) require the
classification of the Schur multipliers of the alternating groups.  This
module establishes the *transfer* infrastructure on top of the `Covering`
API: a base-preserving isomorphism between covering groups induces an
isomorphism of their kernels, hence a canonical isomorphism between the
kernels of any two universal coverings (the Schur multiplier of the base).

Source positions:
* [A1, 33.1] — `refs/KGroup/GLS3/Ch5A1.tex` (Aschbacher, FGT ch. 33): up to
  isomorphism there is at most one universal central extension, and its
  kernel is the Schur multiplier; (33.15) computes it for the alternating
  groups (`M(A_n) ≅ Z₆` for `n = 6, 7`, `≅ Z₂` otherwise; `3^{1+2}` Sylow-3
  for `n = 6, 7`).
* [Su1, pp. 301-306] — `refs/KGroup/GLS3/Ch5Su1.tex` (Suzuki GT I, Ch. 3
  §2): (2.21) multiplier of `Σ_n`; (2.22) multiplier of `A_n` of order 2 for
  `n ≠ 6, 7`; p. 305: `M(A₆) = M(A₇) ≅ C₆`.
-/

section KernelTransfer

variable {G₁ G₂ : Type __ch5_SchurMultiplier_u} {H : Type __ch5_SchurMultiplier_v}
variable [Group G₁] [Finite G₁] [IsQuasisimple G₁]
variable [Group G₂] [Finite G₂] [IsQuasisimple G₂]
variable [Group H] [Finite H] [IsQuasisimple H]

/-- A base-preserving covering isomorphism carries the kernel of the first
covering into the kernel of the second. -/
public theorem mem_kernel_map_of_mem_kernel (f₁ : Covering G₁ H) (f₂ : Covering G₂ H)
    (e : G₁ ≃* G₂) (he : f₂.comp (Covering.ofMulEquiv e) = f₁)
    {x : G₁} (hx : x ∈ f₁.toMonoidHom.ker) :
    e x ∈ f₂.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  change f₂ (e x) = 1
  have hx' : f₂ (e x) = f₁ x := by
    rw [← he]
    rfl
  rw [hx']
  exact hx

/-- A base-preserving covering isomorphism induces an isomorphism between the
kernels (i.e. between the Schur multipliers, in the universal case). -/
public noncomputable def kernelMulEquiv (f₁ : Covering G₁ H) (f₂ : Covering G₂ H)
    (e : G₁ ≃* G₂) (he : f₂.comp (Covering.ofMulEquiv e) = f₁) :
    ↥f₁.toMonoidHom.ker ≃* ↥f₂.toMonoidHom.ker where
  toFun x := ⟨e x.1, mem_kernel_map_of_mem_kernel f₁ f₂ e he x.2⟩
  invFun y := ⟨e.symm y.1, by
    have hz : ∀ z : G₁, f₁ z = f₂ (e z) := by
      intro z
      rw [← he]
      rfl
    have hy1 : f₂ y.1 = 1 := (MonoidHom.mem_ker.mp y.2)
    change f₁ (e.symm y.1) = 1
    calc
      f₁ (e.symm y.1) = f₂ (e (e.symm y.1)) := hz (e.symm y.1)
      _ = f₂ y.1 := by rw [e.apply_symm_apply]
      _ = 1 := hy1⟩
  left_inv x := by
    apply Subtype.ext
    change e.symm (e x.1) = x.1
    rw [e.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    change e (e.symm y.1) = y.1
    rw [e.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    change e (x.1 * y.1) = e x.1 * e y.1
    exact e.map_mul x.1 y.1

/-- Cardinalities of the kernels are invariant under base-preserving
covering isomorphisms. -/
public theorem kernel_card_eq_of_mulEquiv (f₁ : Covering G₁ H) (f₂ : Covering G₂ H)
    (e : G₁ ≃* G₂) (he : f₂.comp (Covering.ofMulEquiv e) = f₁) :
    Nat.card ↥f₁.toMonoidHom.ker = Nat.card ↥f₂.toMonoidHom.ker :=
  Nat.card_congr (kernelMulEquiv f₁ f₂ e he)

end KernelTransfer

section UniversalKernel

variable {K L₁ L₂ : Type __ch5_SchurMultiplier_u}
variable [Group K] [Finite K] [IsQuasisimple K]
variable [Group L₁] [Finite L₁] [IsQuasisimple L₁]
variable [Group L₂] [Finite L₂] [IsQuasisimple L₂]

/-- The kernels of two universal coverings of the same group are isomorphic:
by universal uniqueness there is a base-preserving isomorphism between the
covering groups, and `kernelMulEquiv` transfers it to the kernels.  This
makes "the Schur multiplier of `K`" a well-defined object up to isomorphism
([A1, 33.1], [Su1, Ch. 2 §9]). -/
public noncomputable def universalKernelMulEquiv (f₁ : Covering L₁ K) (f₂ : Covering L₂ K)
    (hf₁ : IsUniversal.{__ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u} f₁) (hf₂ : IsUniversal.{__ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u} f₂) :
    ↥f₁.toMonoidHom.ker ≃* ↥f₂.toMonoidHom.ker := by
  let h := existsUnique_mulEquiv_of_isUniversal_sameBase f₁ f₂ hf₁ hf₂
  let e : L₁ ≃* L₂ := Classical.choose h
  have he : f₂.comp (Covering.ofMulEquiv e) = f₁ := (Classical.choose_spec h).1
  exact kernelMulEquiv f₁ f₂ e he

/-- Cardinality of the Schur multiplier is well-defined: any two universal
coverings of the same group have kernels of the same cardinality. -/
public theorem universalKernel_card_eq (f₁ : Covering L₁ K) (f₂ : Covering L₂ K)
    (hf₁ : IsUniversal.{__ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u} f₁) (hf₂ : IsUniversal.{__ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u, __ch5_SchurMultiplier_u} f₂) :
    Nat.card ↥f₁.toMonoidHom.ker = Nat.card ↥f₂.toMonoidHom.ker :=
  Nat.card_congr (universalKernelMulEquiv f₁ f₂ hf₁ hf₂)

end UniversalKernel

end GLS3.Chapter5.Covering
/- END Theory.SchurMultiplier -/

/- BEGIN Theory.DirectProductSubgroupMulEquivApply -/
open scoped Pointwise

namespace GLS3.Chapter5

/-- The internal direct-product equivalence with its multiplication formula
exposed for transport arguments. -/
public theorem exists_mulEquiv_prod_sup_of_disjoint_of_commute_apply
    {G : Type*} [Group G] (A B : Subgroup G)
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1) :
    ∃ e : (A × B) ≃* ↥(A ⊔ B),
      ∀ x : A × B, e x =
        (⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B)) := by
  let f : A × B →* ↥(A ⊔ B) :=
    { toFun := fun x =>
        ⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
          (x.1.1 * x.2.1) * (y.1.1 * y.2.1)
        calc
          (x.1.1 * y.1.1) * (x.2.1 * y.2.1) =
              x.1.1 * (y.1.1 * x.2.1) * y.2.1 := by simp [mul_assoc]
          _ = x.1.1 * (x.2.1 * y.1.1) * y.2.1 := by
            rw [(hcommute y.1 x.2).eq]
          _ = (x.1.1 * x.2.1) * (y.1.1 * y.2.1) := by simp [mul_assoc] }
  have hcentralizer : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcommute ⟨a, ha⟩ ⟨b, hb⟩).eq.symm
  have hnormalizer : A ≤ Subgroup.normalizer B :=
    hcentralizer.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hsurjective : Function.Surjective f := by
    intro x
    have hxset : x.1 ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnormalizer]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hxset
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact hab
  have hinjective : Function.Injective f := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  let e : (A × B) ≃* ↥(A ⊔ B) :=
    MulEquiv.ofBijective f ⟨hinjective, hsurjective⟩
  refine ⟨e, ?_⟩
  intro x
  rfl

end GLS3.Chapter5
/- END Theory.DirectProductSubgroupMulEquivApply -/

/- BEGIN Theory.SubnormalComplementFullCommutator -/
namespace GLS3.Chapter5

/-- If `R` and `L` generate the ambient group and `R` is generated by its
commutators with `L`, then the normal closure of `L` is the ambient group. -/
public theorem normalClosure_eq_top_of_sup_eq_top_of_le_commutator
    {G : Type*} [Group G] (R L : Subgroup G)
    (hsup : R ⊔ L = ⊤)
    (hRcomm : R ≤ ⁅R, L⁆) :
    Subgroup.normalClosure (L : Set G) = ⊤ := by
  apply top_unique
  rw [← hsup]
  apply sup_le
  · exact hRcomm.trans (Subgroup.commutator_le.mpr fun r hr l hl => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _
        (Subgroup.normalClosure_normal.conj_mem l
          (Subgroup.subset_normalClosure hl) r)
        (Subgroup.inv_mem _ (Subgroup.subset_normalClosure hl)))
  · exact fun _ hl => Subgroup.subset_normalClosure hl

/-- A subnormal complement cannot be proper when the normal factor is
generated by commutators with that complement. -/
public theorem eq_top_of_isSubnormal_of_sup_eq_top_of_le_commutator
    {G : Type*} [Group G] (R L : Subgroup G)
    (hL : L.IsSubnormal)
    (hsup : R ⊔ L = ⊤)
    (hRcomm : R ≤ ⁅R, L⁆) :
    L = ⊤ := by
  apply eq_top_of_isSubnormal_of_normalClosure_eq_top L hL
  exact normalClosure_eq_top_of_sup_eq_top_of_le_commutator R L hsup hRcomm

end GLS3.Chapter5
/- END Theory.SubnormalComplementFullCommutator -/

/- BEGIN Theory.CentralCommutatorHom -/
namespace GLS3.Chapter5

open scoped commutatorElement

/-- When all commutators with a fixed element are central, the commutator map
is a homomorphism into the center. -/
@[expose]
public def centralCommutatorHom
    {P K : Type*} [Group P] [Group K]
    (s : P →* K) (b : K)
    (hc : ∀ a : P, ⁅s a, b⁆ ∈ Subgroup.center K) :
    P →* Subgroup.center K where
  toFun a := ⟨⁅s a, b⁆, hc a⟩
  map_one' := by ext; simp
  map_mul' a₁ a₂ := by
    apply Subtype.ext
    change ⁅s (a₁ * a₂), b⁆ = ⁅s a₁, b⁆ * ⁅s a₂, b⁆
    rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
    have hc₂ := hc a₂
    have hconj : s a₁ * ⁅s a₂, b⁆ * (s a₁)⁻¹ = ⁅s a₂, b⁆ := by
      have hcomm := Subgroup.mem_center_iff.mp hc₂ (s a₁)
      rw [hcomm]
      simp
    rw [hconj]
    exact (Subgroup.mem_center_iff.mp hc₂ ⁅s a₁, b⁆).symm

end GLS3.Chapter5
/- END Theory.CentralCommutatorHom -/

/- BEGIN Theory.ExtraspecialOrAbelianCenter -/
noncomputable section

namespace GLS3.Chapter5

/-- A finite `2`-group whose center has order two and contains its Frattini
subgroup is either extraspecial or abelian.  In the abelian branch its center
is the whole group, so a separately identified order-two center forces the
group itself to have order two. -/
public theorem isExtraspecialTwoSubgroup_or_center_eq_top
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hcenterCard : Nat.card (Subgroup.center P) = 2)
    (hfrattini : frattini P ≤ Subgroup.center P) :
    IsExtraspecialTwoSubgroup P ∨ Subgroup.center P = ⊤ := by
  have hcommPhi : _root_.commutator P ≤ frattini P := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact commutator_le_frattini_of_isPGroup hP
  have hcommCenter : _root_.commutator P ≤ Subgroup.center P :=
    hcommPhi.trans hfrattini
  let C : Subgroup (Subgroup.center P) :=
    (_root_.commutator P).subgroupOf (Subgroup.center P)
  let : Fact (Nat.card (Subgroup.center P)).Prime :=
    ⟨by simpa [hcenterCard] using Nat.prime_two⟩
  rcases C.eq_bot_or_eq_top_of_prime_card with hC | hC
  · right
    apply (commutator_eq_bot_iff_center_eq_top P).mp
    apply le_antisymm
    · intro x hx
      have hxC : (⟨x, hcommCenter hx⟩ : Subgroup.center P) ∈ C := hx
      rw [hC] at hxC
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxC)
    · exact bot_le
  · left
    have hcenterComm : Subgroup.center P ≤ _root_.commutator P := by
      exact Subgroup.subgroupOf_eq_top.mp hC
    have hcommEq : _root_.commutator P = Subgroup.center P :=
      le_antisymm hcommCenter hcenterComm
    have hPhiEq : frattini P = Subgroup.center P :=
      le_antisymm hfrattini (hcommEq ▸ hcommPhi)
    exact ⟨hP, hcommEq, hPhiEq, hcenterCard⟩

end GLS3.Chapter5
/- END Theory.ExtraspecialOrAbelianCenter -/

/- BEGIN Theory.TraceZeroAllOneParity -/
noncomputable section
namespace GLS3.Chapter5

public theorem traceZeroTwoSubgroup_allOne_mem_iff_even (r : Nat) :
    (fun _ : Fin r => (1 : ZMod 2)) ∈ traceZeroTwoSubgroup r ↔ Even r := by
  rw [mem_traceZeroTwoSubgroup]
  rw [show (∑ _ : Fin r, (1 : ZMod 2)) = (r : ZMod 2) by simp]
  constructor
  · intro h
    apply (Nat.even_iff).2
    by_contra hmod
    have hmod1 : r % 2 = 1 := by omega
    have hz : (1 : ZMod 2) = 0 := by
      calc
        (1 : ZMod 2) = (↑(r % 2) : ZMod 2) := by simp [hmod1]
        _ = (r : ZMod 2) := ZMod.natCast_mod r 2
        _ = 0 := h
    norm_num at hz
  · intro h
    rw [← ZMod.natCast_mod r 2]
    rw [(Nat.even_iff).1 h]
    exact ZMod.natCast_self 2

end GLS3.Chapter5
/- END Theory.TraceZeroAllOneParity -/

/- BEGIN Theory.TraceZeroNonconstantCoordinates -/
noncomputable section

namespace GLS3.Chapter5

/-- A nonzero, nonconstant trace-zero vector over `ZMod 2` has two distinct
coordinates equal to one and a third coordinate equal to zero. -/
public theorem traceZero_exists_two_one_one_zero_coordinates
    {r : Nat} (v : traceZeroTwoSubgroup r)
    (hvzero : v.1 ≠ 0) (hvall : v.1 ≠ fun _ => 1) :
    ∃ i j k : Fin r,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      v.1 i = 1 ∧ v.1 j = 1 ∧ v.1 k = 0 := by
  classical
  have zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
    have hlt : a.val < 2 := ZMod.val_lt a
    have hval : a.val = 0 ∨ a.val = 1 := by omega
    rcases hval with hval | hval
    · left
      apply ZMod.val_injective 2
      simpa using hval
    · right
      apply ZMod.val_injective 2
      rw [ZMod.val_one]
      exact hval
  have hexistsOne : ∃ i, v.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply hvzero
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hexistsOne
  have hiOne : v.1 i = 1 :=
    (zmodTwo_eq_zero_or_one (v.1 i)).resolve_left hi
  have hexistsZero : ∃ k, v.1 k ≠ 1 := by
    by_contra h
    push Not at h
    apply hvall
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hexistsZero
  have hkZero : v.1 k = 0 :=
    (zmodTwo_eq_zero_or_one (v.1 k)).resolve_right hk
  have hexistsSecond : ∃ j, j ≠ i ∧ v.1 j ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : ∑ j, v.1 j = v.1 i := by
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        exact h j hji
      · simp
    have hvsum : ∑ j, v.1 j = 0 :=
      (mem_traceZeroTwoSubgroup v.1).mp v.2
    exact hi (hsum ▸ hvsum)
  obtain ⟨j, hji, hj⟩ := hexistsSecond
  have hjOne : v.1 j = 1 :=
    (zmodTwo_eq_zero_or_one (v.1 j)).resolve_left hj
  have hik : i ≠ k := by
    intro hik
    rw [hik, hkZero] at hi
    exact hi rfl
  have hjk : j ≠ k := by
    intro hjk
    rw [hjk, hkZero] at hj
    exact hj rfl
  exact ⟨i, j, k, hji.symm, hik, hjk, hiOne, hjOne, hkZero⟩

end GLS3.Chapter5
/- END Theory.TraceZeroNonconstantCoordinates -/

/- BEGIN Theory.ElementaryAbelianFourComplement -/
noncomputable section

namespace GLS3.Chapter5

/-- A prescribed subgroup of order two in a four-element `F₂`-vector group
has a complementary subgroup of order two. -/
public theorem exists_order_two_complement_of_vector_group
    {X V : Type*} [Group X] [Finite X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : X ≃* Multiplicative V) (Z : Subgroup X)
    (hXcard : Nat.card X = 4) (hZcard : Nat.card Z = 2) :
    ∃ C : Subgroup X,
      Z ⊔ C = ⊤ ∧ Z ⊓ C = ⊥ ∧ Nat.card C = 2 ∧ IsCyclic C := by
  have hker : e.toMonoidHom.ker = (⊥ : Subgroup X) :=
    (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  obtain ⟨C, hsup, hinf⟩ :=
    exists_sup_eq_top_inf_eq_ker_of_vector_quotient e.toMonoidHom Z
      (hker ▸ bot_le)
  have hinfBot : Z ⊓ C = ⊥ := hinf.trans hker
  have hCcard : Nat.card C = 2 := by
    have hdvd : Nat.card C ∣ 2 ^ 2 := by
      simpa [hXcard] using Subgroup.card_subgroup_dvd_card C
    obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · have hCbot : C = ⊥ :=
        (Subgroup.eq_bot_iff_card C).mpr (by simpa using hkcard)
      have hZtop : Z = ⊤ := by simpa [hCbot] using hsup
      have : Nat.card Z = Nat.card X :=
        (Subgroup.card_eq_iff_eq_top Z).mpr hZtop
      omega
    · simpa using hkcard
    · have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by omega)
      have hZbot : Z = ⊥ := by simpa [hCtop] using hinfBot
      have : Nat.card Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hZbot
      omega
  refine ⟨C, hsup, hinfBot, hCcard, ?_⟩
  exact isCyclic_of_prime_card hCcard

end GLS3.Chapter5
/- END Theory.ElementaryAbelianFourComplement -/

/- BEGIN KGroup.GLS3.Chapter5.theorem_5_2_1 -/
/- Source: theorem_5_2_1_a.lean -/

set_option maxHeartbeats 800000

namespace GLS3.Chapter5

/-! Printed Theorem 5.2.1(a), exposed from the automorphism proof module. -/
public noncomputable def theorem_5_2_1_a_split
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 < Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6) :
    MulAut (alternatingGroup Ω) ≃* Equiv.Perm Ω :=
  theorem_5_2_1_a h5 h6

end GLS3.Chapter5

/- Source: theorem_5_2_1_b.lean -/

namespace GLS3.Chapter5

/-! Printed Theorem 5.2.1(b), exposed as its own theorem file. -/
public theorem theorem_5_2_1_b_split :
    ∃ H : Subgroup (MulAut (alternatingGroup (Fin 6))),
      H.index = 2 ∧ Nonempty (H ≃* Equiv.Perm (Fin 6)) :=
  theorem_5_2_1_b

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.theorem_5_2_1 -/

/- BEGIN Theory.AutomorphismDefectHom -/
namespace GLS3.Chapter5

/-- If the defects `α(s a) * (s a)⁻¹` are central, they form a homomorphism
into the center. -/
@[expose]
public def automorphismDefectHom
    {P K : Type*} [Group P] [Group K]
    (s : P →* K) (alpha : MulAut K)
    (hc : ∀ a : P, alpha (s a) * (s a)⁻¹ ∈ Subgroup.center K) :
    P →* Subgroup.center K where
  toFun a := ⟨alpha (s a) * (s a)⁻¹, hc a⟩
  map_one' := by ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change alpha (s (a * b)) * (s (a * b))⁻¹ =
      (alpha (s a) * (s a)⁻¹) * (alpha (s b) * (s b)⁻¹)
    rw [map_mul, map_mul, mul_inv_rev]
    have hbCenter := hc b
    have hba : (alpha (s a) * (s a)⁻¹) *
        (alpha (s b) * (s b)⁻¹) =
          (alpha (s b) * (s b)⁻¹) * (alpha (s a) * (s a)⁻¹) :=
      Subgroup.mem_center_iff.mp hbCenter _
    calc
      alpha (s a) * alpha (s b) * ((s b)⁻¹ * (s a)⁻¹) =
          alpha (s a) * (alpha (s b) * (s b)⁻¹) * (s a)⁻¹ := by
            simp only [mul_assoc]
      _ = (alpha (s b) * (s b)⁻¹) *
          (alpha (s a) * (s a)⁻¹) := by
            rw [Subgroup.mem_center_iff.mp hbCenter (alpha (s a))]
            simp only [mul_assoc]
      _ = (alpha (s a) * (s a)⁻¹) *
          (alpha (s b) * (s b)⁻¹) := hba.symm

end GLS3.Chapter5
/- END Theory.AutomorphismDefectHom -/

/- BEGIN Theory.Centralizer -/
universe __ch5_Centralizer_u

namespace GLS3.Chapter5

/-- The points lying in cycles of length `i` for a permutation. -/
public def orbitLengthSet {Ω : Type __ch5_Centralizer_u} (x : Equiv.Perm Ω) (i : ℕ) : Set Ω :=
  (fun ω ↦ Function.minimalPeriod x ω) ⁻¹' {i}

/-- Lemma 5.2.2(a): a finite permutation set is the disjoint union of the
subsets consisting of points in cycles of each possible length. -/
public theorem theorem_5_2_2_a {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω) :
    (⋃ i ∈ Finset.Icc 1 (Fintype.card Ω), orbitLengthSet x i) = Set.univ ∧
      (↑(Finset.Icc 1 (Fintype.card Ω)) : Set ℕ).PairwiseDisjoint
        (orbitLengthSet x) := by
  constructor
  · apply Set.eq_univ_of_forall
    intro ω
    let i := Function.minimalPeriod x ω
    have hi_pos : 1 ≤ i := by
      exact Function.minimalPeriod_pos_of_mem_periodicPts
        (x.injective.mem_periodicPts ω)
    have hi_le : i ≤ Fintype.card Ω := Function.minimalPeriod_le_card
    have hi : i ∈ Finset.Icc 1 (Fintype.card Ω) :=
      Finset.mem_Icc.mpr ⟨hi_pos, hi_le⟩
    refine Set.mem_iUnion_of_mem i ?_
    refine Set.mem_iUnion_of_mem hi ?_
    change Function.minimalPeriod x ω ∈ ({i} : Set ℕ)
    exact Set.mem_singleton i
  · exact Set.pairwiseDisjoint_fiber
      (fun ω ↦ Function.minimalPeriod x ω)
      (↑(Finset.Icc 1 (Fintype.card Ω)) : Set ℕ)

public theorem minimalPeriod_eq_of_commute
    {Ω : Type*} [Finite Ω] (x y : Equiv.Perm Ω) (h : Commute y x) (ω : Ω) :
    Function.minimalPeriod x (y ω) = Function.minimalPeriod x ω := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  have hfun : Function.Commute (y : Ω → Ω) x := by
    intro z
    exact congrArg (fun q : Equiv.Perm Ω ↦ q z) h.eq
  have hinvfun : Function.Commute ((y⁻¹ : Equiv.Perm Ω) : Ω → Ω) x := by
    intro z
    exact congrArg (fun q : Equiv.Perm Ω ↦ q z) h.inv_left.eq
  constructor
  · intro hyω
    have hback := hyω.map hinvfun.semiconj
    simpa using hback
  · intro hω
    exact hω.map hfun.semiconj

public theorem orbitLengthSet_apply_iff
    {Ω : Type*} [Finite Ω] (x : Equiv.Perm Ω) (i : ℕ) (ω : Ω) :
    x ω ∈ orbitLengthSet x i ↔ ω ∈ orbitLengthSet x i := by
  simp only [orbitLengthSet, Set.mem_preimage, Set.mem_singleton_iff]
  rw [Function.minimalPeriod_apply (x.injective.mem_periodicPts ω)]

public theorem orbitLengthSet_apply_iff_of_commute
    {Ω : Type*} [Finite Ω] (x y : Equiv.Perm Ω) (h : Commute y x)
    (i : ℕ) (ω : Ω) :
    y ω ∈ orbitLengthSet x i ↔ ω ∈ orbitLengthSet x i := by
  simp only [orbitLengthSet, Set.mem_preimage, Set.mem_singleton_iff]
  rw [minimalPeriod_eq_of_commute x y h ω]

/-- The restriction of a permutation to the points in cycles of length `i`. -/
@[expose]
public def orbitLengthPerm
    {Ω : Type __ch5_Centralizer_u} [Finite Ω] (x : Equiv.Perm Ω) (i : ℕ) :
    Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i} :=
  x.subtypePerm fun ω ↦ by
    rw [Function.minimalPeriod_apply (x.injective.mem_periodicPts ω)]

public theorem orbitLengthPerm_iterate_coe
    {Ω : Type __ch5_Centralizer_u} [Finite Ω] (x : Equiv.Perm Ω) (i n : ℕ)
    (ω : {ω : Ω // Function.minimalPeriod x ω = i}) :
    (((orbitLengthPerm x i : _ → _)^[n]) ω).1 = (x^[n]) ω.1 := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

public theorem minimalPeriod_orbitLengthPerm
    {Ω : Type __ch5_Centralizer_u} [Finite Ω] (x : Equiv.Perm Ω) (i : ℕ)
    (ω : {ω : Ω // Function.minimalPeriod x ω = i}) :
    Function.minimalPeriod (orbitLengthPerm x i) ω = i := by
  have hperiod : Function.minimalPeriod (orbitLengthPerm x i) ω =
      Function.minimalPeriod x ω := by
    rw [Function.minimalPeriod_eq_minimalPeriod_iff]
    intro n
    constructor
    · intro h
      change (x^[n]) ω.1 = ω.1
      rw [← orbitLengthPerm_iterate_coe x i n ω]
      exact congrArg Subtype.val h
    · intro h
      change ((orbitLengthPerm x i : _ → _)^[n]) ω = ω
      apply Subtype.ext
      rw [orbitLengthPerm_iterate_coe x i n ω]
      exact h
  exact hperiod.trans ω.2

/-- Restrict a centralizing permutation to every orbit-length block. -/
@[expose]
public noncomputable def centralizerToOrbitLengthCentralizers
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω) :
    Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) →*
      (∀ i : ℕ, Subgroup.centralizer ({orbitLengthPerm x i} :
        Set (Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i}))) where
  toFun y i := by
    have hcomm : Commute (y.1 : Equiv.Perm Ω) x :=
      Subgroup.mem_centralizer_singleton_iff.mp y.property
    refine ⟨y.1.subtypePerm (fun ω ↦ ?_), ?_⟩
    · rw [minimalPeriod_eq_of_commute x y.1 hcomm ω]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Equiv.ext
      intro ω
      apply Subtype.ext
      change y.1 (x ω.1) = x (y.1 ω.1)
      exact congrArg (fun q : Equiv.Perm Ω ↦ q ω.1) hcomm.eq
  map_one' := by
    ext i ω
    rfl
  map_mul' y z := by
    ext i ω
    rfl

public theorem centralizerToOrbitLengthCentralizers_apply
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) (i : ℕ)
    (ω : {ω : Ω // Function.minimalPeriod x ω = i}) :
    (((centralizerToOrbitLengthCentralizers x) y i).1 ω).1 = y.1 ω.1 := rfl

/-- Assemble commuting permutations on the orbit-length blocks into a
permutation centralizing `x`. -/
@[expose]
public noncomputable def orbitLengthCentralizersToCentralizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω) :
    (∀ i : ℕ, Subgroup.centralizer ({orbitLengthPerm x i} :
      Set (Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i}))) →*
      Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) where
  toFun g := by
    let y : Equiv.Perm Ω :=
      DomMulAct.stabilizerEquiv_invFun_aux (fun i ↦ (g i).1)
    refine ⟨y, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro ω
    change DomMulAct.stabilizerEquiv_invFun (fun i ↦ (g i).1) (x ω) =
      x (DomMulAct.stabilizerEquiv_invFun (fun i ↦ (g i).1) ω)
    let i := Function.minimalPeriod x ω
    have hx : Function.minimalPeriod x (x ω) = i := by
      exact Function.minimalPeriod_apply (x.injective.mem_periodicPts ω)
    rw [DomMulAct.stabilizerEquiv_invFun_eq _ hx]
    change ((g i).1 ⟨x ω, hx⟩).1 = x (((g i).1 ⟨ω, rfl⟩).1)
    have hcomm : Commute (g i).1 (orbitLengthPerm x i) :=
      Subgroup.mem_centralizer_singleton_iff.mp (g i).property
    have heval := congrArg
      (fun q : Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i} ↦ q ⟨ω, rfl⟩)
      hcomm.eq
    simpa [orbitLengthPerm] using congrArg Subtype.val heval
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro ω
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro ω
    change DomMulAct.stabilizerEquiv_invFun (fun i ↦ ((g * h) i).1) ω =
      DomMulAct.stabilizerEquiv_invFun (fun i ↦ (g i).1)
        (DomMulAct.stabilizerEquiv_invFun (fun i ↦ (h i).1) ω)
    rw [DomMulAct.stabilizerEquiv_invFun_eq _
      (DomMulAct.comp_stabilizerEquiv_invFun (fun i ↦ (h i).1) ω)]
    rfl

public theorem orbitLengthCentralizersToCentralizer_apply
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (g : ∀ i : ℕ, Subgroup.centralizer ({orbitLengthPerm x i} :
      Set (Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i}))) (ω : Ω) :
    ((orbitLengthCentralizersToCentralizer x) g).1 ω =
      ((g (Function.minimalPeriod x ω)).1 ⟨ω, rfl⟩).1 := rfl

/-- Lemma 5.2.2(b): the centralizer of a permutation is the direct product of
the centralizers of its restrictions to the orbit-length blocks. -/
@[expose]
public noncomputable def theorem_5_2_2_b
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω) :
    Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) ≃*
      (∀ i : ℕ, Subgroup.centralizer ({orbitLengthPerm x i} :
        Set (Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i}))) := by
  refine (centralizerToOrbitLengthCentralizers x).toMulEquiv
    (orbitLengthCentralizersToCentralizer x) ?_ ?_
  · apply MonoidHom.ext
    intro y
    apply Subtype.ext
    apply DFunLike.ext _ _
    intro ω
    change DomMulAct.stabilizerEquiv_invFun
      (fun i ↦ ((centralizerToOrbitLengthCentralizers x) y i).1) ω = y.1 ω
    rfl
  · apply MonoidHom.ext
    intro g
    funext i
    apply Subtype.ext
    apply DFunLike.ext _ _
    intro ω
    rcases ω with ⟨ω, rfl⟩
    apply Subtype.ext
    change (((centralizerToOrbitLengthCentralizers x)
      ((orbitLengthCentralizersToCentralizer x) g)
        (Function.minimalPeriod x ω)).1 ⟨ω, rfl⟩).1 =
          ((g (Function.minimalPeriod x ω)).1 ⟨ω, rfl⟩).1
    rw [centralizerToOrbitLengthCentralizers_apply,
      orbitLengthCentralizersToCentralizer_apply]

/-- The component of a centralizing permutation supported on the points in
cycles of length `i`. -/
@[expose]
public noncomputable def orbitLengthComponent
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) (i : ℕ) :
    Equiv.Perm Ω := by
  classical
  have hcomm : Commute (y.1 : Equiv.Perm Ω) x :=
    Subgroup.mem_centralizer_singleton_iff.mp y.property
  exact Equiv.Perm.ofSubtype
    (y.1.subtypePerm (orbitLengthSet_apply_iff_of_commute x y.1 hcomm i))

public theorem orbitLengthComponent_apply_of_mem
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) (i : ℕ) (ω : Ω)
    (hω : ω ∈ orbitLengthSet x i) :
    orbitLengthComponent x y i ω = y.1 ω := by
  classical
  simp [orbitLengthComponent, Equiv.Perm.ofSubtype_apply_of_mem, hω]

public theorem orbitLengthComponent_apply_of_not_mem
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) (i : ℕ) (ω : Ω)
    (hω : ω ∉ orbitLengthSet x i) :
    orbitLengthComponent x y i ω = ω := by
  classical
  simp [orbitLengthComponent, Equiv.Perm.ofSubtype_apply_of_not_mem, hω]

public theorem orbitLengthComponent_commute
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) (i : ℕ) :
    Commute (orbitLengthComponent x y i) x := by
  have hcomm : Commute (y.1 : Equiv.Perm Ω) x :=
    Subgroup.mem_centralizer_singleton_iff.mp y.property
  apply Equiv.ext
  intro ω
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases hω : ω ∈ orbitLengthSet x i
  · rw [orbitLengthComponent_apply_of_mem x y i ω hω]
    rw [orbitLengthComponent_apply_of_mem x y i (x ω)
      ((orbitLengthSet_apply_iff x i ω).mpr hω)]
    exact congrArg (fun q : Equiv.Perm Ω ↦ q ω) hcomm.eq
  · rw [orbitLengthComponent_apply_of_not_mem x y i ω hω]
    rw [orbitLengthComponent_apply_of_not_mem x y i (x ω)
      ((not_congr (orbitLengthSet_apply_iff x i ω)).mpr hω)]

/-- The short exact sequence obtained from the action of the centralizer of a
permutation on its cycle factors. -/
@[expose]
public noncomputable def cycleCentralizerExtension
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    GroupExtension (Equiv.Perm.OnCycleFactors.toPermHom x).ker
      (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
      (Equiv.Perm.OnCycleFactors.toPermHom x).range where
  inl := Subgroup.subtype _
  rightHom := (Equiv.Perm.OnCycleFactors.toPermHom x).codRestrict _
    (fun y ↦ ⟨y, rfl⟩)
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      exact z.property
    · intro hy
      refine ⟨⟨y, ?_⟩, rfl⟩
      exact congrArg Subtype.val hy
  rightHom_surjective := by
    rintro ⟨z, y, rfl⟩
    exact ⟨y, rfl⟩

/-- Identify the actual range of the action on cycle factors with Mathlib's
explicit subgroup of cycle-length-preserving permutations. -/
@[expose]
public noncomputable def cycleActionRangeToExplicitRange
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (Equiv.Perm.OnCycleFactors.toPermHom x).range →*
      Equiv.Perm.OnCycleFactors.range_toPermHom' x where
  toFun z := ⟨z.1, by
    rw [← Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom']
    exact z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual cycle-action image is isomorphic to the explicit subgroup of
cycle-length-preserving permutations. -/
@[expose]
public noncomputable def cycleActionRangeMulEquivExplicitRange
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (Equiv.Perm.OnCycleFactors.toPermHom x).range ≃*
      Equiv.Perm.OnCycleFactors.range_toPermHom' x :=
  MulEquiv.ofBijective (cycleActionRangeToExplicitRange x) ⟨by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun q : Equiv.Perm.OnCycleFactors.range_toPermHom' x ↦ q.1) hyz
  , by
    intro z
    refine ⟨⟨z.1, ?_⟩, rfl⟩
    rw [Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom']
    exact z.2⟩

public theorem cycleFactor_support_card_eq_orderOf_of_primeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) :
    c.1.support.card = orderOf x := by
  have hc : c.1.support.card ∈ x.cycleType := by
    simp only [Equiv.Perm.cycleType_def, Multiset.mem_map, Finset.mem_val]
    exact ⟨c.1, c.2, rfl⟩
  exact (hx.eq_one_or_self_of_dvd _
    (Equiv.Perm.dvd_of_mem_cycleType hc)).resolve_left
      (Equiv.Perm.one_lt_of_mem_cycleType hc).ne'

public theorem minimalPeriod_eq_cycleFactor_support_card
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (c : x.cycleFactorsFinset) (ω : Ω) (hω : ω ∈ c.1.support) :
    Function.minimalPeriod x ω = c.1.support.card := by
  let hcycle := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.2
  apply Nat.dvd_antisymm
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    change (x ^ c.1.support.card) ω = ω
    exact (hcycle.pow_apply_eq hω).mpr dvd_rfl
  · have hperiod := Function.isPeriodicPt_minimalPeriod x ω
    change (x ^ Function.minimalPeriod x ω) ω = ω at hperiod
    exact (hcycle.pow_apply_eq hω).mp hperiod

public theorem orbitLengthPerm_cycleFactor_support_card
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ)
    (c : (orbitLengthPerm x i).cycleFactorsFinset) :
    c.1.support.card = i := by
  classical
  obtain ⟨ω, hω⟩ := Equiv.Perm.IsCycle.nonempty_support
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
  exact (minimalPeriod_eq_cycleFactor_support_card (orbitLengthPerm x i) c ω hω).symm.trans
    (minimalPeriod_orbitLengthPerm x i ω)

public theorem cycleActionExplicitRange_orbitLengthPerm_eq_top
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ) :
    Equiv.Perm.OnCycleFactors.range_toPermHom' (orbitLengthPerm x i) = ⊤ := by
  classical
  ext y
  rw [Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff]
  simp only [Subgroup.mem_top, iff_true]
  intro c
  rw [orbitLengthPerm_cycleFactor_support_card x i,
    orbitLengthPerm_cycleFactor_support_card x i]

/-- On an orbit-length block, every cycle factor has the same length, hence
the cycle-action image is the full symmetric group on the cycle factors. -/
@[expose]
public noncomputable def orbitLengthCycleActionRangeMulEquivPerm
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ) :
    (Equiv.Perm.OnCycleFactors.toPermHom (orbitLengthPerm x i)).range ≃*
      Equiv.Perm (orbitLengthPerm x i).cycleFactorsFinset := by
  classical
  let f := Subgroup.subtype
    (Equiv.Perm.OnCycleFactors.toPermHom (orbitLengthPerm x i)).range
  refine MulEquiv.ofBijective f ⟨Subtype.val_injective, ?_⟩
  intro y
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom',
    cycleActionExplicitRange_orbitLengthPerm_eq_top x i]
  exact Subgroup.mem_top y

/-- The base group of independent rotations of the nontrivial cycle factors. -/
public abbrev CycleRotationGroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
    (c : x.cycleFactorsFinset) → Subgroup.zpowers c.1

public theorem orbitLengthCycleRotationGroup_pow_eq_one
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ)
    (a : CycleRotationGroup (orbitLengthPerm x i)) : a ^ i = 1 := by
  funext c
  apply Subtype.ext
  change (a c).1 ^ i = 1
  rw [← orderOf_dvd_iff_pow_eq_one]
  have hc : orderOf c.1 = i :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf.trans
      (orbitLengthPerm_cycleFactor_support_card x i c)
  simpa only [hc] using orderOf_dvd_of_mem_zpowers (a c).2

public theorem orbitLengthCycleRotationGroup_card
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ) :
    Nat.card (CycleRotationGroup (orbitLengthPerm x i)) =
      i ^ Fintype.card (orbitLengthPerm x i).cycleFactorsFinset := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp_rw [Fintype.card_zpowers]
  apply Finset.prod_eq_pow_card
  intro c _
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf.trans
    (orbitLengthPerm_cycleFactor_support_card x i c)

public theorem cycleActionExplicitRange_eq_top_of_primeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Equiv.Perm.OnCycleFactors.range_toPermHom' x = ⊤ := by
  ext y
  rw [Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff]
  simp only [Subgroup.mem_top, iff_true]
  intro c
  rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x hx,
    cycleFactor_support_card_eq_orderOf_of_primeOrder x hx]

/-- For a permutation of prime order, every nontrivial cycle has the same
length, so the induced action quotient is the full symmetric group on the
set of cycle factors. -/
@[expose]
public noncomputable def cycleActionRangeMulEquivPermOfPrimeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    (Equiv.Perm.OnCycleFactors.toPermHom x).range ≃*
      Equiv.Perm x.cycleFactorsFinset := by
  let f := Subgroup.subtype (Equiv.Perm.OnCycleFactors.toPermHom x).range
  refine MulEquiv.ofBijective f ⟨Subtype.val_injective, ?_⟩
  intro y
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom',
    cycleActionExplicitRange_eq_top_of_primeOrder x hx]
  exact Subgroup.mem_top y

/-- The explicit rotation kernel in the cycle-wreath description: arbitrary
permutations of the fixed points, together with one power of each cycle. -/
public abbrev CycleWreathKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
    Equiv.Perm (Function.fixedPoints x) ×
      ((c : x.cycleFactorsFinset) → Subgroup.zpowers c.1)

public theorem cycleRotationGroup_mul_comm
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (a b : CycleRotationGroup x) : a * b = b * a := by
  funext c
  exact (inferInstance : IsMulCommutative (Subgroup.zpowers c.1)).is_comm.comm
    (a c) (b c)

public theorem cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : CycleRotationGroup x) :
    a ^ orderOf x = 1 := by
  funext c
  apply Subtype.ext
  change (a c).1 ^ orderOf x = 1
  rw [← orderOf_dvd_iff_pow_eq_one]
  have hc : orderOf c.1 = orderOf x :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf.trans
      (cycleFactor_support_card_eq_orderOf_of_primeOrder x hx c)
  rw [← hc]
  exact orderOf_dvd_of_mem_zpowers (a c).2

public theorem cycleRotationGroup_card_of_primeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Nat.card (CycleRotationGroup x) =
      orderOf x ^ Fintype.card x.cycleFactorsFinset := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp_rw [Fintype.card_zpowers]
  apply Finset.prod_eq_pow_card
  intro c _
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf.trans
    (cycleFactor_support_card_eq_orderOf_of_primeOrder x hx c)

/-- Map the explicit cycle-rotation parameters to the kernel of the action of
the centralizer on the cycle factors. -/
@[expose]
public noncomputable def cycleWreathKernelToKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    CycleWreathKernel x →* (Equiv.Perm.OnCycleFactors.toPermHom x).ker where
  toFun z := by
    let y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) :=
      ⟨Equiv.Perm.OnCycleFactors.kerParam x z,
        Equiv.Perm.OnCycleFactors.kerParam_range_le_centralizer (g := x) (by
          exact ⟨z, rfl⟩)⟩
    refine ⟨y, ?_⟩
    have hz : Equiv.Perm.OnCycleFactors.kerParam x z ∈
        (Equiv.Perm.OnCycleFactors.toPermHom x).ker.map
          (Subgroup.subtype _) := by
      rw [← Equiv.Perm.OnCycleFactors.kerParam_range_eq]
      exact ⟨z, rfl⟩
    rcases hz with ⟨w, hw, hwz⟩
    have hyw : y = w := by
      apply Subtype.ext
      exact hwz.symm
    exact hyw ▸ hw
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (Equiv.Perm.OnCycleFactors.kerParam x)
  map_mul' z w := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (Equiv.Perm.OnCycleFactors.kerParam x) z w

public theorem cycleWreathKernelToKernel_coe
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (z : CycleWreathKernel x) :
    (((cycleWreathKernelToKernel x) z).1.1 : Equiv.Perm Ω) =
      Equiv.Perm.OnCycleFactors.kerParam x z := rfl

/-- Include the pure cycle-rotation factor into the explicit wreath kernel. -/
@[expose]
public def cycleRotationToWreathKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    CycleRotationGroup x →* CycleWreathKernel x where
  toFun a := (1, a)
  map_one' := rfl
  map_mul' _ _ := rfl

public theorem cycleRotationToWreathKernel_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Function.Injective (cycleRotationToWreathKernel x) := by
  intro a b hab
  exact congrArg Prod.snd hab

/-- The kernel of the cycle action is exactly the fixed-point symmetric group
times the product of the cyclic rotation groups of the cycle factors. -/
@[expose]
public noncomputable def cycleWreathKernelMulEquiv
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    CycleWreathKernel x ≃*
      (Equiv.Perm.OnCycleFactors.toPermHom x).ker :=
  MulEquiv.ofBijective (cycleWreathKernelToKernel x) ⟨by
    intro z w hzw
    apply Equiv.Perm.OnCycleFactors.kerParam_injective x
    have hzw' := congrArg (fun q ↦ (q.1.1 : Equiv.Perm Ω)) hzw
    rw [cycleWreathKernelToKernel_coe, cycleWreathKernelToKernel_coe] at hzw'
    exact hzw'
  , by
    intro y
    have hy : (y.1.1 : Equiv.Perm Ω) ∈
        (Equiv.Perm.OnCycleFactors.kerParam x).range := by
      rw [Equiv.Perm.OnCycleFactors.kerParam_range_eq]
      exact ⟨y.1, y.2, rfl⟩
    rcases hy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [cycleWreathKernelToKernel_coe]
    exact hz⟩

/-- Embed the independent cycle rotations as a subgroup of the permutation
centralizer. -/
@[expose]
public noncomputable def cycleRotationToCentralizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    CycleRotationGroup x →*
      Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) :=
  (cycleCentralizerExtension x).inl.comp
    ((cycleWreathKernelToKernel x).comp (cycleRotationToWreathKernel x))

public theorem cycleRotationToCentralizer_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Function.Injective (cycleRotationToCentralizer x) :=
  (cycleCentralizerExtension x).inl_injective.comp
    ((cycleWreathKernelMulEquiv x).injective.comp
      (cycleRotationToWreathKernel_injective x))

/-- The elementary-abelian rotation subgroup in a prime-order permutation
centralizer. -/
@[expose]
public noncomputable def cycleRotationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) :=
  (cycleRotationToCentralizer x).range

@[expose]
public noncomputable def cycleRotationGroupMulEquivSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    CycleRotationGroup x ≃* cycleRotationSubgroup x :=
  MonoidHom.ofInjective (cycleRotationToCentralizer_injective x)

/-- Include arbitrary permutations of the fixed points into the explicit
wreath kernel. -/
@[expose]
public def fixedPointPermToWreathKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Equiv.Perm (Function.fixedPoints x) →* CycleWreathKernel x where
  toFun a := (a, 1)
  map_one' := rfl
  map_mul' _ _ := rfl

public theorem fixedPointPermToWreathKernel_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Function.Injective (fixedPointPermToWreathKernel x) := by
  intro a b hab
  exact congrArg Prod.fst hab

/-- Embed the fixed-point symmetric group into the centralizer. -/
@[expose]
public noncomputable def fixedPointPermToCentralizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Equiv.Perm (Function.fixedPoints x) →*
      Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) :=
  (cycleCentralizerExtension x).inl.comp
    ((cycleWreathKernelToKernel x).comp (fixedPointPermToWreathKernel x))

public theorem fixedPointPermToCentralizer_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Function.Injective (fixedPointPermToCentralizer x) :=
  (cycleCentralizerExtension x).inl_injective.comp
    ((cycleWreathKernelMulEquiv x).injective.comp
      (fixedPointPermToWreathKernel_injective x))

/-- The subgroup of the centralizer supported on the fixed points. -/
@[expose]
public noncomputable def fixedPointPermutationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) :=
  (fixedPointPermToCentralizer x).range

@[expose]
public noncomputable def fixedPointPermMulEquivSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Equiv.Perm (Function.fixedPoints x) ≃*
      fixedPointPermutationSubgroup x :=
  MonoidHom.ofInjective (fixedPointPermToCentralizer_injective x)

/-- A multiplicative section of the action of the centralizer on the cycle
factors, obtained by choosing one base point in every cycle. -/
@[expose]
public noncomputable def cycleCentralizerSplitting
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (cycleCentralizerExtension x).Splitting := by
  let a := Classical.choice (Equiv.Perm.Basis.nonempty x)
  refine {
    __ := (Equiv.Perm.Basis.toCentralizer a).comp
      (cycleActionRangeToExplicitRange x)
    rightInverse_rightHom := ?_ }
  intro z
  apply Subtype.ext
  exact Equiv.Perm.Basis.toPermHom_apply_toCentralizer a
    (cycleActionRangeToExplicitRange x z)

/-- The subgroup of the centralizer induced by permuting the nontrivial cycle
factors through the chosen multiplicative section. -/
@[expose]
public noncomputable def cyclePermutationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) :=
  (cycleCentralizerSplitting x).toMonoidHom.range

/-- The cycle-action quotient is isomorphic to its section subgroup in the
centralizer. -/
@[expose]
public noncomputable def cycleActionRangeMulEquivCyclePermutationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (Equiv.Perm.OnCycleFactors.toPermHom x).range ≃*
      cyclePermutationSubgroup x :=
  MonoidHom.ofInjective
    (cycleCentralizerSplitting x).rightInverse_rightHom.injective

/-- The cycle-wreath-product model of a permutation centralizer: the kernel
of the action on cycles, semidirect the induced cycle permutation group. -/
public abbrev CycleWreathProduct
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
    (Equiv.Perm.OnCycleFactors.toPermHom x).ker ⋊[
      (cycleCentralizerSplitting x).conjAct]
        (Equiv.Perm.OnCycleFactors.toPermHom x).range

/-- Lemma 5.2.2(c): each orbit-length centralizer has its cycle wreath-product
decomposition. The action quotient consists precisely of the permutations of
the equal-length cycle factors. -/
@[expose]
public noncomputable def theorem_5_2_2_c
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) (i : ℕ) :
    Subgroup.centralizer ({orbitLengthPerm x i} :
      Set (Equiv.Perm {ω : Ω // Function.minimalPeriod x ω = i})) ≃*
        CycleWreathProduct (orbitLengthPerm x i) :=
  (cycleCentralizerSplitting (orbitLengthPerm x i)).semidirectProductMulEquiv.symm

public theorem mem_cycleRotationSubgroup_iff
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) :
    y ∈ cycleRotationSubgroup x ↔
      y ∈ (Equiv.Perm.OnCycleFactors.toPermHom x).ker ∧
        ∀ ω : Function.fixedPoints x, y.1 ω.1 = ω.1 := by
  constructor
  · rintro ⟨a, rfl⟩
    constructor
    · rw [MonoidHom.mem_ker]
      change (Equiv.Perm.OnCycleFactors.toPermHom x)
          ↑((cycleWreathKernelToKernel x) ((cycleRotationToWreathKernel x) a)) = 1
      exact congrArg Subtype.val
        ((cycleCentralizerExtension x).rightHom_inl
          ((cycleWreathKernelToKernel x) ((cycleRotationToWreathKernel x) a)))
    · intro ω
      change Equiv.Perm.OnCycleFactors.kerParam x (1, a) ω.1 = ω.1
      rw [Equiv.Perm.OnCycleFactors.kerParam_apply]
      have hω : x.cycleOf ω.1 ∉ x.cycleFactorsFinset := by
        rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
          Equiv.Perm.notMem_support]
        exact ω.2
      rw [dif_neg hω]
      exact Equiv.Perm.ofSubtype_apply_of_mem (1 : Equiv.Perm (Function.fixedPoints x)) ω.2
  · rintro ⟨hyker, hyfix⟩
    let yker : (Equiv.Perm.OnCycleFactors.toPermHom x).ker := ⟨y, hyker⟩
    obtain ⟨⟨__ch5_Centralizer_u, a⟩, hua⟩ := (cycleWreathKernelMulEquiv x).surjective yker
    have hu : __ch5_Centralizer_u = 1 := by
      apply Equiv.ext
      intro ω
      apply Subtype.ext
      have hval := congrArg
        (fun z : (Equiv.Perm.OnCycleFactors.toPermHom x).ker ↦ z.1.1 ω.1) hua
      change Equiv.Perm.OnCycleFactors.kerParam x (__ch5_Centralizer_u, a) ω.1 = y.1 ω.1 at hval
      rw [Equiv.Perm.OnCycleFactors.kerParam_apply] at hval
      have hω : x.cycleOf ω.1 ∉ x.cycleFactorsFinset := by
        rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
          Equiv.Perm.notMem_support]
        exact ω.2
      rw [dif_neg hω, Equiv.Perm.ofSubtype_apply_of_mem __ch5_Centralizer_u ω.2] at hval
      exact hval.trans (hyfix ω)
    subst __ch5_Centralizer_u
    refine ⟨a, ?_⟩
    change (cycleWreathKernelToKernel x) (1, a) = yker at hua
    change (cycleCentralizerExtension x).inl
      ((cycleWreathKernelToKernel x) (1, a)) = y
    exact congrArg Subtype.val hua

public theorem cyclePermutationSubgroup_fixes_fixedPoints
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (y : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hy : y ∈ cyclePermutationSubgroup x)
    (ω : Function.fixedPoints x) : y.1 ω.1 = ω.1 := by
  rcases hy with ⟨q, rfl⟩
  change Equiv.Perm.Basis.ofPermHomFun
    (Classical.choice (Equiv.Perm.Basis.nonempty x))
      (cycleActionRangeToExplicitRange x q) ω.1 = ω.1
  exact Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints _ _ ω.2

public theorem cycleRotationSubgroup_inf_cyclePermutationSubgroup_eq_bot
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    cycleRotationSubgroup x ⊓ cyclePermutationSubgroup x = ⊥ := by
  apply le_antisymm
  · intro y hy
    rcases hy.2 with ⟨q, rfl⟩
    have hyker := (mem_cycleRotationSubgroup_iff x _).mp hy.1 |>.1
    have hker := MonoidHom.mem_ker.mp hyker
    have hsection := congrArg Subtype.val
      ((cycleCentralizerSplitting x).rightHom_splitting q)
    have hq : q = 1 := by
      apply Subtype.ext
      exact hsection.symm.trans hker
    subst q
    simp
  · exact bot_le

public theorem cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    cyclePermutationSubgroup x ≤ Subgroup.normalizer (cycleRotationSubgroup x) := by
  rw [Subgroup.le_normalizer_iff]
  intro l hl r hr
  apply (mem_cycleRotationSubgroup_iff x _).mpr
  constructor
  · have hrker := (mem_cycleRotationSubgroup_iff x r).mp hr |>.1
    exact (inferInstance : (Equiv.Perm.OnCycleFactors.toPermHom x).ker.Normal).conj_mem
      r hrker l
  · intro ω
    have hlfix := cyclePermutationSubgroup_fixes_fixedPoints x l hl ω
    have hlinv : l.1⁻¹ ω.1 = ω.1 :=
      l.1.symm_apply_eq.mpr hlfix.symm
    have hrfix := (mem_cycleRotationSubgroup_iff x r).mp hr |>.2 ω
    change l.1 (r.1 (l.1⁻¹ ω.1)) = ω.1
    rw [hlinv, hrfix, hlfix]

public theorem cycleRotationSubgroup_normal_subgroupOf_sup_cyclePermutationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    ((cycleRotationSubgroup x).subgroupOf
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x)).Normal := by
  rw [sup_comm]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x)

public theorem fixedPointPermToCentralizer_coe
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (__ch5_Centralizer_u : Equiv.Perm (Function.fixedPoints x)) :
    ((fixedPointPermToCentralizer x) __ch5_Centralizer_u).1 = Equiv.Perm.ofSubtype __ch5_Centralizer_u := by
  apply Equiv.ext
  intro ω
  change Equiv.Perm.OnCycleFactors.kerParam x (__ch5_Centralizer_u, 1) ω =
    Equiv.Perm.ofSubtype __ch5_Centralizer_u ω
  rw [Equiv.Perm.OnCycleFactors.kerParam_apply]
  split_ifs with hω
  · rw [Pi.one_apply, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    intro hfix
    have hsupport : ω ∈ x.support :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mp hω
    exact (Equiv.Perm.notMem_support.mpr
      (Function.mem_fixedPoints_iff.mp hfix)) hsupport
  · rfl

public theorem fixedPointPermutationSubgroup_commutes_cycleRotationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (i : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hi : i ∈ fixedPointPermutationSubgroup x)
    (r : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr : r ∈ cycleRotationSubgroup x) : Commute i r := by
  rcases hi with ⟨__ch5_Centralizer_u, rfl⟩
  rcases hr with ⟨a, rfl⟩
  let f := (cycleCentralizerExtension x).inl.comp (cycleWreathKernelToKernel x)
  change Commute (f (__ch5_Centralizer_u, 1)) (f (1, a))
  apply Commute.map
  ext <;> simp

public theorem fixedPointPermutationSubgroup_commutes_cyclePermutationSubgroup
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (i : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hi : i ∈ fixedPointPermutationSubgroup x)
    (l : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hl : l ∈ cyclePermutationSubgroup x) : Commute i l := by
  rcases hi with ⟨__ch5_Centralizer_u, rfl⟩
  apply Subtype.ext
  apply Equiv.ext
  intro ω
  change ((fixedPointPermToCentralizer x) __ch5_Centralizer_u).1 (l.1 ω) =
    l.1 (((fixedPointPermToCentralizer x) __ch5_Centralizer_u).1 ω)
  rw [fixedPointPermToCentralizer_coe]
  by_cases hω : ω ∈ Function.fixedPoints x
  · let ω' : Function.fixedPoints x := ⟨ω, hω⟩
    have hlω := cyclePermutationSubgroup_fixes_fixedPoints x l hl ω'
    have hluω := cyclePermutationSubgroup_fixes_fixedPoints x l hl (__ch5_Centralizer_u ω')
    rw [hlω, Equiv.Perm.ofSubtype_apply_of_mem __ch5_Centralizer_u hω]
    exact hluω.symm
  · have hlω : l.1 ω ∉ Function.fixedPoints x := by
      intro hlω
      apply hω
      rw [Function.mem_fixedPoints_iff] at hlω ⊢
      have hcomm : Commute l.1 x :=
        Subgroup.mem_centralizer_singleton_iff.mp l.2
      apply l.1.injective
      exact (congrArg (fun q : Equiv.Perm Ω ↦ q ω) hcomm.eq).trans hlω
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem __ch5_Centralizer_u hlω,
      Equiv.Perm.ofSubtype_apply_of_not_mem __ch5_Centralizer_u hω]

public theorem fixedPointPermutationSubgroup_inf_cycleRotationSubgroup_eq_bot
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ⊓ cycleRotationSubgroup x = ⊥ := by
  apply le_antisymm
  · intro y hy
    rcases hy.1 with ⟨__ch5_Centralizer_u, rfl⟩
    rcases hy.2 with ⟨a, ha⟩
    let f := (cycleCentralizerExtension x).inl.comp (cycleWreathKernelToKernel x)
    have ha' : f (1, a) = f (__ch5_Centralizer_u, 1) := by exact ha
    have hf : Function.Injective f :=
      (cycleCentralizerExtension x).inl_injective.comp
        (cycleWreathKernelMulEquiv x).injective
    have hua : (1, a) = (__ch5_Centralizer_u, 1) := hf ha'
    have hu : __ch5_Centralizer_u = 1 := (congrArg Prod.fst hua).symm
    subst __ch5_Centralizer_u
    simp
  · exact bot_le

public theorem fixedPointPermutationSubgroup_sup_cycleRotationSubgroup_eq_cycleKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ⊔ cycleRotationSubgroup x =
      (cycleCentralizerExtension x).inl.range := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · rintro y ⟨__ch5_Centralizer_u, rfl⟩
      refine ⟨(cycleWreathKernelToKernel x) (__ch5_Centralizer_u, 1), ?_⟩
      rfl
    · rintro y ⟨a, rfl⟩
      refine ⟨(cycleWreathKernelToKernel x) (1, a), ?_⟩
      rfl
  · rintro y ⟨k, rfl⟩
    generalize hza : (cycleWreathKernelMulEquiv x).symm k = za
    rcases za with ⟨__ch5_Centralizer_u, a⟩
    have hk : (cycleWreathKernelToKernel x) (__ch5_Centralizer_u, a) = k := by
      change (cycleWreathKernelMulEquiv x) (__ch5_Centralizer_u, a) = k
      rw [← hza]
      exact (cycleWreathKernelMulEquiv x).apply_symm_apply k
    rw [← hk]
    have hprod :
        (cycleCentralizerExtension x).inl ((cycleWreathKernelToKernel x) (__ch5_Centralizer_u, a)) =
          (fixedPointPermToCentralizer x) __ch5_Centralizer_u * (cycleRotationToCentralizer x) a := by
      let f := (cycleCentralizerExtension x).inl.comp (cycleWreathKernelToKernel x)
      change f (__ch5_Centralizer_u, a) = f (__ch5_Centralizer_u, 1) * f (1, a)
      rw [show (__ch5_Centralizer_u, a) = (__ch5_Centralizer_u, 1) * (1, a) by rfl, map_mul]
    rw [hprod]
    exact (fixedPointPermutationSubgroup x ⊔ cycleRotationSubgroup x).mul_mem
      ((le_sup_left : fixedPointPermutationSubgroup x ≤
        fixedPointPermutationSubgroup x ⊔ cycleRotationSubgroup x) ⟨__ch5_Centralizer_u, rfl⟩)
      ((le_sup_right : cycleRotationSubgroup x ≤
        fixedPointPermutationSubgroup x ⊔ cycleRotationSubgroup x) ⟨a, rfl⟩)

public theorem cycleKernel_sup_cyclePermutationSubgroup_eq_top
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (cycleCentralizerExtension x).inl.range ⊔ cyclePermutationSubgroup x = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := (cycleCentralizerSplitting x).semidirectProductMulEquiv.surjective y
  rcases z with ⟨k, q⟩
  change (cycleCentralizerExtension x).inl k * (cycleCentralizerSplitting x) q ∈
    (cycleCentralizerExtension x).inl.range ⊔ cyclePermutationSubgroup x
  exact ((cycleCentralizerExtension x).inl.range ⊔ cyclePermutationSubgroup x).mul_mem
    ((le_sup_left : (cycleCentralizerExtension x).inl.range ≤
      (cycleCentralizerExtension x).inl.range ⊔ cyclePermutationSubgroup x) ⟨k, rfl⟩)
    ((le_sup_right : cyclePermutationSubgroup x ≤
      (cycleCentralizerExtension x).inl.range ⊔ cyclePermutationSubgroup x) ⟨q, rfl⟩)

public theorem fixedPointPermutationSubgroup_sup_rotation_sup_permutation_eq_top
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ⊔
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) = ⊤ := by
  rw [← sup_assoc,
    fixedPointPermutationSubgroup_sup_cycleRotationSubgroup_eq_cycleKernel,
    cycleKernel_sup_cyclePermutationSubgroup_eq_top]

public theorem fixedPointPermutationSubgroup_le_centralizer_rotation_sup_permutation
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ≤
      Subgroup.centralizer
        ((cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x :
          Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) : Set _) := by
  rw [Subgroup.le_centralizer_iff]
  apply sup_le
  · intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact (fixedPointPermutationSubgroup_commutes_cycleRotationSubgroup x i hi r hr).eq
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact (fixedPointPermutationSubgroup_commutes_cyclePermutationSubgroup x i hi l hl).eq

public theorem fixedPointPermutationSubgroup_le_cycleActionKernel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ≤
      (Equiv.Perm.OnCycleFactors.toPermHom x).ker := by
  rintro y ⟨__ch5_Centralizer_u, rfl⟩
  rw [MonoidHom.mem_ker]
  change (Equiv.Perm.OnCycleFactors.toPermHom x)
      ↑((cycleWreathKernelToKernel x) (__ch5_Centralizer_u, 1)) = 1
  exact congrArg Subtype.val
    ((cycleCentralizerExtension x).rightHom_inl
      ((cycleWreathKernelToKernel x) (__ch5_Centralizer_u, 1)))

public theorem fixedPointPermutationSubgroup_inf_rotation_sup_permutation_eq_bot
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ⊓
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) = ⊥ := by
  apply le_antisymm
  · intro y hy
    have hymul := hy.2
    change y ∈ (↑(cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) :
      Set (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) at hymul
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x)] at hymul
    rcases hymul with ⟨r, hr, l, hl, rfl⟩
    rcases hl with ⟨q, rfl⟩
    have hyker := MonoidHom.mem_ker.mp
      (fixedPointPermutationSubgroup_le_cycleActionKernel x hy.1)
    have hrker := MonoidHom.mem_ker.mp
      ((mem_cycleRotationSubgroup_iff x r).mp hr |>.1)
    rw [map_mul, hrker, one_mul] at hyker
    have hsection := congrArg Subtype.val
      ((cycleCentralizerSplitting x).rightHom_splitting q)
    have hq : q = 1 := by
      apply Subtype.ext
      exact hsection.symm.trans hyker
    subst q
    have hir : r ∈ fixedPointPermutationSubgroup x ⊓ cycleRotationSubgroup x :=
      ⟨by simpa using hy.1, hr⟩
    have hirbot : r ∈ (⊥ : Subgroup
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) := by
      rw [← fixedPointPermutationSubgroup_inf_cycleRotationSubgroup_eq_bot x]
      exact hir
    simpa using hirbot
  · exact bot_le

/-- Lemma 5.2.2(d)(1): for a prime-order permutation, the rotation subgroup
`R` is normal in `RL` and intersects the cycle-permuting complement `L`
trivially; the fixed-point factor `I` is an internal direct factor complementary
to `RL`. -/
public theorem theorem_5_2_2_d_1
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (_hx : (orderOf x).Prime) :
    ((cycleRotationSubgroup x).subgroupOf
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x)).Normal ∧
    cycleRotationSubgroup x ⊓ cyclePermutationSubgroup x = ⊥ ∧
    fixedPointPermutationSubgroup x ⊓
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) = ⊥ ∧
    fixedPointPermutationSubgroup x ⊔
      (cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) = ⊤ ∧
    fixedPointPermutationSubgroup x ≤
      Subgroup.centralizer
        ((cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x :
          Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) : Set _) := by
  exact ⟨cycleRotationSubgroup_normal_subgroupOf_sup_cyclePermutationSubgroup x,
    cycleRotationSubgroup_inf_cyclePermutationSubgroup_eq_bot x,
    fixedPointPermutationSubgroup_inf_rotation_sup_permutation_eq_bot x,
    fixedPointPermutationSubgroup_sup_rotation_sup_permutation_eq_top x,
    fixedPointPermutationSubgroup_le_centralizer_rotation_sup_permutation x⟩

/-- Lemma 5.2.2(d)(2), commutativity clause. -/
public theorem theorem_5_2_2_d_2_a
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (a b : cycleRotationSubgroup x) : a * b = b * a := by
  let e := cycleRotationGroupMulEquivSubgroup x
  rcases e.surjective a with ⟨a, rfl⟩
  rcases e.surjective b with ⟨b, rfl⟩
  simpa only [map_mul] using congrArg e (cycleRotationGroup_mul_comm x a b)

/-- Lemma 5.2.2(d)(2), exponent clause. -/
public theorem theorem_5_2_2_d_2_b
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : cycleRotationSubgroup x) :
    a ^ orderOf x = 1 := by
  let e := cycleRotationGroupMulEquivSubgroup x
  rcases e.surjective a with ⟨a, rfl⟩
  rw [← map_pow, cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hx,
    map_one]

/-- Lemma 5.2.2(d)(2), order clause. -/
public theorem theorem_5_2_2_d_2_c
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Nat.card (cycleRotationSubgroup x) =
      orderOf x ^ Fintype.card x.cycleFactorsFinset :=
  (Nat.card_congr (cycleRotationGroupMulEquivSubgroup x).toEquiv).symm.trans
    (cycleRotationGroup_card_of_primeOrder x hx)

/-- Lemma 5.2.2(d)(3), symmetric-group clause: for a prime-order
permutation, the cycle-permuting complement is the full symmetric group on
the set of its nontrivial cycles. -/
@[expose]
public noncomputable def theorem_5_2_2_d_3_a
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    cyclePermutationSubgroup x ≃* Equiv.Perm x.cycleFactorsFinset :=
  (cycleActionRangeMulEquivCyclePermutationSubgroup x).symm.trans
    (cycleActionRangeMulEquivPermOfPrimeOrder x hx)

public theorem cycleRotationSubgroup_normal
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (cycleRotationSubgroup x).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [← fixedPointPermutationSubgroup_sup_rotation_sup_permutation_eq_top x]
  apply sup_le
  · rw [Subgroup.le_normalizer_iff]
    intro i hi r hr
    have hcomm :=
      fixedPointPermutationSubgroup_commutes_cycleRotationSubgroup x i hi r hr
    rw [hcomm.eq, mul_inv_cancel_right]
    exact hr
  · exact sup_le Subgroup.le_normalizer
      (cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x)

@[expose]
public noncomputable def cyclePermutationActionOnCycleRotations
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    cyclePermutationSubgroup x →* MulAut (CycleRotationGroup x) := by
  let : (cycleRotationSubgroup x).Normal := cycleRotationSubgroup_normal x
  exact (MulAut.congr (cycleRotationGroupMulEquivSubgroup x)).symm.toMonoidHom.comp
    ((MulAut.conjNormal :
      Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) →*
        MulAut (cycleRotationSubgroup x)).comp
          (Subgroup.subtype (cyclePermutationSubgroup x)))

public theorem cyclePermutationActionOnCycleRotations_apply
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (l : cyclePermutationSubgroup x) (a : CycleRotationGroup x) :
    ((cycleRotationGroupMulEquivSubgroup x)
      ((cyclePermutationActionOnCycleRotations x) l a)).1.1 =
        l.1.1 * ((cycleRotationGroupMulEquivSubgroup x) a).1.1 * l.1.1⁻¹ := by
  simp [cyclePermutationActionOnCycleRotations, MulAut.congr,
    MulAut.conjNormal_apply]

public theorem cyclePermutationSubgroup_map_cycleRotationCoordinate
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (l : cyclePermutationSubgroup x) (c : x.cycleFactorsFinset) :
    (Subgroup.zpowers c.1).map (MulAut.conj l.1.1).toMonoidHom =
      Subgroup.zpowers
        (((Equiv.Perm.OnCycleFactors.toPermHom x) l.1 c).1) := by
  rw [MonoidHom.map_zpowers]
  congr

/-- Lemma 5.2.2(d)(3), natural-action clause: the cycle-permuting complement
acts on the product of cyclic rotation coordinates by conjugation, carrying
the coordinate attached to a cycle to the coordinate attached to its image. -/
public theorem theorem_5_2_2_d_3_b
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (_hx : (orderOf x).Prime) :
    (∀ (l : cyclePermutationSubgroup x) (a : CycleRotationGroup x),
      ((cycleRotationGroupMulEquivSubgroup x)
        ((cyclePermutationActionOnCycleRotations x) l a)).1.1 =
          l.1.1 * ((cycleRotationGroupMulEquivSubgroup x) a).1.1 * l.1.1⁻¹) ∧
    ∀ (l : cyclePermutationSubgroup x) (c : x.cycleFactorsFinset),
      (Subgroup.zpowers c.1).map (MulAut.conj l.1.1).toMonoidHom =
        Subgroup.zpowers
          (((Equiv.Perm.OnCycleFactors.toPermHom x) l.1 c).1) := by
  exact ⟨cyclePermutationActionOnCycleRotations_apply x,
    cyclePermutationSubgroup_map_cycleRotationCoordinate x⟩

/-- Lemma 5.2.2(d)(4): the factor supported on the fixed points is the full
symmetric group on those fixed points. -/
@[expose]
public noncomputable def theorem_5_2_2_d_4
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    fixedPointPermutationSubgroup x ≃*
      Equiv.Perm (Function.fixedPoints x) :=
  (fixedPointPermMulEquivSubgroup x).symm

/-- A common choice of origin in every nontrivial cycle of `x`. -/
@[expose]
public noncomputable def cycleBasis
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    Equiv.Perm.Basis x :=
  Classical.choice (Equiv.Perm.Basis.nonempty x)

/-- Evaluation at the chosen origin identifies the powers of a cycle factor
with its support. -/
@[expose]
public noncomputable def basisZPowersEquivSupport
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (c : x.cycleFactorsFinset) : Subgroup.zpowers c.1 ≃ c.1.support :=
  let hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
  let b : c.1.support := ⟨cycleBasis x c, (cycleBasis x).mem_support_self c⟩
  (Equiv.mulRight (hcycle.zpowersEquivSupport.symm b)).trans
    hcycle.zpowersEquivSupport

/-- The underlying equivalence between an additive type and its
multiplicative type synonym. -/
@[expose]
public def toMultiplicativeEquiv (A : Type*) : A ≃ Multiplicative A where
  toFun := Multiplicative.ofAdd
  invFun := Multiplicative.toAdd
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
public theorem toMultiplicativeEquiv_apply (A : Type*) (a : A) :
    toMultiplicativeEquiv A a = Multiplicative.ofAdd a := rfl

/-- A cycle factor regarded as the standard generator of its own power
subgroup. -/
@[expose]
public def cycleFactorGenerator
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] {x : Equiv.Perm Ω}
    (c : x.cycleFactorsFinset) : Subgroup.zpowers c.1 :=
  ⟨c.1, Subgroup.mem_zpowers c.1⟩

public theorem cycleFactorGenerator_generates
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] {x : Equiv.Perm Ω}
    (c : x.cycleFactorsFinset) (z : Subgroup.zpowers c.1) :
    z ∈ Subgroup.zpowers (cycleFactorGenerator c) := by
  rcases z with ⟨z, hz⟩
  rcases hz with ⟨n, rfl⟩
  exact ⟨n, rfl⟩

public theorem cycleFactorZPowers_card_of_primeOrder
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) :
    Nat.card (Subgroup.zpowers c.1) = orderOf x := by
  rw [Nat.card_zpowers]
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf.trans
    (cycleFactor_support_card_eq_orderOf_of_primeOrder x hx c)

/-- Coordinates on a prime-order cycle, with zero at the chosen cycle basis. -/
@[expose]
public noncomputable def cycleCoordinateEquiv
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) :
    ZMod (orderOf x) ≃ c.1.support := by
  exact (toMultiplicativeEquiv (ZMod (orderOf x))).trans
    ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (cycleFactorZPowers_card_of_primeOrder x hx c)).toEquiv.trans
      (basisZPowersEquivSupport x c))

public theorem cycleCoordinateEquiv_intCast
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) (n : ℤ) :
    (cycleCoordinateEquiv x hx c (n : ZMod (orderOf x))).1 =
      (c.1 ^ n) (cycleBasis x c) := by
  unfold cycleCoordinateEquiv
  simp only [Equiv.trans_apply, toMultiplicativeEquiv_apply]
  have hcoord :
      zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
          (cycleFactorZPowers_card_of_primeOrder x hx c)
          (Multiplicative.ofAdd (n : ZMod (orderOf x))) =
        cycleFactorGenerator c ^ n :=
    zmodMulEquivOfGenerator_apply_ofAdd_intCast
      (cycleFactorGenerator_generates c)
      (cycleFactorZPowers_card_of_primeOrder x hx c) n
  change ((basisZPowersEquivSupport x c)
    (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (cycleFactorZPowers_card_of_primeOrder x hx c)
      (Multiplicative.ofAdd (n : ZMod (orderOf x))))).1 =
        (c.1 ^ n) (cycleBasis x c)
  rw [hcoord]
  unfold basisZPowersEquivSupport
  let hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
  let b : c.1.support := ⟨cycleBasis x c, (cycleBasis x).mem_support_self c⟩
  change (((c.1 ^ n : Equiv.Perm Ω) *
    (hcycle.zpowersEquivSupport.symm b).1)
      (Classical.choose hcycle)) = (c.1 ^ n) (cycleBasis x c)
  rw [Equiv.Perm.mul_apply]
  have hb := congrArg Subtype.val
    (hcycle.zpowersEquivSupport.apply_symm_apply b)
  exact congrArg (fun ω => (c.1 ^ n) ω) hb

public theorem cycleCoordinateEquiv_zero
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) :
    (cycleCoordinateEquiv x hx c 0).1 = cycleBasis x c := by
  simpa using cycleCoordinateEquiv_intCast x hx c 0

public theorem cycleCoordinateEquiv_intCast_eq_x_zpow
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset) (n : ℤ) :
    (cycleCoordinateEquiv x hx c (n : ZMod (orderOf x))).1 =
      (x ^ n) (cycleBasis x c) := by
  rw [cycleCoordinateEquiv_intCast]
  rw [← (cycleBasis x).cycleOf_eq c,
    Equiv.Perm.cycleOf_zpow_apply_self]

public theorem cycleCoordinateEquiv_add_one
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) :
    (cycleCoordinateEquiv x hx c (n + 1)).1 =
      c.1 (cycleCoordinateEquiv x hx c n).1 := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  have hn : (n.val : ZMod (orderOf x)) = n := ZMod.natCast_zmod_val n
  calc
    (cycleCoordinateEquiv x hx c (n + 1)).1 =
        (cycleCoordinateEquiv x hx c
          ((n.val : ZMod (orderOf x)) + 1)).1 := by rw [hn]
    _ = (cycleCoordinateEquiv x hx c
        (((n.val : ℤ) + 1 : ℤ) : ZMod (orderOf x))).1 := by norm_num
    _ = (c.1 ^ ((n.val : ℤ) + 1)) (cycleBasis x c) :=
      cycleCoordinateEquiv_intCast x hx c ((n.val : ℤ) + 1)
    _ = c.1 ((c.1 ^ (n.val : ℤ)) (cycleBasis x c)) := by
      rw [zpow_add, Equiv.Perm.mul_apply]
      simpa using Equiv.Perm.zpow_apply_comm c.1 (n.val : ℤ) 1
        (x := cycleBasis x c)
    _ = c.1 (cycleCoordinateEquiv x hx c
        ((n.val : ℤ) : ZMod (orderOf x))).1 := by
      rw [cycleCoordinateEquiv_intCast x hx c (n.val : ℤ)]
    _ = c.1 (cycleCoordinateEquiv x hx c n).1 := by
      have hn' : ((n.val : ℤ) : ZMod (orderOf x)) = n := by simp
      rw [hn']

public theorem x_apply_cycleCoordinateEquiv
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) :
    x (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx c (n + 1)).1 := by
  rw [cycleCoordinateEquiv_add_one]
  exact ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).2 _
    (cycleCoordinateEquiv x hx c n).2).symm

public theorem x_pow_apply_cycleCoordinateEquiv
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) (j : ℕ) :
    (x ^ j) (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx c (n + j)).1 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, x_apply_cycleCoordinateEquiv,
        ih (n := n + 1)]
      congr 2
      push_cast
      ring

/-- Coordinates consisting of the fixed points and one copy of `ZMod p` for
each nontrivial cycle of a prime-order permutation. -/
public abbrev PrimeCycleModel
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
  Function.fixedPoints x ⊕
    (Σ _c : x.cycleFactorsFinset, ZMod (orderOf x))

/-- The coordinate decomposition of the underlying point set of a
prime-order permutation. -/
@[expose]
public noncomputable def primeCycleCoordinates
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) : PrimeCycleModel x ≃ Ω :=
  Equiv.ofBijective
    (fun z => match z with
      | Sum.inl ω => ω.1
      | Sum.inr ⟨c, n⟩ => (cycleCoordinateEquiv x hx c n).1)
    (by
      constructor
      · intro z w hzw
        rcases z with z | ⟨c, n⟩ <;> rcases w with w | ⟨d, m⟩
        · exact congrArg Sum.inl (Subtype.ext hzw)
        · exfalso
          change z.1 = (cycleCoordinateEquiv x hx d m).1 at hzw
          have hsupp : (cycleCoordinateEquiv x hx d m).1 ∈ d.1.support :=
            (cycleCoordinateEquiv x hx d m).2
          have hfix : x z.1 = z.1 := Function.mem_fixedPoints_iff.mp z.2
          have hxsupp := Equiv.Perm.mem_cycleFactorsFinset_support_le d.2 hsupp
          rw [← hzw, Equiv.Perm.mem_support] at hxsupp
          exact hxsupp hfix
        · exfalso
          change (cycleCoordinateEquiv x hx c n).1 = w.1 at hzw
          have hsupp : (cycleCoordinateEquiv x hx c n).1 ∈ c.1.support :=
            (cycleCoordinateEquiv x hx c n).2
          have hfix : x w.1 = w.1 := Function.mem_fixedPoints_iff.mp w.2
          have hxsupp := Equiv.Perm.mem_cycleFactorsFinset_support_le c.2 hsupp
          rw [hzw, Equiv.Perm.mem_support] at hxsupp
          exact hxsupp hfix
        · have hc : c.1 = x.cycleOf (cycleCoordinateEquiv x hx c n).1 :=
            Equiv.Perm.cycle_is_cycleOf
              (cycleCoordinateEquiv x hx c n).2 c.2
          have hd : d.1 = x.cycleOf (cycleCoordinateEquiv x hx d m).1 :=
            Equiv.Perm.cycle_is_cycleOf
              (cycleCoordinateEquiv x hx d m).2 d.2
          change (cycleCoordinateEquiv x hx c n).1 =
            (cycleCoordinateEquiv x hx d m).1 at hzw
          have hcd : c = d := by
            apply Subtype.ext
            rw [hc, hd, hzw]
          subst d
          have hnm : n = m := (cycleCoordinateEquiv x hx c).injective
            (Subtype.ext hzw)
          subst m
          rfl
      · intro ω
        by_cases hω : x ω = ω
        · exact ⟨Sum.inl ⟨ω, Function.mem_fixedPoints_iff.mpr hω⟩, rfl⟩
        · have hcycle : x.cycleOf ω ∈ x.cycleFactorsFinset := by
            rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
              Equiv.Perm.mem_support]
            exact hω
          let c : x.cycleFactorsFinset := ⟨x.cycleOf ω, hcycle⟩
          have hωc : ω ∈ c.1.support := by
            change ω ∈ (x.cycleOf ω).support
            rw [Equiv.Perm.mem_support_cycleOf_iff]
            exact ⟨Equiv.Perm.SameCycle.rfl, by
              simpa only [Equiv.Perm.mem_support] using hω⟩
          rcases (cycleCoordinateEquiv x hx c).surjective ⟨ω, hωc⟩ with ⟨n, hn⟩
          exact ⟨Sum.inr ⟨c, n⟩, congrArg Subtype.val hn⟩)

public theorem primeCycleCoordinates_apply_fixed
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (ω : Function.fixedPoints x) :
    primeCycleCoordinates x hx (Sum.inl ω) = ω.1 := rfl

public theorem primeCycleCoordinates_apply_cycle
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) :
    primeCycleCoordinates x hx (Sum.inr ⟨c, n⟩) =
      (cycleCoordinateEquiv x hx c n).1 := rfl

/-- Multiplication by a unit, viewed as a permutation of `ZMod p`. -/
@[expose]
public def zmodUnitPermHom (p : ℕ) :
    (ZMod p)ˣ →* Equiv.Perm (ZMod p) :=
  MulAction.toPermHom (ZMod p)ˣ (ZMod p)

public theorem zmodUnitPermHom_apply
    (p : ℕ) (k : (ZMod p)ˣ) (n : ZMod p) :
    zmodUnitPermHom p k n = (k : ZMod p) * n := rfl

public theorem zmodUnitPermHom_injective (p : ℕ) :
    Function.Injective (zmodUnitPermHom p) := by
  intro k l hkl
  apply Units.ext
  have h := congrArg (fun q : Equiv.Perm (ZMod p) => q 1) hkl
  simpa [zmodUnitPermHom_apply] using h

/-- Apply the same unit multiplier in every nontrivial cycle coordinate. -/
@[expose]
public noncomputable def primeCycleSigmaMultiplierHom
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (ZMod (orderOf x))ˣ →*
      Equiv.Perm (Σ _c : x.cycleFactorsFinset, ZMod (orderOf x)) :=
  (Equiv.Perm.sigmaCongrRightHom
    (fun _c : x.cycleFactorsFinset => ZMod (orderOf x))).comp
      { toFun := fun k _c => zmodUnitPermHom (orderOf x) k
        map_one' := by ext c n; simp
        map_mul' := by
          intro k l
          ext c n
          simp [Equiv.Perm.mul_apply, zmodUnitPermHom_apply] }

/-- The uniform cycle multiplier on the fixed-point/cycle-coordinate model. -/
@[expose]
public noncomputable def primeCycleModelMultiplierHom
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    (ZMod (orderOf x))ˣ →* Equiv.Perm (PrimeCycleModel x) :=
  (Equiv.Perm.sumCongrHom (Function.fixedPoints x)
    (Σ _c : x.cycleFactorsFinset, ZMod (orderOf x))).comp
      { toFun := fun k => (1, primeCycleSigmaMultiplierHom x k)
        map_one' := by simp
        map_mul' := by intro k l; simp }

/-- The uniform cycle multiplier transported to the original point set. -/
@[expose]
public noncomputable def primeCycleMultiplierHom
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    (ZMod (orderOf x))ˣ →* Equiv.Perm Ω :=
  (primeCycleCoordinates x hx).permCongrHom.toMonoidHom.comp
    (primeCycleModelMultiplierHom x)

public theorem primeCycleMultiplierHom_apply_fixed
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (ω : Function.fixedPoints x) :
    primeCycleMultiplierHom x hx k ω.1 = ω.1 := by
  change primeCycleCoordinates x hx
    (primeCycleModelMultiplierHom x k
      ((primeCycleCoordinates x hx).symm ω.1)) = ω.1
  have hcoord : (primeCycleCoordinates x hx).symm ω.1 = Sum.inl ω := by
    apply (primeCycleCoordinates x hx).injective
    rw [(primeCycleCoordinates x hx).apply_symm_apply]
    rfl
  calc
    primeCycleCoordinates x hx
        (primeCycleModelMultiplierHom x k
          ((primeCycleCoordinates x hx).symm ω.1)) =
      primeCycleCoordinates x hx
        (primeCycleModelMultiplierHom x k (Sum.inl ω)) := by rw [hcoord]
    _ = ω.1 := rfl

public theorem primeCycleMultiplierHom_apply_cycle
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (c : x.cycleFactorsFinset) (n : ZMod (orderOf x)) :
    primeCycleMultiplierHom x hx k (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx c ((k : ZMod (orderOf x)) * n)).1 := by
  change primeCycleCoordinates x hx
    (primeCycleModelMultiplierHom x k
      ((primeCycleCoordinates x hx).symm
        (primeCycleCoordinates x hx (Sum.inr ⟨c, n⟩)))) = _
  have hcoord := (primeCycleCoordinates x hx).symm_apply_apply (Sum.inr ⟨c, n⟩)
  calc
    primeCycleCoordinates x hx
        (primeCycleModelMultiplierHom x k
          ((primeCycleCoordinates x hx).symm
            (primeCycleCoordinates x hx (Sum.inr ⟨c, n⟩)))) =
      primeCycleCoordinates x hx
        (primeCycleModelMultiplierHom x k (Sum.inr ⟨c, n⟩)) := by rw [hcoord]
    _ = (cycleCoordinateEquiv x hx c
        ((k : ZMod (orderOf x)) * n)).1 := rfl

public theorem primeCycleMultiplierHom_inv_apply_cycle
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (c : x.cycleFactorsFinset) (n : ZMod (orderOf x)) :
    (primeCycleMultiplierHom x hx k)⁻¹ (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx c
        (((k⁻¹ : (ZMod (orderOf x))ˣ) : ZMod (orderOf x)) * n)).1 := by
  rw [← map_inv]
  exact primeCycleMultiplierHom_apply_cycle x hx k⁻¹ c n

public theorem primeCycleMultiplier_conj_x
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ) :
    primeCycleMultiplierHom x hx k * x *
        (primeCycleMultiplierHom x hx k)⁻¹ =
      x ^ (k : ZMod (orderOf x)).val := by
  apply Equiv.ext
  intro ω
  obtain ⟨z, rfl⟩ := (primeCycleCoordinates x hx).surjective ω
  rcases z with ω | ⟨c, n⟩
  · change primeCycleMultiplierHom x hx k
      (x ((primeCycleMultiplierHom x hx k)⁻¹ ω.1)) = (x ^ k.1.val) ω.1
    have hfix : x ω.1 = ω.1 := Function.mem_fixedPoints_iff.mp ω.2
    have hinv : (primeCycleMultiplierHom x hx k)⁻¹ =
        primeCycleMultiplierHom x hx k⁻¹ := by rw [← map_inv]
    rw [hinv, primeCycleMultiplierHom_apply_fixed,
      hfix, primeCycleMultiplierHom_apply_fixed]
    exact (Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix _).symm
  · change primeCycleMultiplierHom x hx k
      (x ((primeCycleMultiplierHom x hx k)⁻¹
        (cycleCoordinateEquiv x hx c n).1)) =
          (x ^ k.1.val) (cycleCoordinateEquiv x hx c n).1
    rw [primeCycleMultiplierHom_inv_apply_cycle,
      x_apply_cycleCoordinateEquiv,
      primeCycleMultiplierHom_apply_cycle,
      x_pow_apply_cycleCoordinateEquiv]
    apply congrArg Subtype.val
    apply congrArg (cycleCoordinateEquiv x hx c)
    let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
    have hkval : (((k : ZMod (orderOf x)).val : ℕ) :
        ZMod (orderOf x)) = k :=
      ZMod.natCast_zmod_val (k : ZMod (orderOf x))
    rw [hkval]
    simp [mul_add]

public theorem zpowers_pow_eq_of_coprime_order
    {G : Type*} [Group G] (x : G) (k : ℕ)
    (hk : (orderOf x).Coprime k) :
    Subgroup.zpowers (x ^ k) = Subgroup.zpowers x := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k)
  · apply Subgroup.zpowers_le.2
    have hk' : (Nat.card (Subgroup.zpowers x)).Coprime k := by
      rwa [Nat.card_zpowers]
    obtain ⟨z, hz⟩ := (powCoprime hk').surjective
      (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x)
    obtain ⟨m, hm⟩ := z.2
    refine ⟨m, ?_⟩
    have hz' := congrArg Subtype.val hz
    change z.1 ^ k = x at hz'
    calc
      (x ^ k) ^ m = (x ^ m) ^ k := by
        simpa only [zpow_natCast] using zpow_comm x (k : ℤ) m
      _ = z.1 ^ k := congrArg (fun y : G => y ^ k) hm
      _ = x := hz'

public theorem primeCycleMultiplier_mem_normalizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ) :
    primeCycleMultiplierHom x hx k ∈
      Subgroup.normalizer (Subgroup.zpowers x) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    MonoidHom.map_zpowers]
  change Subgroup.zpowers
      (primeCycleMultiplierHom x hx k * x *
        (primeCycleMultiplierHom x hx k)⁻¹) = Subgroup.zpowers x
  rw [primeCycleMultiplier_conj_x]
  apply zpowers_pow_eq_of_coprime_order
  exact (ZMod.val_coe_unit_coprime k).symm

public theorem primeCycleMultiplierHom_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Function.Injective (primeCycleMultiplierHom x hx) := by
  intro k l hkl
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hx.ne_one rfl
  have hcycles : x.cycleFactorsFinset.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hxne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp h)
  obtain ⟨c, hc⟩ := hcycles
  let c' : x.cycleFactorsFinset := ⟨c, hc⟩
  have heval := congrArg
    (fun q : Equiv.Perm Ω => q (cycleCoordinateEquiv x hx c' 1).1) hkl
  rw [primeCycleMultiplierHom_apply_cycle,
    primeCycleMultiplierHom_apply_cycle] at heval
  have hunit : (k : ZMod (orderOf x)) = l := by
    simpa using (cycleCoordinateEquiv x hx c').injective (Subtype.ext heval)
  exact Units.ext hunit

/-- A primitive unit modulo the prime order of `x`. -/
@[expose]
public noncomputable def primeCyclePrimitiveUnit
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) : (ZMod (orderOf x))ˣ := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  let : IsCyclic (ZMod (orderOf x))ˣ := ZMod.isCyclic_units_prime hx
  exact Classical.choose
    (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (orderOf x))ˣ))

public theorem primeCyclePrimitiveUnit_orderOf
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    orderOf (primeCyclePrimitiveUnit x hx) = orderOf x - 1 := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  let : IsCyclic (ZMod (orderOf x))ˣ := ZMod.isCyclic_units_prime hx
  rw [primeCyclePrimitiveUnit]
  exact (Classical.choose_spec
    (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (orderOf x))ˣ))).trans (by
      rw [Nat.card_eq_fintype_card]
      exact (Nat.prime_iff_card_units (orderOf x)).mp hx)

/-- The multiplier generator used in Lemma 5.2.2(e). -/
@[expose]
public noncomputable def primeCycleNormalizerGenerator
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) : Equiv.Perm Ω :=
  primeCycleMultiplierHom x hx (primeCyclePrimitiveUnit x hx)

public theorem centralizer_zpowers_eq_centralizer_singleton
    {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

/-- The uniform multiplier, regarded as an element of the normalizer of `⟨x⟩`. -/
@[expose]
public noncomputable def primeCycleMultiplierToNormalizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    (ZMod (orderOf x))ˣ →*
      Subgroup.normalizer
        (Subgroup.zpowers x : Set (Equiv.Perm Ω)) where
  toFun k := ⟨primeCycleMultiplierHom x hx k,
    primeCycleMultiplier_mem_normalizer x hx k⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (primeCycleMultiplierHom x hx)
  map_mul' k l := by
    apply Subtype.ext
    exact map_mul (primeCycleMultiplierHom x hx) k l

/-- The action of uniform multipliers on the cyclic group `⟨x⟩`. -/
@[expose]
public noncomputable def primeCycleNormalizerActionHom
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    (ZMod (orderOf x))ˣ →* MulAut (Subgroup.zpowers x) :=
  (Subgroup.zpowers x).normalizerMonoidHom.comp
    (primeCycleMultiplierToNormalizer x hx)

public theorem primeCycleNormalizerActionHom_apply_generator
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ) :
    primeCycleNormalizerActionHom x hx k
        ⟨x, Subgroup.mem_zpowers x⟩ =
      ⟨x ^ (k : ZMod (orderOf x)).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _⟩ := by
  apply Subtype.ext
  change primeCycleMultiplierHom x hx k * x *
    (primeCycleMultiplierHom x hx k)⁻¹ = x ^ (k : ZMod (orderOf x)).val
  exact primeCycleMultiplier_conj_x x hx k

public theorem primeCycleNormalizerActionHom_injective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Function.Injective (primeCycleNormalizerActionHom x hx) := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  intro k l hkl
  have hpow : x ^ (k : ZMod (orderOf x)).val =
      x ^ (l : ZMod (orderOf x)).val := by
    have h := congrArg
      (fun a : MulAut (Subgroup.zpowers x) =>
        a ⟨x, Subgroup.mem_zpowers x⟩) hkl
    simpa only [primeCycleNormalizerActionHom_apply_generator,
      Subtype.mk.injEq] using h
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (k : ZMod (orderOf x)),
    ← ZMod.natCast_zmod_val (l : ZMod (orderOf x)),
    ZMod.natCast_eq_natCast_iff]
  exact pow_eq_pow_iff_modEq.mp hpow

public theorem primeCycleNormalizerActionHom_surjective
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Function.Surjective (primeCycleNormalizerActionHom x hx) := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  let e : (ZMod (orderOf x))ˣ ≃ MulAut (Subgroup.zpowers x) := by
    let e' := (IsCyclic.mulAutMulEquiv (Subgroup.zpowers x)).symm.toEquiv
    rw [Nat.card_zpowers x] at e'
    exact e'
  exact (primeCycleNormalizerActionHom_injective x hx).surjective_of_finite e

public theorem primeCyclePrimitiveUnit_zpowers_eq_top
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Subgroup.zpowers (primeCyclePrimitiveUnit x hx) = ⊤ := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, primeCyclePrimitiveUnit_orderOf,
    Nat.card_eq_fintype_card]
  exact ((Nat.prime_iff_card_units (orderOf x)).mp hx).symm

public theorem primeCycleMultiplier_mem_zpowers_normalizerGenerator
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ) :
    primeCycleMultiplierHom x hx k ∈
      Subgroup.zpowers (primeCycleNormalizerGenerator x hx) := by
  rw [primeCycleNormalizerGenerator, ← MonoidHom.map_zpowers]
  apply Subgroup.mem_map_of_mem
  rw [primeCyclePrimitiveUnit_zpowers_eq_top x hx]
  exact Subgroup.mem_top k

/-- Lemma 5.2.2(e)(1): the normalizer is the product of the centralizer and
the chosen cyclic complement, whose centralizer of `x` is trivial. -/
public theorem theorem_5_2_2_e_1
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    Subgroup.normalizer (Subgroup.zpowers x) =
        Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) ⊔
          Subgroup.zpowers (primeCycleNormalizerGenerator x hx) ∧
      Subgroup.zpowers (primeCycleNormalizerGenerator x hx) ⊓
          Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) = ⊥ := by
  constructor
  · apply le_antisymm
    · intro n hn
      let n' : Subgroup.normalizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω)) := ⟨n, hn⟩
      obtain ⟨k, hk⟩ := primeCycleNormalizerActionHom_surjective x hx
        ((Subgroup.zpowers x).normalizerMonoidHom n')
      let m : Subgroup.normalizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω)) :=
        primeCycleMultiplierToNormalizer x hx k
      let c : Subgroup.normalizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω)) := n' * m⁻¹
      have hcKer : c ∈ (Subgroup.zpowers x).normalizerMonoidHom.ker := by
        change (Subgroup.zpowers x).normalizerMonoidHom c = 1
        simp only [c, map_mul, map_inv, m]
        change (Subgroup.zpowers x).normalizerMonoidHom n' *
          (primeCycleNormalizerActionHom x hx k)⁻¹ = 1
        rw [hk]
        simp
      rw [Subgroup.normalizerMonoidHom_ker] at hcKer
      have hcZ : (c : Equiv.Perm Ω) ∈
          Subgroup.centralizer (Subgroup.zpowers x : Set (Equiv.Perm Ω)) := hcKer
      have hc : (c : Equiv.Perm Ω) ∈
          Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) := by
        rw [← centralizer_zpowers_eq_centralizer_singleton x]
        exact hcZ
      have hm : (m : Equiv.Perm Ω) ∈
          Subgroup.zpowers (primeCycleNormalizerGenerator x hx) :=
        primeCycleMultiplier_mem_zpowers_normalizerGenerator x hx k
      have hcm : (c : Equiv.Perm Ω) * (m : Equiv.Perm Ω) ∈
          Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) ⊔
            Subgroup.zpowers (primeCycleNormalizerGenerator x hx) :=
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) ⊔
          Subgroup.zpowers (primeCycleNormalizerGenerator x hx)).mul_mem
          (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hm)
      simpa [c, m, n'] using hcm
    · apply sup_le
      · rw [← centralizer_zpowers_eq_centralizer_singleton x]
        exact Subgroup.centralizer_le_normalizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω))
      · apply Subgroup.zpowers_le.2
        exact primeCycleMultiplier_mem_normalizer x hx
          (primeCyclePrimitiveUnit x hx)
  · apply le_antisymm
    · intro h hh
      obtain ⟨z, hz⟩ := hh.1
      have hmul : h = primeCycleMultiplierHom x hx
          (primeCyclePrimitiveUnit x hx ^ z) := by
        calc
          h = primeCycleNormalizerGenerator x hx ^ z := hz.symm
          _ = primeCycleMultiplierHom x hx
              (primeCyclePrimitiveUnit x hx ^ z) := by
            rw [primeCycleNormalizerGenerator, map_zpow]
      have hn : h ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
        rw [hmul]
        exact primeCycleMultiplier_mem_normalizer x hx _
      let h' : Subgroup.normalizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω)) := ⟨h, hn⟩
      have hhZ : h ∈ Subgroup.centralizer
          (Subgroup.zpowers x : Set (Equiv.Perm Ω)) := by
        rw [centralizer_zpowers_eq_centralizer_singleton x]
        exact hh.2
      have hhKer : h' ∈ (Subgroup.zpowers x).normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact hhZ
      have haction : primeCycleNormalizerActionHom x hx
          (primeCyclePrimitiveUnit x hx ^ z) = 1 := by
        change (Subgroup.zpowers x).normalizerMonoidHom
          (primeCycleMultiplierToNormalizer x hx
            (primeCyclePrimitiveUnit x hx ^ z)) = 1
        have hh' : primeCycleMultiplierToNormalizer x hx
            (primeCyclePrimitiveUnit x hx ^ z) = h' := by
          apply Subtype.ext
          exact hmul.symm
        rw [hh']
        exact hhKer
      have hunit : primeCyclePrimitiveUnit x hx ^ z = 1 :=
        primeCycleNormalizerActionHom_injective x hx
          (haction.trans (map_one (primeCycleNormalizerActionHom x hx)).symm)
      rw [hmul, hunit, map_one]
      exact Subgroup.one_mem ⊥
    · exact bot_le

/-- Lemma 5.2.2(e)(2): the multiplier generator has order `p - 1`. -/
public theorem theorem_5_2_2_e_2
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    orderOf (primeCycleNormalizerGenerator x hx) = orderOf x - 1 := by
  exact (orderOf_injective (primeCycleMultiplierHom x hx)
    (primeCycleMultiplierHom_injective x hx)
    (primeCyclePrimitiveUnit x hx)).trans
    (primeCyclePrimitiveUnit_orderOf x hx)

public theorem cycleFactor_zpow_apply_cycleCoordinate
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (z : ℤ) (n : ZMod (orderOf x)) :
    (c.1 ^ z) (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx c (n + (z : ZMod (orderOf x)))).1 := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  have hn : ((n.val : ℤ) : ZMod (orderOf x)) = n := by
    simp
  calc
    (c.1 ^ z) (cycleCoordinateEquiv x hx c n).1 =
        (c.1 ^ z) (cycleCoordinateEquiv x hx c
          ((n.val : ℤ) : ZMod (orderOf x))).1 := by rw [hn]
    _ = (c.1 ^ z) ((c.1 ^ (n.val : ℤ)) (cycleBasis x c)) := by
      rw [cycleCoordinateEquiv_intCast]
    _ = ((c.1 ^ z) * (c.1 ^ (n.val : ℤ))) (cycleBasis x c) := by
      rw [Equiv.Perm.mul_apply]
    _ = (c.1 ^ (z + (n.val : ℤ))) (cycleBasis x c) := by rw [zpow_add]
    _ = (cycleCoordinateEquiv x hx c
        ((z + (n.val : ℤ) : ℤ) : ZMod (orderOf x))).1 :=
      (cycleCoordinateEquiv_intCast x hx c (z + (n.val : ℤ))).symm
    _ = (cycleCoordinateEquiv x hx c
        (n + (z : ZMod (orderOf x)))).1 := by
      apply congrArg Subtype.val
      apply congrArg (cycleCoordinateEquiv x hx c)
      push_cast
      rw [ZMod.natCast_zmod_val n]
      exact add_comm _ _

public theorem cycleRotationToCentralizer_apply_fixed
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (a : CycleRotationGroup x) (ω : Function.fixedPoints x) :
    (cycleRotationToCentralizer x a).1 ω.1 = ω.1 := by
  have ha : cycleRotationToCentralizer x a ∈ cycleRotationSubgroup x := ⟨a, rfl⟩
  exact (mem_cycleRotationSubgroup_iff x _).mp ha |>.2 ω

public theorem cycleRotationToCentralizer_apply_cycleCoordinate
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : CycleRotationGroup x)
    (c : x.cycleFactorsFinset) (n : ZMod (orderOf x)) :
    (cycleRotationToCentralizer x a).1
        (cycleCoordinateEquiv x hx c n).1 =
      (a c).1 (cycleCoordinateEquiv x hx c n).1 := by
  change Equiv.Perm.OnCycleFactors.kerParam x (1, a)
      (cycleCoordinateEquiv x hx c n).1 = _
  rw [Equiv.Perm.OnCycleFactors.kerParam_apply]
  have hcycleEq : x.cycleOf (cycleCoordinateEquiv x hx c n).1 = c.1 :=
    (Equiv.Perm.cycle_is_cycleOf
      (cycleCoordinateEquiv x hx c n).2 c.2).symm
  have hcycle : x.cycleOf (cycleCoordinateEquiv x hx c n).1 ∈
      x.cycleFactorsFinset := by
    rw [hcycleEq]
    exact c.2
  rw [dif_pos hcycle]
  have hc : (⟨x.cycleOf (cycleCoordinateEquiv x hx c n).1, hcycle⟩ :
      x.cycleFactorsFinset) = c := Subtype.ext hcycleEq
  rw [hc]

public theorem cycleRotationToCentralizer_pow_coe
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (a : CycleRotationGroup x) (j : ℕ) :
    (cycleRotationToCentralizer x a).1 ^ j =
      (cycleRotationToCentralizer x (a ^ j)).1 := by
  exact congrArg Subtype.val (map_pow (cycleRotationToCentralizer x) a j).symm

public theorem primeCycleMultiplier_conj_cycleRotationToCentralizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (a : CycleRotationGroup x) :
    primeCycleMultiplierHom x hx k * (cycleRotationToCentralizer x a).1 *
        (primeCycleMultiplierHom x hx k)⁻¹ =
      (cycleRotationToCentralizer x
        (a ^ (k : ZMod (orderOf x)).val)).1 := by
  apply Equiv.ext
  intro ω
  obtain ⟨q, rfl⟩ := (primeCycleCoordinates x hx).surjective ω
  rcases q with ω | ⟨c, n⟩
  · change primeCycleMultiplierHom x hx k
        ((cycleRotationToCentralizer x a).1
          ((primeCycleMultiplierHom x hx k)⁻¹ ω.1)) =
      (cycleRotationToCentralizer x
        (a ^ (k : ZMod (orderOf x)).val)).1 ω.1
    have hinv : (primeCycleMultiplierHom x hx k)⁻¹ =
        primeCycleMultiplierHom x hx k⁻¹ := by rw [← map_inv]
    rw [hinv, primeCycleMultiplierHom_apply_fixed,
      cycleRotationToCentralizer_apply_fixed,
      primeCycleMultiplierHom_apply_fixed,
      cycleRotationToCentralizer_apply_fixed]
  · change primeCycleMultiplierHom x hx k
        ((cycleRotationToCentralizer x a).1
          ((primeCycleMultiplierHom x hx k)⁻¹
            (cycleCoordinateEquiv x hx c n).1)) =
      (cycleRotationToCentralizer x
        (a ^ (k : ZMod (orderOf x)).val)).1
          (cycleCoordinateEquiv x hx c n).1
    obtain ⟨z, hz⟩ := (a c).2
    rw [primeCycleMultiplierHom_inv_apply_cycle,
      cycleRotationToCentralizer_apply_cycleCoordinate]
    rw [← hz, cycleFactor_zpow_apply_cycleCoordinate,
      primeCycleMultiplierHom_apply_cycle,
      cycleRotationToCentralizer_apply_cycleCoordinate]
    have haj : ((a ^ (k : ZMod (orderOf x)).val) c).1 =
        c.1 ^ (z * ((k : ZMod (orderOf x)).val : ℤ)) := by
      change (a c).1 ^ (k : ZMod (orderOf x)).val = _
      rw [← hz, ← zpow_natCast, ← zpow_mul]
    rw [haj, cycleFactor_zpow_apply_cycleCoordinate]
    apply congrArg Subtype.val
    apply congrArg (cycleCoordinateEquiv x hx c)
    let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
    have hkval : (((k : ZMod (orderOf x)).val : ℕ) :
        ZMod (orderOf x)) = k := ZMod.natCast_zmod_val _
    push_cast
    rw [hkval]
    simp [mul_add]
    exact mul_comm _ _

/-- Lemma 5.2.2(e)(3), power-map clause: the chosen generator induces one
common nonzero power map on every rotation coordinate. -/
public theorem theorem_5_2_2_e_3_a
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : CycleRotationGroup x) :
    primeCycleNormalizerGenerator x hx * (cycleRotationToCentralizer x a).1 *
        (primeCycleNormalizerGenerator x hx)⁻¹ =
      (cycleRotationToCentralizer x
        (a ^ (primeCyclePrimitiveUnit x hx : ZMod (orderOf x)).val)).1 :=
  primeCycleMultiplier_conj_cycleRotationToCentralizer x hx
    (primeCyclePrimitiveUnit x hx) a

/-- Lemma 5.2.2(e)(3), Frobenius clause: every nonidentity element of the
chosen cyclic complement acts fixed-point-freely on the rotation subgroup. -/
public theorem theorem_5_2_2_e_3_b
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (z : ℤ)
    (hz : primeCycleNormalizerGenerator x hx ^ z ≠ 1)
    (r : cycleRotationSubgroup x)
    (hcomm : Commute (primeCycleNormalizerGenerator x hx ^ z) r.1.1) :
    r = 1 := by
  let e := cycleRotationGroupMulEquivSubgroup x
  rcases e.surjective r with ⟨a, rfl⟩
  let __ch5_Centralizer_u : (ZMod (orderOf x))ˣ := primeCyclePrimitiveUnit x hx ^ z
  have hgpow : primeCycleNormalizerGenerator x hx ^ z =
      primeCycleMultiplierHom x hx __ch5_Centralizer_u := by
    change (primeCycleMultiplierHom x hx (primeCyclePrimitiveUnit x hx)) ^ z =
      primeCycleMultiplierHom x hx (primeCyclePrimitiveUnit x hx ^ z)
    exact (map_zpow (primeCycleMultiplierHom x hx)
      (primeCyclePrimitiveUnit x hx) z).symm
  have hu : __ch5_Centralizer_u ≠ 1 := by
    intro hu
    apply hz
    rw [hgpow, hu, map_one]
  change Commute (primeCycleNormalizerGenerator x hx ^ z)
    (cycleRotationToCentralizer x a).1 at hcomm
  have hcommconj : primeCycleMultiplierHom x hx __ch5_Centralizer_u *
      (cycleRotationToCentralizer x a).1 *
        (primeCycleMultiplierHom x hx __ch5_Centralizer_u)⁻¹ =
      (cycleRotationToCentralizer x a).1 := by
    rw [← hgpow]
    calc
      primeCycleNormalizerGenerator x hx ^ z *
          (cycleRotationToCentralizer x a).1 *
            (primeCycleNormalizerGenerator x hx ^ z)⁻¹ =
        (cycleRotationToCentralizer x a).1 *
          primeCycleNormalizerGenerator x hx ^ z *
            (primeCycleNormalizerGenerator x hx ^ z)⁻¹ := by rw [hcomm.eq]
      _ = (cycleRotationToCentralizer x a).1 := by simp
  have hcoe : (cycleRotationToCentralizer x
      (a ^ (__ch5_Centralizer_u : ZMod (orderOf x)).val)).1 =
      (cycleRotationToCentralizer x a).1 :=
    (primeCycleMultiplier_conj_cycleRotationToCentralizer x hx __ch5_Centralizer_u a).symm.trans
      hcommconj
  have ha : a ^ (__ch5_Centralizer_u : ZMod (orderOf x)).val = a :=
    cycleRotationToCentralizer_injective x (Subtype.ext hcoe)
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  let : Fact (Nat.Prime (orderOf x)) := ⟨hx⟩
  have huval_ne_zero : (__ch5_Centralizer_u : ZMod (orderOf x)).val ≠ 0 := by
    intro hzero
    have hucoe : (__ch5_Centralizer_u : ZMod (orderOf x)) = 0 := by
      rw [← ZMod.natCast_zmod_val (__ch5_Centralizer_u : ZMod (orderOf x)), hzero]
      simp
    exact Units.ne_zero __ch5_Centralizer_u hucoe
  have huval_ne_one : (__ch5_Centralizer_u : ZMod (orderOf x)).val ≠ 1 := by
    intro hone
    apply hu
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (__ch5_Centralizer_u : ZMod (orderOf x)), hone]
    simp
  have huval_one_lt : 1 < (__ch5_Centralizer_u : ZMod (orderOf x)).val := by omega
  have huval_sub_one_lt : (__ch5_Centralizer_u : ZMod (orderOf x)).val - 1 < orderOf x := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt _)
  have hcoprime : (orderOf x).Coprime
      ((__ch5_Centralizer_u : ZMod (orderOf x)).val - 1) := by
    rw [hx.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by omega) huval_sub_one_lt
  have haone : a = 1 := by
    funext c
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcoprime
    · rw [orderOf_dvd_iff_pow_eq_one]
      have hp := congrArg (fun b : CycleRotationGroup x => b c)
        (cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hx a)
      simpa using hp
    · rw [orderOf_dvd_iff_pow_eq_one]
      have hc := congrArg (fun b : CycleRotationGroup x => b c) ha
      have hc' : (a c) ^ (__ch5_Centralizer_u : ZMod (orderOf x)).val = a c := by
        simpa using hc
      calc
        (a c) ^ ((__ch5_Centralizer_u : ZMod (orderOf x)).val - 1) =
            (a c) ^ ((__ch5_Centralizer_u : ZMod (orderOf x)).val - 1) * (a c) * (a c)⁻¹ := by
          simp
        _ = (a c) ^ (__ch5_Centralizer_u : ZMod (orderOf x)).val * (a c)⁻¹ := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = (a c) * (a c)⁻¹ := by rw [hc']
        _ = 1 := by simp
  rw [haone, map_one]

public theorem cycleCoordinateEquiv_not_mem_fixedPoints
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) :
    (cycleCoordinateEquiv x hx c n).1 ∉ Function.fixedPoints x := by
  intro hfix
  have hsupp : (cycleCoordinateEquiv x hx c n).1 ∈ x.support :=
    Equiv.Perm.mem_cycleFactorsFinset_support_le c.2
      (cycleCoordinateEquiv x hx c n).2
  rw [Equiv.Perm.mem_support, Function.mem_fixedPoints_iff.mp hfix] at hsupp
  exact hsupp rfl

public theorem primeCycleMultiplier_commutes_fixedPointPermToCentralizer
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (i : Equiv.Perm (Function.fixedPoints x)) :
    Commute (primeCycleMultiplierHom x hx k)
      (fixedPointPermToCentralizer x i).1 := by
  rw [Commute]
  apply Equiv.ext
  intro ω
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    fixedPointPermToCentralizer_coe]
  obtain ⟨q, rfl⟩ := (primeCycleCoordinates x hx).surjective ω
  rcases q with ω | ⟨c, n⟩
  · change primeCycleMultiplierHom x hx k (Equiv.Perm.ofSubtype i ω.1) =
      Equiv.Perm.ofSubtype i (primeCycleMultiplierHom x hx k ω.1)
    rw [Equiv.Perm.ofSubtype_apply_of_mem i ω.2,
      primeCycleMultiplierHom_apply_fixed x hx k (i ω),
      primeCycleMultiplierHom_apply_fixed x hx k ω,
      Equiv.Perm.ofSubtype_apply_of_mem i ω.2]
  · change primeCycleMultiplierHom x hx k
        (Equiv.Perm.ofSubtype i (cycleCoordinateEquiv x hx c n).1) =
      Equiv.Perm.ofSubtype i
        (primeCycleMultiplierHom x hx k (cycleCoordinateEquiv x hx c n).1)
    have hnot := cycleCoordinateEquiv_not_mem_fixedPoints x hx c n
    have hnot' := cycleCoordinateEquiv_not_mem_fixedPoints x hx c
      ((k : ZMod (orderOf x)) * n)
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem i hnot,
      primeCycleMultiplierHom_apply_cycle,
      Equiv.Perm.ofSubtype_apply_of_not_mem i hnot']

public theorem cyclePermutationSection_apply_cycleCoordinate
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime)
    (q : (Equiv.Perm.OnCycleFactors.toPermHom x).range)
    (c : x.cycleFactorsFinset) (n : ZMod (orderOf x)) :
    ((cycleCentralizerSplitting x).toMonoidHom q).1
        (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx
        ((cycleActionRangeToExplicitRange x q :
          Equiv.Perm x.cycleFactorsFinset) c) n).1 := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  have hn : (((n.val : ℤ) : ZMod (orderOf x))) = n := by
    simp
  have hm : (x ^ (n.val : ℤ)) (cycleBasis x c) =
      (cycleCoordinateEquiv x hx c n).1 := by
    rw [← cycleCoordinateEquiv_intCast_eq_x_zpow x hx c (n.val : ℤ), hn]
  change Equiv.Perm.Basis.ofPermHomFun (cycleBasis x)
      (cycleActionRangeToExplicitRange x q)
        (cycleCoordinateEquiv x hx c n).1 = _
  rw [Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem
    (cycleBasis x) (cycleActionRangeToExplicitRange x q)
      (cycleCoordinateEquiv x hx c n).2 hm]
  rw [← cycleCoordinateEquiv_intCast_eq_x_zpow x hx
    ((cycleActionRangeToExplicitRange x q :
      Equiv.Perm x.cycleFactorsFinset) c) (n.val : ℤ), hn]

public theorem primeCycleMultiplier_commutes_cyclePermutationSection
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (k : (ZMod (orderOf x))ˣ)
    (q : (Equiv.Perm.OnCycleFactors.toPermHom x).range) :
    Commute (primeCycleMultiplierHom x hx k)
      ((cycleCentralizerSplitting x).toMonoidHom q).1 := by
  rw [Commute]
  apply Equiv.ext
  intro ω
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  obtain ⟨w, rfl⟩ := (primeCycleCoordinates x hx).surjective ω
  rcases w with ω | ⟨c, n⟩
  · have hfix := cyclePermutationSubgroup_fixes_fixedPoints x
      ((cycleCentralizerSplitting x).toMonoidHom q) ⟨q, rfl⟩ ω
    change primeCycleMultiplierHom x hx k
        (((cycleCentralizerSplitting x).toMonoidHom q).1 ω.1) =
      ((cycleCentralizerSplitting x).toMonoidHom q).1
        (primeCycleMultiplierHom x hx k ω.1)
    rw [hfix, primeCycleMultiplierHom_apply_fixed, hfix]
  · change primeCycleMultiplierHom x hx k
        (((cycleCentralizerSplitting x).toMonoidHom q).1
          (cycleCoordinateEquiv x hx c n).1) =
      ((cycleCentralizerSplitting x).toMonoidHom q).1
        (primeCycleMultiplierHom x hx k
          (cycleCoordinateEquiv x hx c n).1)
    rw [cyclePermutationSection_apply_cycleCoordinate,
      primeCycleMultiplierHom_apply_cycle,
      primeCycleMultiplierHom_apply_cycle,
      cyclePermutationSection_apply_cycleCoordinate]

/-- Lemma 5.2.2(e)(4): the chosen generator centralizes `LI`. -/
public theorem theorem_5_2_2_e_4
    {Ω : Type __ch5_Centralizer_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    (fixedPointPermutationSubgroup x ⊔ cyclePermutationSubgroup x).map
        (Subgroup.subtype
          (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) ≤
      Subgroup.centralizer
        ({primeCycleNormalizerGenerator x hx} : Set (Equiv.Perm Ω)) := by
  rw [Subgroup.map_sup]
  apply sup_le
  · intro y hy
    rcases hy with ⟨i, hi, rfl⟩
    rcases hi with ⟨i, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (primeCycleMultiplier_commutes_fixedPointPermToCentralizer x hx
      (primeCyclePrimitiveUnit x hx) i).eq.symm
  · intro y hy
    rcases hy with ⟨l, hl, rfl⟩
    rcases hl with ⟨q, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (primeCycleMultiplier_commutes_cyclePermutationSection x hx
      (primeCyclePrimitiveUnit x hx) q).eq.symm

end GLS3.Chapter5
/- END Theory.Centralizer -/

/- BEGIN Theory.SchurPresentation -/
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_SchurPresentation_u

namespace GLS3.Chapter5
namespace SchurPresentation


public abbrev V (n : Nat) := Fin (n + 5) → ℚ

@[expose] public def Q (n : Nat) : QuadraticForm ℚ (V n) :=
  QuadraticMap.weightedSumSquares ℚ (fun _ => (-1 / 2 : ℚ))

@[expose] public def root (n : Nat) (i : Fin (n + 4)) : V n :=
  fun j => if j = i.castSucc then 1 else if j = i.succ then -1 else 0

public theorem Q_root (n : Nat) (i : Fin (n + 4)) : Q n (root n i) = -1 := by
  classical
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  rw [Q, QuadraticMap.weightedSumSquares_apply]
  let f : Fin (n + 5) → ℚ :=
    fun j => (-1 / 2 : ℚ) * (root n i j * root n i j)
  change (∑ j, f j) = -1
  calc
    (∑ j, f j) = f i.castSucc +
        ∑ j ∈ (Finset.univ : Finset (Fin (n + 5))) \ {i.castSucc}, f j :=
      Finset.sum_eq_add_sum_sdiff_singleton i.castSucc f (by simp)
    _ = -1 := by
      have hsum :
          (∑ j ∈ (Finset.univ : Finset (Fin (n + 5))) \ {i.castSucc}, f j) =
            f i.succ := by
        apply Finset.sum_eq_single i.succ
        · intro j hj hji
          have hja : j ≠ i.castSucc := by
            simpa [Finset.mem_sdiff] using (Finset.mem_sdiff.mp hj).2
          simp [f, root, hja, hji]
        · simp [hne.symm]
      rw [hsum]
      simp [f, root, hne.symm]

public theorem polar_Q (n : Nat) (v w : V n) :
    QuadraticMap.polar (Q n) v w = -∑ j, v j * w j := by
  rw [QuadraticMap.polar, Q]
  simp only [QuadraticMap.weightedSumSquares_apply, Pi.add_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

public theorem root_adjacent_dot (n : Nat) (i : Fin (n + 3)) :
    (∑ j, root n i.castSucc j * root n i.succ j) = -1 := by
  classical
  let m : Fin (n + 5) := i.castSucc.succ
  have hm : i.succ.castSucc = m := rfl
  have ham : i.castSucc.castSucc ≠ m := by
    exact ne_of_lt i.castSucc.castSucc_lt_succ
  have had : i.castSucc.castSucc ≠ i.succ.succ := by
    intro h
    have hval := congrArg Fin.val h
    change i.val = i.val + 1 + 1 at hval
    omega
  calc
    (∑ j, root n i.castSucc j * root n i.succ j) =
        root n i.castSucc m * root n i.succ m := by
      apply Fintype.sum_eq_single m
      intro j hj
      by_cases hja : j = i.castSucc.castSucc
      · subst j
        simp [root, m, hm, ham, had]
      · have hjm : j ≠ m := hj
        simp [root, m, hm, hja, hjm]
    _ = -1 := by
      simp [root, m, hm, ham.symm]

public theorem polar_Q_adjacent (n : Nat) (i : Fin (n + 3)) :
    QuadraticMap.polar (Q n) (root n i.castSucc) (root n i.succ) = 1 := by
  rw [polar_Q, root_adjacent_dot]
  norm_num

public theorem root_mul_root_eq_zero_of_far (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) (k : Fin (n + 5)) :
    root n i k * root n j k = 0 := by
  have hac : i.castSucc ≠ j.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc] at hval
    omega
  have had : i.castSucc ≠ j.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega
  have hbc : i.succ ≠ j.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    omega
  have hbd : i.succ ≠ j.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ] at hval
    omega
  by_cases hka : k = i.castSucc
  · subst k
    simp [root, hac, had]
  · by_cases hkb : k = i.succ
    · subst k
      simp [root, hbc, hbd]
    · simp [root, hka, hkb]

public theorem polar_Q_far (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    QuadraticMap.polar (Q n) (root n i) (root n j) = 0 := by
  rw [polar_Q]
  simp [root_mul_root_eq_zero_of_far n hfar]

public abbrev C (n : Nat) := CliffordAlgebra (Q n)

@[expose] public def rootElem (n : Nat) (i : Fin (n + 4)) : C n :=
  CliffordAlgebra.ι (Q n) (root n i)

public theorem rootElem_sq (n : Nat) (i : Fin (n + 4)) :
    rootElem n i * rootElem n i = -1 := by
  rw [rootElem, CliffordAlgebra.ι_sq_scalar, Q_root]
  simp

@[expose] public def rootUnit (n : Nat) (i : Fin (n + 4)) : (C n)ˣ where
  val := rootElem n i
  inv := -rootElem n i
  val_inv := by rw [mul_neg, rootElem_sq]; simp
  inv_val := by rw [neg_mul, rootElem_sq]; simp

public theorem rootUnit_sq (n : Nat) (i : Fin (n + 4)) :
    rootUnit n i ^ 2 = -1 := by
  apply Units.ext
  simpa [pow_two, rootUnit] using rootElem_sq n i

public theorem rootElem_adjacent_add_swap (n : Nat) (i : Fin (n + 3)) :
    rootElem n i.castSucc * rootElem n i.succ +
        rootElem n i.succ * rootElem n i.castSucc = 1 := by
  simpa [rootElem, polar_Q_adjacent] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Q n) (root n i.castSucc) (root n i.succ))

public theorem rootElem_adjacent_mul_pow_three (n : Nat) (i : Fin (n + 3)) :
    (rootElem n i.castSucc * rootElem n i.succ) ^ 3 = -1 := by
  let a := rootElem n i.castSucc
  let b := rootElem n i.succ
  have ha : a * a = -1 := rootElem_sq n i.castSucc
  have hb : b * b = -1 := rootElem_sq n i.succ
  have hab : a * b + b * a = 1 := rootElem_adjacent_add_swap n i
  have hba : b * a = 1 - a * b := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hab
  change (a * b) ^ 3 = -1
  have hx2 : (a * b) ^ 2 = a * b - 1 := by
    rw [pow_two]
    calc
      a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
      _ = a * (1 - a * b) * b := by rw [hba]
      _ = a * b - (a * a) * (b * b) := by noncomm_ring
      _ = a * b - 1 := by rw [ha, hb]; simp
  rw [pow_succ, hx2]
  calc
    (a * b - 1) * (a * b) = (a * b) ^ 2 - a * b := by
      rw [pow_two]
      noncomm_ring
    _ = -1 := by rw [hx2]; noncomm_ring

public theorem rootUnit_adjacent_mul_pow_three (n : Nat) (i : Fin (n + 3)) :
    (rootUnit n i.castSucc * rootUnit n i.succ) ^ 3 = -1 := by
  apply Units.ext
  simpa [rootUnit] using rootElem_adjacent_mul_pow_three n i

public theorem rootElem_far_add_swap (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    rootElem n i * rootElem n j + rootElem n j * rootElem n i = 0 := by
  simpa [rootElem, polar_Q_far n hfar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Q n) (root n i) (root n j))

public theorem rootElem_far_mul_sq (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (rootElem n i * rootElem n j) ^ 2 = -1 := by
  let a := rootElem n i
  let b := rootElem n j
  have ha : a * a = -1 := rootElem_sq n i
  have hb : b * b = -1 := rootElem_sq n j
  have hab : a * b + b * a = 0 := rootElem_far_add_swap n hfar
  have hba : b * a = -(a * b) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hab)
  change (a * b) ^ 2 = -1
  rw [pow_two]
  calc
    a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
    _ = a * (-(a * b)) * b := by rw [hba]
    _ = -((a * a) * (b * b)) := by noncomm_ring
    _ = -1 := by rw [ha, hb]; simp

public theorem rootUnit_far_mul_sq (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (rootUnit n i * rootUnit n j) ^ 2 = -1 := by
  apply Units.ext
  simpa [rootUnit] using rootElem_far_mul_sq n hfar

public inductive Gen (n : Nat)
  | central
  | adjacent (i : Fin (n + 4))
  deriving DecidableEq

@[expose] public def zWord (n : Nat) : FreeGroup (Gen n) :=
  FreeGroup.of .central

@[expose] public def tWord (n : Nat) (i : Fin (n + 4)) : FreeGroup (Gen n) :=
  FreeGroup.of (.adjacent i)

public inductive Relator (n : Nat) : FreeGroup (Gen n) → Prop
  | central_sq : Relator n (zWord n ^ 2)
  | central_comm (i : Fin (n + 4)) :
      Relator n (zWord n * tWord n i * (zWord n)⁻¹ * (tWord n i)⁻¹)
  | adjacent_sq (i : Fin (n + 4)) :
      Relator n (tWord n i ^ 2 * (zWord n)⁻¹)
  | braid (i : Fin (n + 3)) :
      Relator n ((tWord n i.castSucc * tWord n i.succ) ^ 3 * (zWord n)⁻¹)
  | far (i j : Fin (n + 4))
      (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
      Relator n ((tWord n i * tWord n j) ^ 2 * (zWord n)⁻¹)

public abbrev SchurPresentedGroup (n : Nat) := PresentedGroup (Relator n)

public instance schurPresentedGroupGroup (n : Nat) : Group (SchurPresentedGroup n) :=
  instGroupPresentedGroup (Relator n : Set (FreeGroup (Gen n)))

@[expose] public def generatorUnit (n : Nat) : Gen n → (C n)ˣ
  | .central => -1
  | .adjacent i => rootUnit n i

public theorem relator_lift_generatorUnit (n : Nat) (r : FreeGroup (Gen n))
    (hr : Relator n r) : FreeGroup.lift (generatorUnit n) r = 1 := by
  cases hr with
  | central_sq =>
      simp [zWord, generatorUnit, FreeGroup.lift_apply_of]
  | central_comm i =>
      simp [zWord, tWord, generatorUnit, FreeGroup.lift_apply_of]
  | adjacent_sq i =>
      simp [zWord, tWord, generatorUnit, FreeGroup.lift_apply_of, rootUnit_sq]
  | braid i =>
      simp [zWord, tWord, generatorUnit, FreeGroup.lift_apply_of,
        rootUnit_adjacent_mul_pow_three]
  | far i j hfar =>
      simp [zWord, tWord, generatorUnit, FreeGroup.lift_apply_of,
        rootUnit_far_mul_sq n hfar]

@[expose] public def schurCliffordRepresentation (n : Nat) :
    SchurPresentedGroup n →* (C n)ˣ :=
  PresentedGroup.toGroup (f := generatorUnit n) (relator_lift_generatorUnit n)

public theorem schurCliffordRepresentation_central (n : Nat) :
    schurCliffordRepresentation n (PresentedGroup.of (.central : Gen n)) = -1 := by
  simpa [schurCliffordRepresentation, generatorUnit] using
    (PresentedGroup.toGroup.of
      (rels := (Relator n : Set (FreeGroup (Gen n))))
      (f := generatorUnit n) (relator_lift_generatorUnit n)
      (x := (.central : Gen n)))

public theorem schurPresented_central_ne_one (n : Nat) :
    (PresentedGroup.of (.central : Gen n) : SchurPresentedGroup n) ≠ 1 := by
  intro h
  have hmap := congrArg (schurCliffordRepresentation n) h
  rw [schurCliffordRepresentation_central, map_one] at hmap
  have hcoe := congrArg (fun __ch5_SchurPresentation_u : (C n)ˣ => (__ch5_SchurPresentation_u : C n)) hmap
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hext := congrArg (CliffordAlgebra.equivExterior (Q n)) hcoe
  have hscalar :
      algebraMap ℚ (ExteriorAlgebra ℚ (V n)) (-1) =
        algebraMap ℚ (ExteriorAlgebra ℚ (V n)) 1 := by
    simpa using hext
  have hrat := FaithfulSMul.algebraMap_injective ℚ
    (ExteriorAlgebra ℚ (V n)) hscalar
  norm_num at hrat

@[expose] public def adjacentSwap (n : Nat) (i : Fin (n + 4)) :
    Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap i.castSucc i.succ

public theorem adjacentSwap_sq (n : Nat) (i : Fin (n + 4)) :
    adjacentSwap n i ^ 2 = 1 := by
  simp [adjacentSwap, pow_two]

private theorem __ch5_SchurPresentation_adjacentSwap_mul_pow_three (n : Nat) (i : Fin (n + 3)) :
    (adjacentSwap n i.castSucc * adjacentSwap n i.succ) ^ 3 = 1 := by
  let a : Fin (n + 5) := i.castSucc.castSucc
  let b : Fin (n + 5) := i.castSucc.succ
  let c : Fin (n + 5) := i.succ.succ
  have hab : a ≠ b := by
    exact ne_of_lt i.castSucc.castSucc_lt_succ
  have hac : a ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    change i.val = i.val + 1 + 1 at hval
    omega
  have hbc : b ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    change i.val + 1 = i.val + 1 + 1 at hval
    omega
  have hrewrite : Equiv.swap a b * Equiv.swap b c =
      Equiv.swap a c * Equiv.swap a b := by
    have hconj :
        Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
      simpa [Equiv.swap_comm] using
        (Equiv.swap_mul_swap_mul_swap
          (x := c) (y := b) (z := a) hbc.symm hac.symm)
    calc
      Equiv.swap a b * Equiv.swap b c =
          (Equiv.swap a b * Equiv.swap b c * Equiv.swap a b) *
            Equiv.swap a b := by simp [mul_assoc]
      _ = Equiv.swap a c * Equiv.swap a b := by rw [hconj]
  have hthree : Equiv.Perm.IsThreeCycle
      (Equiv.swap a c * Equiv.swap a b) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab hbc.symm
  change (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1
  rw [hrewrite, ← hthree.orderOf]
  exact pow_orderOf_eq_one _

private theorem __ch5_SchurPresentation_adjacentSwap_far_commute (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (adjacentSwap n i) (adjacentSwap n j) := by
  have hca : j.castSucc ≠ i.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc] at hval
    omega
  have hcb : j.castSucc ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega
  have hda : j.succ ≠ i.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    omega
  have hdb : j.succ ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ] at hval
    omega
  change adjacentSwap n i * adjacentSwap n j =
    adjacentSwap n j * adjacentSwap n i
  rw [adjacentSwap, adjacentSwap, Equiv.mul_swap_eq_swap_mul]
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb,
    Equiv.swap_apply_of_ne_of_ne hda hdb]

private theorem __ch5_SchurPresentation_adjacentSwap_far_mul_sq (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (adjacentSwap n i * adjacentSwap n j) ^ 2 = 1 := by
  have hcomm := __ch5_SchurPresentation_adjacentSwap_far_commute n hfar
  have hi2 : adjacentSwap n i * adjacentSwap n i = 1 := by
    simpa [pow_two] using adjacentSwap_sq n i
  have hj2 : adjacentSwap n j * adjacentSwap n j = 1 := by
    simpa [pow_two] using adjacentSwap_sq n j
  rw [pow_two, mul_assoc, hcomm.eq]
  calc
    adjacentSwap n i * adjacentSwap n j *
        (adjacentSwap n j * adjacentSwap n i) =
      adjacentSwap n i * (adjacentSwap n j * adjacentSwap n j) *
        adjacentSwap n i := by simp [mul_assoc]
    _ = 1 := by rw [hj2]; simpa using hi2

@[expose] public def generatorPerm (n : Nat) :
    Gen n → Equiv.Perm (Fin (n + 5))
  | .central => 1
  | .adjacent i => adjacentSwap n i

public theorem relator_lift_generatorPerm (n : Nat) (r : FreeGroup (Gen n))
    (hr : Relator n r) : FreeGroup.lift (generatorPerm n) r = 1 := by
  cases hr with
  | central_sq =>
      simp [zWord, generatorPerm, FreeGroup.lift_apply_of]
  | central_comm i =>
      simp [zWord, tWord, generatorPerm, FreeGroup.lift_apply_of]
  | adjacent_sq i =>
      simp [zWord, tWord, generatorPerm, FreeGroup.lift_apply_of, adjacentSwap_sq]
  | braid i =>
      simp [zWord, tWord, generatorPerm, FreeGroup.lift_apply_of,
        __ch5_SchurPresentation_adjacentSwap_mul_pow_three]
  | far i j hfar =>
      simp [zWord, tWord, generatorPerm, FreeGroup.lift_apply_of,
        __ch5_SchurPresentation_adjacentSwap_far_mul_sq n hfar]

@[expose] public def schurSymmetricProjection (n : Nat) :
    SchurPresentedGroup n →* Equiv.Perm (Fin (n + 5)) :=
  PresentedGroup.toGroup (f := generatorPerm n) (relator_lift_generatorPerm n)

public theorem schurSymmetricProjection_adjacent (n : Nat) (i : Fin (n + 4)) :
    schurSymmetricProjection n (PresentedGroup.of (.adjacent i)) = adjacentSwap n i := by
  simpa [schurSymmetricProjection, generatorPerm] using
    (PresentedGroup.toGroup.of
      (rels := (Relator n : Set (FreeGroup (Gen n))))
      (f := generatorPerm n) (relator_lift_generatorPerm n)
      (x := (.adjacent i : Gen n)))

public theorem schurSymmetricProjection_surjective (n : Nat) :
    Function.Surjective (schurSymmetricProjection n) := by
  apply MonoidHom.mrange_eq_top.mp
  apply top_unique
  rw [← Equiv.Perm.mclosure_swap_castSucc_succ (n + 4)]
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of (.adjacent i), schurSymmetricProjection_adjacent n i⟩

@[expose] public def schurCentral (n : Nat) : SchurPresentedGroup n :=
  PresentedGroup.of (.central : Gen n)

public theorem schurCentral_sq (n : Nat) : schurCentral n ^ 2 = 1 := by
  have hrel : Relator n (zWord n ^ 2) := Relator.central_sq
  have h := PresentedGroup.one_of_mem hrel
  simpa [schurCentral, zWord, PresentedGroup.of] using h

public theorem schurAdjacent_sq (n : Nat) (i : Fin (n + 4)) :
    (PresentedGroup.of (.adjacent i) : SchurPresentedGroup n) ^ 2 =
      schurCentral n := by
  have hrel : Relator n (tWord n i ^ 2 * (zWord n)⁻¹) :=
    Relator.adjacent_sq i
  have h := PresentedGroup.one_of_mem hrel
  apply mul_inv_eq_one.mp
  simpa [schurCentral, zWord, tWord, PresentedGroup.of] using h

public theorem schurAdjacent_mul_pow_three (n : Nat) (i : Fin (n + 3)) :
    (PresentedGroup.of (.adjacent i.castSucc) *
        PresentedGroup.of (.adjacent i.succ) : SchurPresentedGroup n) ^ 3 =
      schurCentral n := by
  have hrel : Relator n
      ((tWord n i.castSucc * tWord n i.succ) ^ 3 * (zWord n)⁻¹) :=
    Relator.braid i
  have h := PresentedGroup.one_of_mem hrel
  apply mul_inv_eq_one.mp
  simpa [schurCentral, zWord, tWord, PresentedGroup.of] using h

public theorem schurAdjacent_far_mul_sq (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (PresentedGroup.of (.adjacent i) *
        PresentedGroup.of (.adjacent j) : SchurPresentedGroup n) ^ 2 =
      schurCentral n := by
  have hrel : Relator n
      ((tWord n i * tWord n j) ^ 2 * (zWord n)⁻¹) :=
    Relator.far i j hfar
  have h := PresentedGroup.one_of_mem hrel
  apply mul_inv_eq_one.mp
  simpa [schurCentral, zWord, tWord, PresentedGroup.of] using h

public theorem schurCentral_ne_one (n : Nat) : schurCentral n ≠ 1 :=
  schurPresented_central_ne_one n

public theorem orderOf_schurCentral (n : Nat) : orderOf (schurCentral n) = 2 :=
  orderOf_eq_prime (schurCentral_sq n) (schurCentral_ne_one n)

public theorem schurCentral_commutes_generator (n : Nat) (g : Gen n) :
    Commute (schurCentral n) (PresentedGroup.of g) := by
  rcases g with _ | i
  · exact Commute.refl _
  · have hrel : Relator n
        (zWord n * tWord n i * (zWord n)⁻¹ * (tWord n i)⁻¹) :=
      Relator.central_comm i
    have h := PresentedGroup.one_of_mem hrel
    rw [← commutatorElement_eq_one_iff_commute]
    simpa [commutatorElement_def, schurCentral, zWord, tWord,
      PresentedGroup.of] using h

public theorem schurCentral_mem_center (n : Nat) :
    schurCentral n ∈ Subgroup.center (SchurPresentedGroup n) := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.centralizer
      ({schurCentral n} : Set (SchurPresentedGroup n)) := by
    apply PresentedGroup.generated_by (Relator n)
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (schurCentral_commutes_generator n g).eq.symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  exact hy

public theorem schurSymmetricProjection_central (n : Nat) :
    schurSymmetricProjection n (schurCentral n) = 1 := by
  simpa [schurCentral, schurSymmetricProjection, generatorPerm] using
    (PresentedGroup.toGroup.of
      (rels := (Relator n : Set (FreeGroup (Gen n))))
      (f := generatorPerm n) (relator_lift_generatorPerm n)
      (x := (.central : Gen n)))

public abbrev TypeACoxeterGroup (n : Nat) :=
  (CoxeterMatrix.A (n + 4)).Group

@[expose] public def generatorCoxeter (n : Nat) : Gen n → TypeACoxeterGroup n
  | .central => 1
  | .adjacent i => (CoxeterMatrix.A (n + 4)).simple i

private theorem __ch5_SchurPresentation_typeACoxeter_sq (n : Nat) (i : Fin (n + 4)) :
    (CoxeterMatrix.A (n + 4)).simple i ^ 2 = 1 := by
  change (CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i ^ 2 = 1
  exact (CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple_sq i

private theorem __ch5_SchurPresentation_typeACoxeter_braid (n : Nat) (i : Fin (n + 3)) :
    ((CoxeterMatrix.A (n + 4)).simple i.castSucc *
        (CoxeterMatrix.A (n + 4)).simple i.succ) ^ 3 = 1 := by
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  change (((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i.castSucc) *
      (CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i.succ) ^ 3 = 1
  simpa [CoxeterMatrix.A, hne] using
    ((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple_mul_simple_pow
      i.castSucc i.succ)

private theorem __ch5_SchurPresentation_typeACoxeter_far (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    ((CoxeterMatrix.A (n + 4)).simple i *
        (CoxeterMatrix.A (n + 4)).simple j) ^ 2 = 1 := by
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    omega
  have hji : j.val + 1 ≠ i.val := by omega
  have hij' : i.val + 1 ≠ j.val := by omega
  change (((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i) *
      (CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple j) ^ 2 = 1
  simpa [CoxeterMatrix.A, hij, hji, hij'] using
    ((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple_mul_simple_pow i j)

public theorem relator_lift_generatorCoxeter (n : Nat) (r : FreeGroup (Gen n))
    (hr : Relator n r) : FreeGroup.lift (generatorCoxeter n) r = 1 := by
  cases hr with
  | central_sq =>
      simp [zWord, generatorCoxeter, FreeGroup.lift_apply_of]
  | central_comm i =>
      simp [zWord, tWord, generatorCoxeter, FreeGroup.lift_apply_of]
  | adjacent_sq i =>
      simp [zWord, tWord, generatorCoxeter, FreeGroup.lift_apply_of,
        __ch5_SchurPresentation_typeACoxeter_sq]
  | braid i =>
      simp [zWord, tWord, generatorCoxeter, FreeGroup.lift_apply_of,
        __ch5_SchurPresentation_typeACoxeter_braid]
  | far i j hfar =>
      simp [zWord, tWord, generatorCoxeter, FreeGroup.lift_apply_of,
        __ch5_SchurPresentation_typeACoxeter_far n hfar]

@[expose] public def schurCoxeterProjection (n : Nat) :
    SchurPresentedGroup n →* TypeACoxeterGroup n :=
  PresentedGroup.toGroup (f := generatorCoxeter n)
    (relator_lift_generatorCoxeter n)

public theorem schurCoxeterProjection_adjacent (n : Nat) (i : Fin (n + 4)) :
    schurCoxeterProjection n (PresentedGroup.of (.adjacent i)) =
      (CoxeterMatrix.A (n + 4)).simple i := by
  simpa [schurCoxeterProjection, generatorCoxeter] using
    (PresentedGroup.toGroup.of
      (rels := (Relator n : Set (FreeGroup (Gen n))))
      (f := generatorCoxeter n) (relator_lift_generatorCoxeter n)
      (x := (.adjacent i : Gen n)))

public theorem schurCoxeterProjection_surjective (n : Nat) :
    Function.Surjective (schurCoxeterProjection n) := by
  apply MonoidHom.mrange_eq_top.mp
  apply top_unique
  rw [← (CoxeterMatrix.A (n + 4)).toCoxeterSystem.submonoid_closure_range_simple]
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of (.adjacent i), schurCoxeterProjection_adjacent n i⟩

public theorem schurCoxeterProjection_central (n : Nat) :
    schurCoxeterProjection n (schurCentral n) = 1 := by
  simpa [schurCentral, schurCoxeterProjection, generatorCoxeter] using
    (PresentedGroup.toGroup.of
      (rels := (Relator n : Set (FreeGroup (Gen n))))
      (f := generatorCoxeter n) (relator_lift_generatorCoxeter n)
      (x := (.central : Gen n)))

set_option backward.isDefEq.respectTransparency false in
public instance schurCentralZpowersNormal (n : Nat) :
    (Subgroup.zpowers (schurCentral n)).Normal where
  conj_mem x hx g := by
    have hxcenter : x ∈ Subgroup.center (SchurPresentedGroup n) :=
      (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hx
    have hcomm := Subgroup.mem_center_iff.mp hxcenter g
    simpa only [hcomm, mul_inv_cancel_right] using hx

public abbrev SchurCoxeterQuotient (n : Nat) :=
  SchurPresentedGroup n ⧸ Subgroup.zpowers (schurCentral n)

@[expose] public def schurCoxeterQuotientProjection (n : Nat) :
    SchurCoxeterQuotient n →* TypeACoxeterGroup n :=
  QuotientGroup.lift (Subgroup.zpowers (schurCentral n))
    (schurCoxeterProjection n) (by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact schurCoxeterProjection_central n)

public theorem schurCoxeterQuotientProjection_mk (n : Nat)
    (x : SchurPresentedGroup n) :
    schurCoxeterQuotientProjection n
        (QuotientGroup.mk' (Subgroup.zpowers (schurCentral n)) x) =
      schurCoxeterProjection n x := by
  rfl

public theorem schurCoxeterQuotientProjection_surjective (n : Nat) :
    Function.Surjective (schurCoxeterQuotientProjection n) :=
  QuotientGroup.lift_surjective_of_surjective
    (Subgroup.zpowers (schurCentral n)) (schurCoxeterProjection n)
    (schurCoxeterProjection_surjective n) (by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact schurCoxeterProjection_central n)

@[expose] public def schurCoxeterQuotientSimple (n : Nat) (i : Fin (n + 4)) :
    SchurCoxeterQuotient n :=
  QuotientGroup.mk' (Subgroup.zpowers (schurCentral n))
    (PresentedGroup.of (.adjacent i))

set_option backward.isDefEq.respectTransparency false in
public theorem schurCoxeterQuotient_mk_central (n : Nat) :
    QuotientGroup.mk' (Subgroup.zpowers (schurCentral n)) (schurCentral n) = 1 := by
  exact (QuotientGroup.eq_one_iff (schurCentral n)).mpr
    (Subgroup.mem_zpowers (schurCentral n))

set_option backward.isDefEq.respectTransparency false in
public theorem schurCoxeterQuotientSimple_sq (n : Nat) (i : Fin (n + 4)) :
    schurCoxeterQuotientSimple n i ^ 2 = 1 := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (schurCentral n))
  change (q (PresentedGroup.of (.adjacent i))) ^ 2 = 1
  rw [← map_pow, schurAdjacent_sq,
    schurCoxeterQuotient_mk_central]

set_option backward.isDefEq.respectTransparency false in
public theorem schurCoxeterQuotientSimple_braid (n : Nat) (i : Fin (n + 3)) :
    (schurCoxeterQuotientSimple n i.castSucc *
        schurCoxeterQuotientSimple n i.succ) ^ 3 = 1 := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (schurCentral n))
  change (q (PresentedGroup.of (.adjacent i.castSucc)) *
      q (PresentedGroup.of (.adjacent i.succ))) ^ 3 = 1
  rw [← map_mul, ← map_pow,
    schurAdjacent_mul_pow_three, schurCoxeterQuotient_mk_central]

set_option backward.isDefEq.respectTransparency false in
public theorem schurCoxeterQuotientSimple_far (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (schurCoxeterQuotientSimple n i * schurCoxeterQuotientSimple n j) ^ 2 = 1 := by
  let q := QuotientGroup.mk' (Subgroup.zpowers (schurCentral n))
  change (q (PresentedGroup.of (.adjacent i)) *
      q (PresentedGroup.of (.adjacent j))) ^ 2 = 1
  rw [← map_mul, ← map_pow,
    schurAdjacent_far_mul_sq n hfar, schurCoxeterQuotient_mk_central]

private theorem __ch5_SchurPresentation_schurCoxeterQuotientSimple_braid_rev (n : Nat)
    (i : Fin (n + 3)) :
    (schurCoxeterQuotientSimple n i.succ *
        schurCoxeterQuotientSimple n i.castSucc) ^ 3 = 1 := by
  let a := schurCoxeterQuotientSimple n i.castSucc
  let b := schurCoxeterQuotientSimple n i.succ
  have ha2 : a * a = 1 := by
    simpa [a, pow_two] using schurCoxeterQuotientSimple_sq n i.castSucc
  have hb2 : b * b = 1 := by
    simpa [b, pow_two] using schurCoxeterQuotientSimple_sq n i.succ
  have ha : a⁻¹ = a := (eq_inv_of_mul_eq_one_right ha2).symm
  have hb : b⁻¹ = b := (eq_inv_of_mul_eq_one_right hb2).symm
  have hab : (a * b) ^ 3 = 1 :=
    schurCoxeterQuotientSimple_braid n i
  change (b * a) ^ 3 = 1
  calc
    (b * a) ^ 3 = ((a * b)⁻¹) ^ 3 := by rw [mul_inv_rev, ha, hb]
    _ = ((a * b) ^ 3)⁻¹ := by rw [inv_pow]
    _ = 1 := by rw [hab, inv_one]

public theorem schurCoxeterQuotientSimple_isLiftable (n : Nat) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A (n + 4))
      (schurCoxeterQuotientSimple n) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [CoxeterMatrix.A, pow_two] using
      schurCoxeterQuotientSimple_sq n i
  by_cases hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val
  · rcases hadj with hji | hij'
    · let k : Fin (n + 3) := ⟨j.val, by omega⟩
      have hk0 : k.castSucc = j := by ext; simp [k]
      have hk1 : k.succ = i := by ext; simp [k]; omega
      simpa [CoxeterMatrix.A, hij, hji, hk0, hk1] using
        __ch5_SchurPresentation_schurCoxeterQuotientSimple_braid_rev n k
    · let k : Fin (n + 3) := ⟨i.val, by omega⟩
      have hk0 : k.castSucc = i := by ext; simp [k]
      have hk1 : k.succ = j := by ext; simp [k]; omega
      simpa [CoxeterMatrix.A, hij, hij', hk0, hk1] using
        schurCoxeterQuotientSimple_braid n k
  · have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
    simpa [CoxeterMatrix.A, hij, hadj] using
      schurCoxeterQuotientSimple_far n hfar

@[expose] public def coxeterToSchurCoxeterQuotient (n : Nat) :
    TypeACoxeterGroup n →* SchurCoxeterQuotient n :=
  (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift
    ⟨schurCoxeterQuotientSimple n,
      schurCoxeterQuotientSimple_isLiftable n⟩

public theorem coxeterToSchurCoxeterQuotient_simple (n : Nat)
    (i : Fin (n + 4)) :
    coxeterToSchurCoxeterQuotient n
        ((CoxeterMatrix.A (n + 4)).simple i) =
      schurCoxeterQuotientSimple n i := by
  change coxeterToSchurCoxeterQuotient n
      ((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i) = _
  exact (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift_apply_simple
    (schurCoxeterQuotientSimple_isLiftable n) i

set_option backward.isDefEq.respectTransparency false in
public theorem schurCoxeterQuotientProjection_comp_coxeterTo (n : Nat) :
    (schurCoxeterQuotientProjection n).comp
        (coxeterToSchurCoxeterQuotient n) =
      MonoidHom.id (TypeACoxeterGroup n) := by
  apply (CoxeterMatrix.A (n + 4)).toCoxeterSystem.ext_simple
  intro i
  change schurCoxeterQuotientProjection n
      (coxeterToSchurCoxeterQuotient n
        ((CoxeterMatrix.A (n + 4)).simple i)) =
    (CoxeterMatrix.A (n + 4)).simple i
  rw [coxeterToSchurCoxeterQuotient_simple]
  change schurCoxeterProjection n (PresentedGroup.of (.adjacent i)) = _
  rw [schurCoxeterProjection_adjacent]

set_option backward.isDefEq.respectTransparency false in
public theorem coxeterTo_comp_schurCoxeterQuotientProjection (n : Nat) :
    (coxeterToSchurCoxeterQuotient n).comp
        (schurCoxeterQuotientProjection n) =
      MonoidHom.id (SchurCoxeterQuotient n) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.zpowers (schurCentral n)) x
  have hhom :
      (coxeterToSchurCoxeterQuotient n).comp (schurCoxeterProjection n) =
        QuotientGroup.mk' (Subgroup.zpowers (schurCentral n)) := by
    apply PresentedGroup.ext
    intro gen
    cases gen with
    | central =>
        change 1 = QuotientGroup.mk'
          (Subgroup.zpowers (schurCentral n)) (schurCentral n)
        exact (schurCoxeterQuotient_mk_central n).symm
    | adjacent i =>
        simp [schurCoxeterProjection_adjacent,
          coxeterToSchurCoxeterQuotient_simple,
          schurCoxeterQuotientSimple]
  change coxeterToSchurCoxeterQuotient n (schurCoxeterProjection n g) = _
  exact DFunLike.congr_fun hhom g

@[expose] public def schurCoxeterQuotientMulEquiv (n : Nat) :
    SchurCoxeterQuotient n ≃* TypeACoxeterGroup n :=
  MonoidHom.toMulEquiv (schurCoxeterQuotientProjection n)
    (coxeterToSchurCoxeterQuotient n)
    (coxeterTo_comp_schurCoxeterQuotientProjection n)
    (schurCoxeterQuotientProjection_comp_coxeterTo n)

public theorem zpowers_schurCentral_eq_schurCoxeterProjection_ker (n : Nat) :
    Subgroup.zpowers (schurCentral n) = (schurCoxeterProjection n).ker := by
  apply (QuotientGroup.injective_lift_iff
    (Subgroup.zpowers (schurCentral n)) (schurCoxeterProjection n) (by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact schurCoxeterProjection_central n)).mp
  change Function.Injective (schurCoxeterQuotientProjection n)
  exact (schurCoxeterQuotientMulEquiv n).injective

@[expose] public def schurSymmetricQuotientProjection (n : Nat) :
    SchurCoxeterQuotient n →* Equiv.Perm (Fin (n + 5)) :=
  QuotientGroup.lift (Subgroup.zpowers (schurCentral n))
    (schurSymmetricProjection n)
    (by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact schurSymmetricProjection_central n)

public theorem schurSymmetricQuotientProjection_surjective (n : Nat) :
    Function.Surjective (schurSymmetricQuotientProjection n) :=
  QuotientGroup.lift_surjective_of_surjective
    (Subgroup.zpowers (schurCentral n)) (schurSymmetricProjection n)
    (schurSymmetricProjection_surjective n)
    (by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact schurSymmetricProjection_central n)

@[expose] public def typeACoxeterPermutationProjection (n : Nat) :
    TypeACoxeterGroup n →* Equiv.Perm (Fin (n + 5)) :=
  (schurSymmetricQuotientProjection n).comp
    (schurCoxeterQuotientMulEquiv n).symm.toMonoidHom

set_option backward.isDefEq.respectTransparency false in
public theorem typeACoxeterPermutationProjection_simple (n : Nat)
    (i : Fin (n + 4)) :
    typeACoxeterPermutationProjection n
        ((CoxeterMatrix.A (n + 4)).simple i) = adjacentSwap n i := by
  change schurSymmetricQuotientProjection n
      (coxeterToSchurCoxeterQuotient n
        ((CoxeterMatrix.A (n + 4)).simple i)) = adjacentSwap n i
  rw [coxeterToSchurCoxeterQuotient_simple]
  change schurSymmetricProjection n (PresentedGroup.of (.adjacent i)) = _
  exact schurSymmetricProjection_adjacent n i

public theorem typeACoxeterPermutationProjection_surjective (n : Nat) :
    Function.Surjective (typeACoxeterPermutationProjection n) :=
  (schurSymmetricQuotientProjection_surjective n).comp
    (schurCoxeterQuotientMulEquiv n).symm.surjective

public theorem schurSymmetricProjection_ker_eq_zpowers_iff (n : Nat) :
    (schurSymmetricProjection n).ker = Subgroup.zpowers (schurCentral n) ↔
      Function.Injective (typeACoxeterPermutationProjection n) := by
  let N := Subgroup.zpowers (schurCentral n)
  have hN : N ≤ (schurSymmetricProjection n).ker :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr
      (schurSymmetricProjection_central n))
  have hlift :
      Function.Injective (schurSymmetricQuotientProjection n) ↔
        N = (schurSymmetricProjection n).ker := by
    simpa [N, schurSymmetricQuotientProjection] using
      (QuotientGroup.injective_lift_iff N (schurSymmetricProjection n) hN)
  constructor
  · intro hker
    have hq : Function.Injective (schurSymmetricQuotientProjection n) :=
      hlift.mpr hker.symm
    exact hq.comp (schurCoxeterQuotientMulEquiv n).symm.injective
  · intro htype
    have hq : Function.Injective (schurSymmetricQuotientProjection n) := by
      intro x y hxy
      have hxy' :
          typeACoxeterPermutationProjection n
              (schurCoxeterQuotientMulEquiv n x) =
            typeACoxeterPermutationProjection n
              (schurCoxeterQuotientMulEquiv n y) := by
        simpa [typeACoxeterPermutationProjection] using hxy
      exact (schurCoxeterQuotientMulEquiv n).injective (htype hxy')
    exact (hlift.mp hq).symm

public abbrev SchurAlternatingGroup (n : Nat) :=
  (alternatingGroup (Fin (n + 5))).comap (schurSymmetricProjection n)

@[expose] public def schurAlternatingProjection (n : Nat) :
    SchurAlternatingGroup n →* alternatingGroup (Fin (n + 5)) where
  toFun x := ⟨schurSymmetricProjection n x.1, x.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

public theorem schurAlternatingProjection_surjective (n : Nat) :
    Function.Surjective (schurAlternatingProjection n) := by
  intro y
  obtain ⟨x, hx⟩ := schurSymmetricProjection_surjective n y.1
  have hxmem : x ∈ SchurAlternatingGroup n := by
    change schurSymmetricProjection n x ∈ alternatingGroup (Fin (n + 5))
    simp [hx]
  refine ⟨⟨x, hxmem⟩, ?_⟩
  apply Subtype.ext
  exact hx

@[expose] public def schurAlternatingCentral (n : Nat) : SchurAlternatingGroup n :=
  ⟨schurCentral n, by
    change schurSymmetricProjection n (schurCentral n) ∈
      alternatingGroup (Fin (n + 5))
    rw [schurSymmetricProjection_central]
    exact Subgroup.one_mem _⟩

public theorem schurAlternatingCentral_sq (n : Nat) :
    schurAlternatingCentral n ^ 2 = 1 := by
  apply Subtype.ext
  exact schurCentral_sq n

public theorem schurAlternatingCentral_ne_one (n : Nat) :
    schurAlternatingCentral n ≠ 1 := by
  intro h
  apply schurCentral_ne_one n
  exact congrArg Subtype.val h

public theorem orderOf_schurAlternatingCentral (n : Nat) :
    orderOf (schurAlternatingCentral n) = 2 :=
  orderOf_eq_prime (schurAlternatingCentral_sq n)
    (schurAlternatingCentral_ne_one n)

public theorem schurAlternatingCentral_mem_ker (n : Nat) :
    schurAlternatingCentral n ∈ (schurAlternatingProjection n).ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change schurSymmetricProjection n (schurCentral n) = 1
  exact schurSymmetricProjection_central n

public theorem schurAlternatingProjection_central (n : Nat) :
    schurAlternatingProjection n (schurAlternatingCentral n) = 1 :=
  MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n)

public theorem schurAlternatingCentral_mem_center (n : Nat) :
    schurAlternatingCentral n ∈ Subgroup.center (SchurAlternatingGroup n) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x.1

public theorem zpowers_schurCentral_le_symmetricProjection_ker (n : Nat) :
    Subgroup.zpowers (schurCentral n) ≤ (schurSymmetricProjection n).ker := by
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  exact schurSymmetricProjection_central n

public theorem natCard_zpowers_schurCentral (n : Nat) :
    Nat.card (Subgroup.zpowers (schurCentral n)) = 2 := by
  rw [Nat.card_zpowers, orderOf_schurCentral]

public theorem zpowers_schurAlternatingCentral_le_ker (n : Nat) :
    Subgroup.zpowers (schurAlternatingCentral n) ≤
      (schurAlternatingProjection n).ker := by
  rw [Subgroup.zpowers_le]
  exact schurAlternatingCentral_mem_ker n

public theorem natCard_zpowers_schurAlternatingCentral (n : Nat) :
    Nat.card (Subgroup.zpowers (schurAlternatingCentral n)) = 2 := by
  rw [Nat.card_zpowers, orderOf_schurAlternatingCentral]

public theorem schurAlternatingProjection_ker_eq_zpowers_of_typeA_injective
    (n : Nat) (hinj : Function.Injective (typeACoxeterPermutationProjection n)) :
    (schurAlternatingProjection n).ker =
      Subgroup.zpowers (schurAlternatingCentral n) := by
  have hsym :
      (schurSymmetricProjection n).ker =
        Subgroup.zpowers (schurCentral n) :=
    (schurSymmetricProjection_ker_eq_zpowers_iff n).mpr hinj
  apply le_antisymm
  · intro x hx
    have hxSym : x.1 ∈ (schurSymmetricProjection n).ker := by
      rw [MonoidHom.mem_ker]
      have hx' := MonoidHom.mem_ker.mp hx
      exact congrArg Subtype.val hx'
    rw [hsym, Subgroup.mem_zpowers_iff] at hxSym
    rcases hxSym with ⟨k, hk⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  · exact zpowers_schurAlternatingCentral_le_ker n

public theorem natCard_ker_schurAlternatingProjection_of_typeA_injective
    (n : Nat) (hinj : Function.Injective (typeACoxeterPermutationProjection n)) :
    Nat.card (schurAlternatingProjection n).ker = 2 := by
  rw [schurAlternatingProjection_ker_eq_zpowers_of_typeA_injective n hinj,
    natCard_zpowers_schurAlternatingCentral]

namespace TypeANormalForm

public abbrev Group (r : Nat) := (CoxeterMatrix.A r).Group

@[expose] public def inclusionGenerator (r : Nat) : Fin r → Group (r + 1) :=
  fun i => (CoxeterMatrix.A (r + 1)).simple i.castSucc

set_option backward.isDefEq.respectTransparency false in
public theorem inclusionGenerator_isLiftable (r : Nat) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A r) (inclusionGenerator r) := by
  intro i j
  change (((CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple i.castSucc) *
      (CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple j.castSucc) ^
        CoxeterMatrix.A r i j = 1
  simpa [CoxeterMatrix.A] using
    ((CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple_mul_simple_pow
      i.castSucc j.castSucc)

@[expose] public def inclusion (r : Nat) : Group r →* Group (r + 1) :=
  (CoxeterMatrix.A r).toCoxeterSystem.lift
    ⟨inclusionGenerator r, inclusionGenerator_isLiftable r⟩

public theorem inclusion_simple (r : Nat) (i : Fin r) :
    inclusion r ((CoxeterMatrix.A r).simple i) =
      (CoxeterMatrix.A (r + 1)).simple i.castSucc := by
  change inclusion r ((CoxeterMatrix.A r).toCoxeterSystem.simple i) = _
  exact (CoxeterMatrix.A r).toCoxeterSystem.lift_apply_simple
    (inclusionGenerator_isLiftable r) i

public theorem simple_sq (r : Nat) (i : Fin r) :
    (CoxeterMatrix.A r).simple i ^ 2 = 1 := by
  change (CoxeterMatrix.A r).toCoxeterSystem.simple i ^ 2 = 1
  exact (CoxeterMatrix.A r).toCoxeterSystem.simple_sq i

public theorem simple_braid (m : Nat) (i : Fin (m + 1)) :
    ((CoxeterMatrix.A (m + 2)).simple i.castSucc *
        (CoxeterMatrix.A (m + 2)).simple i.succ *
          (CoxeterMatrix.A (m + 2)).simple i.castSucc) =
      ((CoxeterMatrix.A (m + 2)).simple i.succ *
        (CoxeterMatrix.A (m + 2)).simple i.castSucc *
          (CoxeterMatrix.A (m + 2)).simple i.succ) := by
  let a := (CoxeterMatrix.A (m + 2)).simple i.castSucc
  let b := (CoxeterMatrix.A (m + 2)).simple i.succ
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  have hp : (a * b) ^ 3 = 1 := by
    change (((CoxeterMatrix.A (m + 2)).toCoxeterSystem.simple i.castSucc) *
        (CoxeterMatrix.A (m + 2)).toCoxeterSystem.simple i.succ) ^ 3 = 1
    simpa [CoxeterMatrix.A, hne] using
      ((CoxeterMatrix.A (m + 2)).toCoxeterSystem.simple_mul_simple_pow
        i.castSucc i.succ)
  have hb2 : b * b = 1 := by
    simpa [b, pow_two] using simple_sq (m + 2) i.succ
  have h2 : (a * b) ^ 2 = (a * b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa [pow_succ, mul_assoc] using hp
  have ha : a⁻¹ = a := by
    have ha2 : a * a = 1 := by
      simpa [a, pow_two] using simple_sq (m + 2) i.castSucc
    exact (eq_inv_of_mul_eq_one_right ha2).symm
  have hb : b⁻¹ = b := (eq_inv_of_mul_eq_one_right hb2).symm
  change a * b * a = b * a * b
  apply mul_right_cancel (b := b)
  simpa [pow_two, mul_assoc, mul_inv_rev, ha, hb, hb2] using h2

public theorem simple_commute_of_far (r : Nat) {i j : Fin r}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute ((CoxeterMatrix.A r).simple i) ((CoxeterMatrix.A r).simple j) := by
  let a := (CoxeterMatrix.A r).simple i
  let b := (CoxeterMatrix.A r).simple j
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    omega
  have hji : j.val + 1 ≠ i.val := by omega
  have hij' : i.val + 1 ≠ j.val := by omega
  have hp : (a * b) ^ 2 = 1 := by
    change (((CoxeterMatrix.A r).toCoxeterSystem.simple i) *
        (CoxeterMatrix.A r).toCoxeterSystem.simple j) ^ 2 = 1
    simpa [CoxeterMatrix.A, hij, hji, hij'] using
      ((CoxeterMatrix.A r).toCoxeterSystem.simple_mul_simple_pow i j)
  have ha2 : a * a = 1 := by
    simpa [a, pow_two] using simple_sq r i
  have hb2 : b * b = 1 := by
    simpa [b, pow_two] using simple_sq r j
  have hab : a * b = (a * b)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hp)
  have ha : a⁻¹ = a := (eq_inv_of_mul_eq_one_right ha2).symm
  have hb : b⁻¹ = b := (eq_inv_of_mul_eq_one_right hb2).symm
  change a * b = b * a
  simpa [mul_inv_rev, ha, hb] using hab

@[expose] public def descendingSimpleIndex (r j : Nat) : Fin (r + 1) :=
  ⟨r - j, Nat.lt_succ_of_le (Nat.sub_le r j)⟩

@[expose] public def representativeWord (r : Nat) (k : Fin (r + 2)) :
    List (Fin (r + 1)) :=
  (List.range k).map (descendingSimpleIndex r)

@[expose] public def representative (r : Nat) (k : Fin (r + 2)) : Group (r + 1) :=
  (CoxeterMatrix.A (r + 1)).toCoxeterSystem.wordProd (representativeWord r k)

public theorem representative_zero (r : Nat) :
    representative r (0 : Fin (r + 2)) = 1 := by
  simp [representative, representativeWord]

public theorem representative_succ (r : Nat) (k : Fin (r + 1)) :
    representative r k.succ =
      representative r k.castSucc *
        (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) := by
  rw [representative, representative, representativeWord, representativeWord]
  simp only [Fin.val_succ, Fin.val_castSucc, List.range_succ, List.map_append,
    List.map_singleton]
  simpa [List.concat_eq_append] using
    ((CoxeterMatrix.A (r + 1)).toCoxeterSystem.wordProd_concat
      (descendingSimpleIndex r k) ((List.range k).map (descendingSimpleIndex r)))

public theorem simple_commutes_representative_of_add_lt (r : Nat)
    (i : Fin (r + 1)) (k : Fin (r + 2)) (hfar : i.val + k.val + 1 < r + 1) :
    Commute ((CoxeterMatrix.A (r + 1)).simple i) (representative r k) := by
  change Commute ((CoxeterMatrix.A (r + 1)).simple i)
    (((representativeWord r k).map (CoxeterMatrix.A (r + 1)).simple).prod)
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨j, hj, rfl⟩
  rw [representativeWord, List.mem_map] at hj
  rcases hj with ⟨t, ht, rfl⟩
  rw [List.mem_range] at ht
  apply simple_commute_of_far
  left
  change i.val + 1 < r - t
  omega

public theorem representative_succ_mul_last (r : Nat) (k : Fin (r + 1)) :
    representative r k.succ *
        (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) =
      representative r k.castSucc := by
  rw [representative_succ]
  have hs :
      (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) *
          (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) = 1 := by
    change (CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple
        (descendingSimpleIndex r k) *
      (CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple
        (descendingSimpleIndex r k) = 1
    exact (CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple_mul_simple_self _
  rw [mul_assoc, hs, mul_one]

@[expose] public def previousSimpleIndex (r : Nat) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩

public theorem representative_mul_simple_of_endpoint_lt (r : Nat)
    (k : Fin (r + 2)) (i : Fin (r + 1)) (hinside : r + 1 - k.val < i.val) :
    representative r k * (CoxeterMatrix.A (r + 1)).simple i =
      (CoxeterMatrix.A (r + 1)).simple (previousSimpleIndex r i) *
        representative r k := by
  induction k using Fin.induction with
  | zero =>
      simp only [Fin.val_zero, Nat.sub_zero] at hinside
      omega
  | succ k ih =>
      have hinside' : r - k.val < i.val := by
        simpa [Nat.succ_sub_succ_eq_sub] using hinside
      rw [representative_succ]
      by_cases hadj : i.val = r - k.val + 1
      · have hk0 : k ≠ 0 := by
          intro hk
          subst k
          simp only [Fin.val_zero, Nat.sub_zero] at hadj
          omega
        obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero hk0
        simp only [Fin.val_succ] at hadj
        cases r with
        | zero => exact Fin.elim0 l
        | succ m =>
            let q : Fin (m + 1) := descendingSimpleIndex m l
            have hi : i = q.succ := by
              ext
              change i.val = (m - l.val) + 1
              omega
            have hend : descendingSimpleIndex (m + 1) l.succ = q.castSucc := by
              ext
              change (m + 1) - (l.val + 1) = m - l.val
              omega
            have hprev : descendingSimpleIndex (m + 1) l.castSucc = q.succ := by
              ext
              change (m + 1) - l.val = (m - l.val) + 1
              omega
            have hfin : l.succ.castSucc = l.castSucc.succ := by
              ext
              simp
            have hprevious : previousSimpleIndex (m + 1) q.succ = q.castSucc := by
              ext
              simp [previousSimpleIndex]
            have hcomm :
                Commute ((CoxeterMatrix.A (m + 2)).simple q.castSucc)
                  (representative (m + 1) l.castSucc.castSucc) := by
              apply simple_commutes_representative_of_add_lt
              change q.val + l.val + 1 < m + 2
              simp [q, descendingSimpleIndex]
              omega
            rw [hi, hend, hfin, representative_succ (m + 1) l.castSucc, hprev,
              hprevious]
            let P := representative (m + 1) l.castSucc.castSucc
            let a := (CoxeterMatrix.A (m + 2)).simple q.castSucc
            let b := (CoxeterMatrix.A (m + 2)).simple q.succ
            change (P * b) * a * b = a * ((P * b) * a)
            calc
              (P * b) * a * b = P * (b * a * b) := by simp [mul_assoc]
              _ = P * (a * b * a) := by rw [← simple_braid m q]
              _ = (P * a) * b * a := by simp [mul_assoc]
              _ = (a * P) * b * a := by rw [hcomm.eq.symm]
              _ = a * ((P * b) * a) := by simp [mul_assoc]
      · have hfar :
            Commute ((CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k))
              ((CoxeterMatrix.A (r + 1)).simple i) := by
          apply simple_commute_of_far
          left
          change r - k.val + 1 < i.val
          omega
        have hih := ih (by
          simp only [Fin.val_castSucc]
          rw [Nat.succ_sub (Nat.le_of_lt_succ k.isLt)]
          omega)
        calc
          (representative r k.castSucc *
                (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k)) *
              (CoxeterMatrix.A (r + 1)).simple i =
              representative r k.castSucc *
                ((CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) *
                  (CoxeterMatrix.A (r + 1)).simple i) := by simp [mul_assoc]
          _ = representative r k.castSucc *
                ((CoxeterMatrix.A (r + 1)).simple i *
                  (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k)) := by
                rw [hfar.eq]
          _ = (representative r k.castSucc *
                (CoxeterMatrix.A (r + 1)).simple i) *
              (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) := by
                simp [mul_assoc]
          _ = ((CoxeterMatrix.A (r + 1)).simple (previousSimpleIndex r i) *
                representative r k.castSucc) *
              (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k) := by
                rw [hih]
          _ = (CoxeterMatrix.A (r + 1)).simple (previousSimpleIndex r i) *
              (representative r k.castSucc *
                (CoxeterMatrix.A (r + 1)).simple (descendingSimpleIndex r k)) := by
                simp [mul_assoc]

public theorem representative_mul_simple_normalForm (r : Nat)
    (k : Fin (r + 2)) (i : Fin (r + 1)) :
    ∃ h : Group r, ∃ k' : Fin (r + 2),
      representative r k * (CoxeterMatrix.A (r + 1)).simple i =
        inclusion r h * representative r k' := by
  by_cases hfar : i.val + k.val < r
  · let j : Fin r := ⟨i.val, by omega⟩
    refine ⟨(CoxeterMatrix.A r).simple j, k, ?_⟩
    have hi : i = j.castSucc := by
      ext
      rfl
    calc
      representative r k * (CoxeterMatrix.A (r + 1)).simple i =
          (CoxeterMatrix.A (r + 1)).simple i * representative r k :=
        (simple_commutes_representative_of_add_lt r i k (by omega)).eq.symm
      _ = inclusion r ((CoxeterMatrix.A r).simple j) * representative r k := by
        rw [inclusion_simple, hi]
  · by_cases hextend : i.val + k.val = r
    · let k0 : Fin (r + 1) := ⟨k.val, by omega⟩
      have hk : k = k0.castSucc := by
        ext
        rfl
      have hi : i = descendingSimpleIndex r k0 := by
        ext
        change i.val = r - k.val
        omega
      refine ⟨1, k0.succ, ?_⟩
      simp only [map_one, one_mul]
      simpa [hk, hi] using (representative_succ r k0).symm
    · by_cases hcancel : i.val + k.val = r + 1
      · have hk0 : k ≠ 0 := by
          intro hk
          subst k
          simp only [Fin.val_zero, add_zero] at hcancel
          omega
        obtain ⟨k0, rfl⟩ := Fin.eq_succ_of_ne_zero hk0
        have hi : i = descendingSimpleIndex r k0 := by
          ext
          change i.val = r - k0.val
          simp only [Fin.val_succ] at hcancel
          omega
        refine ⟨1, k0.castSucc, ?_⟩
        simp only [map_one, one_mul]
        simpa [hi] using representative_succ_mul_last r k0
      · have hinside : r + 1 - k.val < i.val := by omega
        have hi0 : 0 < i.val := by omega
        let j : Fin r := ⟨i.val - 1, by omega⟩
        have hprevious : previousSimpleIndex r i = j.castSucc := by
          ext
          rfl
        refine ⟨(CoxeterMatrix.A r).simple j, k, ?_⟩
        calc
          representative r k * (CoxeterMatrix.A (r + 1)).simple i =
              (CoxeterMatrix.A (r + 1)).simple (previousSimpleIndex r i) *
                representative r k :=
            representative_mul_simple_of_endpoint_lt r k i hinside
          _ = inclusion r ((CoxeterMatrix.A r).simple j) * representative r k := by
            rw [inclusion_simple, hprevious]

public theorem exists_normalForm (r : Nat) (w : Group (r + 1)) :
    ∃ h : Group r, ∃ k : Fin (r + 2), w = inclusion r h * representative r k := by
  apply (CoxeterMatrix.A (r + 1)).toCoxeterSystem.simple_induction_right w
  · refine ⟨1, 0, ?_⟩
    simp [representative_zero]
  · intro w i hw
    rcases hw with ⟨h, k, rfl⟩
    rcases representative_mul_simple_normalForm r k i with ⟨h', k', hk'⟩
    refine ⟨h * h', k', ?_⟩
    rw [mul_assoc]
    change inclusion r h *
        (representative r k * (CoxeterMatrix.A (r + 1)).simple i) =
      inclusion r (h * h') * representative r k'
    rw [hk']
    simp [mul_assoc]

@[expose] public def normalFormMap (r : Nat) : Group r × Fin (r + 2) → Group (r + 1) :=
  fun hk => inclusion r hk.1 * representative r hk.2

public theorem normalFormMap_surjective (r : Nat) : Function.Surjective (normalFormMap r) := by
  intro w
  rcases exists_normalForm r w with ⟨h, k, rfl⟩
  exact ⟨(h, k), rfl⟩

public theorem group_zero_eq_one (w : Group 0) : w = 1 := by
  apply (CoxeterMatrix.A 0).toCoxeterSystem.simple_induction_right w
  · rfl
  · intro _ i _
    exact Fin.elim0 i

public theorem group_finite (r : Nat) : Finite (Group r) := by
  induction r with
  | zero =>
      apply Finite.of_surjective (fun _ : Unit => (1 : Group 0))
      intro w
      exact ⟨(), (group_zero_eq_one w).symm⟩
  | succ r ih =>
      let : Finite (Group r) := ih
      exact Finite.of_surjective (normalFormMap r) (normalFormMap_surjective r)

public theorem natCard_group_le_factorial (r : Nat) :
    Nat.card (Group r) ≤ (r + 1).factorial := by
  induction r with
  | zero =>
      have hsurj : Function.Surjective (fun _ : Unit => (1 : Group 0)) := by
        intro w
        exact ⟨(), (group_zero_eq_one w).symm⟩
      simpa using Nat.card_le_card_of_surjective (fun _ : Unit => (1 : Group 0)) hsurj
  | succ r ih =>
      let : Finite (Group r) := group_finite r
      calc
        Nat.card (Group (r + 1)) ≤ Nat.card (Group r × Fin (r + 2)) :=
          Nat.card_le_card_of_surjective (normalFormMap r) (normalFormMap_surjective r)
        _ = Nat.card (Group r) * (r + 2) := by simp
        _ ≤ (r + 1).factorial * (r + 2) := Nat.mul_le_mul_right (r + 2) ih
        _ = (r + 2) * (r + 1).factorial := by ac_rfl
        _ = (r + 2).factorial := (Nat.factorial_succ (r + 1)).symm

end TypeANormalForm

public theorem typeACoxeterPermutationProjection_injective (n : Nat) :
    Function.Injective (typeACoxeterPermutationProjection n) := by
  let : Finite (TypeACoxeterGroup n) := TypeANormalForm.group_finite (n + 4)
  refine ((typeACoxeterPermutationProjection_surjective n).bijective_of_nat_card_le ?_).1
  exact calc
    Nat.card (TypeACoxeterGroup n) ≤ (n + 5).factorial := by
      simpa [TypeACoxeterGroup, TypeANormalForm.Group, Nat.add_assoc] using
        TypeANormalForm.natCard_group_le_factorial (n + 4)
    _ = Nat.card (Equiv.Perm (Fin (n + 5))) := by
      rw [Nat.card_perm, Nat.card_fin]

public theorem schurSymmetricProjection_ker_eq_zpowers (n : Nat) :
    (schurSymmetricProjection n).ker = Subgroup.zpowers (schurCentral n) :=
  (schurSymmetricProjection_ker_eq_zpowers_iff n).mpr
    (typeACoxeterPermutationProjection_injective n)

public theorem schurAlternatingProjection_ker_eq_zpowers (n : Nat) :
    (schurAlternatingProjection n).ker =
      Subgroup.zpowers (schurAlternatingCentral n) :=
  schurAlternatingProjection_ker_eq_zpowers_of_typeA_injective n
    (typeACoxeterPermutationProjection_injective n)

public theorem natCard_ker_schurAlternatingProjection (n : Nat) :
    Nat.card (schurAlternatingProjection n).ker = 2 :=
  natCard_ker_schurAlternatingProjection_of_typeA_injective n
    (typeACoxeterPermutationProjection_injective n)

@[expose] public def schurAlternatingThreeCycle (n : Nat) (i : Fin (n + 3)) :
    SchurAlternatingGroup n :=
  ⟨PresentedGroup.of (.adjacent i.castSucc) * PresentedGroup.of (.adjacent i.succ), by
    change schurSymmetricProjection n
        (PresentedGroup.of (.adjacent i.castSucc) * PresentedGroup.of (.adjacent i.succ)) ∈
      alternatingGroup (Fin (n + 5))
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      schurSymmetricProjection_adjacent, schurSymmetricProjection_adjacent,
      map_mul]
    simp [adjacentSwap, Equiv.Perm.sign_swap', ne_of_lt i.castSucc_lt_succ,
      ne_of_lt i.castSucc.castSucc_lt_succ]⟩

public theorem schurAlternatingThreeCycle_pow_three (n : Nat) (i : Fin (n + 3)) :
    schurAlternatingThreeCycle n i ^ 3 = schurAlternatingCentral n := by
  apply Subtype.ext
  change (PresentedGroup.of (.adjacent i.castSucc) *
      PresentedGroup.of (.adjacent i.succ) : SchurPresentedGroup n) ^ 3 = schurCentral n
  exact schurAdjacent_mul_pow_three n i

public theorem schurAlternatingThreeCycle_mul_sq (n : Nat) (i : Fin (n + 2)) :
    (schurAlternatingThreeCycle n i.castSucc *
        schurAlternatingThreeCycle n i.succ) ^ 2 = schurAlternatingCentral n := by
  apply Subtype.ext
  let a : Fin (n + 4) := i.castSucc.castSucc
  let b : Fin (n + 4) := i.castSucc.succ
  let c : Fin (n + 4) := i.succ.succ
  have hmiddle : i.succ.castSucc = b := by
    ext
    rfl
  change (((PresentedGroup.of (.adjacent a) * PresentedGroup.of (.adjacent b)) *
      (PresentedGroup.of (.adjacent i.succ.castSucc) *
        PresentedGroup.of (.adjacent c))) : SchurPresentedGroup n) ^ 2 = schurCentral n
  rw [hmiddle]
  let ta : SchurPresentedGroup n := PresentedGroup.of (.adjacent a)
  let tb : SchurPresentedGroup n := PresentedGroup.of (.adjacent b)
  let tc : SchurPresentedGroup n := PresentedGroup.of (.adjacent c)
  let z := schurCentral n
  have hb2 : tb * tb = z := by
    simpa [tb, z, pow_two] using schurAdjacent_sq n b
  have hac : a.val + 1 < c.val := by
    simp [a, c]
  have hfar2 : (ta * tc) ^ 2 = z := by
    exact schurAdjacent_far_mul_sq n (i := a) (j := c) (Or.inl hac)
  have hza : Commute z ta := schurCentral_commutes_generator n (.adjacent a)
  have hzc : Commute z tc := schurCentral_commutes_generator n (.adjacent c)
  have hzprod : Commute z (ta * tc) := hza.mul_right hzc
  change ((ta * tb) * (tb * tc)) ^ 2 = z
  calc
    ((ta * tb) * (tb * tc)) ^ 2 = (ta * (tb * tb) * tc) ^ 2 := by
      congr 1
    _ = (ta * z * tc) ^ 2 := by rw [hb2]
    _ = (z * (ta * tc)) ^ 2 := by
      congr 1
      rw [hza.eq.symm]
      simp [mul_assoc]
    _ = z ^ 2 * (ta * tc) ^ 2 := hzprod.mul_pow 2
    _ = z ^ 2 * z := by rw [hfar2]
    _ = z := by rw [schurCentral_sq]; simp

public theorem schurAlternatingCentral_mem_commutator (n : Nat) :
    schurAlternatingCentral n ∈ commutator (SchurAlternatingGroup n) := by
  let q := QuotientGroup.mk' (commutator (SchurAlternatingGroup n))
  let i : Fin (n + 2) := 0
  let x := schurAlternatingThreeCycle n i.castSucc
  let y := schurAlternatingThreeCycle n i.succ
  let z := schurAlternatingCentral n
  have hx : q x ^ 3 = q z := by
    simpa only [map_pow, x, z] using
      congrArg q (schurAlternatingThreeCycle_pow_three n i.castSucc)
  have hy : q y ^ 3 = q z := by
    simpa only [map_pow, y, z] using
      congrArg q (schurAlternatingThreeCycle_pow_three n i.succ)
  have hxy : (q x * q y) ^ 2 = q z := by
    simpa only [map_mul, map_pow, x, y, z] using
      congrArg q (schurAlternatingThreeCycle_mul_sq n i)
  have hz : q z ^ 2 = 1 := by
    simpa only [map_pow, map_one, z] using
      congrArg q (schurAlternatingCentral_sq n)
  let : IsMulCommutative
      ((SchurAlternatingGroup n) ⧸ commutator (SchurAlternatingGroup n)) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hcomm : Commute (q x) (q y) := mul_comm' _ _
  have hy_sq : q y ^ 2 = q x := by
    apply mul_left_cancel (a := q x ^ 2)
    calc
      q x ^ 2 * q y ^ 2 = (q x * q y) ^ 2 :=
        (hcomm.mul_pow 2).symm
      _ = q z := hxy
      _ = q x ^ 3 := hx.symm
      _ = q x ^ 2 * q x := by rw [pow_succ]
  have hqz : q z = 1 := calc
    q z = q x ^ 3 := hx.symm
    _ = (q y ^ 2) ^ 3 := by rw [hy_sq]
    _ = (q y ^ 3) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
    _ = q z ^ 2 := by rw [hy]
    _ = 1 := hz
  rw [← QuotientGroup.eq_one_iff]
  exact hqz

public theorem schurAlternating_commutator_eq_top (n : Nat) :
    commutator (SchurAlternatingGroup n) = ⊤ := by
  let f := schurAlternatingProjection n
  have hmap : (commutator (SchurAlternatingGroup n)).map f = ⊤ := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (schurAlternatingProjection_surjective n)]
    exact commutator_alternatingGroup_eq_top (by simp)
  have hker : f.ker ≤ commutator (SchurAlternatingGroup n) := by
    rw [schurAlternatingProjection_ker_eq_zpowers]
    exact Subgroup.zpowers_le.mpr
      (schurAlternatingCentral_mem_commutator n)
  apply top_unique
  intro g _
  have hfg : f g ∈ (commutator (SchurAlternatingGroup n)).map f := by
    rw [hmap]
    exact Subgroup.mem_top _
  rcases hfg with ⟨d, hd, hfd⟩
  have hgd : g * d⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfd]
    simp
  have hprod : (g * d⁻¹) * d ∈ commutator (SchurAlternatingGroup n) :=
    Subgroup.mul_mem _ (hker hgd) hd
  simpa using hprod

public theorem schurAlternating_center_eq_ker (n : Nat) :
    Subgroup.center (SchurAlternatingGroup n) = (schurAlternatingProjection n).ker := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hcenter : schurAlternatingProjection n x ∈
        Subgroup.center (alternatingGroup (Fin (n + 5))) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨g, rfl⟩ := schurAlternatingProjection_surjective n y
      rw [← map_mul, ← map_mul, hx g]
    rw [alternatingGroup.center_eq_bot (by simp)] at hcenter
    exact hcenter
  · rw [schurAlternatingProjection_ker_eq_zpowers, Subgroup.zpowers_le]
    exact schurAlternatingCentral_mem_center n

public instance schurAlternating_isPerfect (n : Nat) :
    Group.IsPerfect (SchurAlternatingGroup n) :=
  ⟨schurAlternating_commutator_eq_top n⟩

public instance schurAlternating_finite (n : Nat) :
    Finite (SchurAlternatingGroup n) := by
  rw [(schurAlternatingProjection n).finite_iff_finite_ker_range]
  constructor
  · apply Nat.finite_of_card_ne_zero
    rw [natCard_ker_schurAlternatingProjection]
    norm_num
  · infer_instance

@[expose]
public noncomputable def alternatingCenterQuotientEquiv (n : Nat) :
    alternatingGroup (Fin (n + 5)) ⧸
        Subgroup.center (alternatingGroup (Fin (n + 5))) ≃*
      alternatingGroup (Fin (n + 5)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans
    QuotientGroup.quotientBot

public instance alternatingGroup_isQuasisimple (n : Nat) :
    IsQuasisimple (alternatingGroup (Fin (n + 5))) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin (n + 5))) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact (alternatingCenterQuotientEquiv n).isSimpleGroup

@[expose]
public noncomputable def schurAlternatingCenterQuotientEquiv (n : Nat) :
    SchurAlternatingGroup n ⧸ Subgroup.center (SchurAlternatingGroup n) ≃*
      alternatingGroup (Fin (n + 5)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (schurAlternating_center_eq_ker n)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (schurAlternatingProjection n)
      (schurAlternatingProjection_surjective n))

public instance schurAlternating_isQuasisimple (n : Nat) :
    IsQuasisimple (SchurAlternatingGroup n) where
  toIsPerfect := schurAlternating_isPerfect n
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin (n + 5))) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact (schurAlternatingCenterQuotientEquiv n).isSimpleGroup

@[expose]
public def schurAlternatingCovering (n : Nat) :
    Covering (SchurAlternatingGroup n) (alternatingGroup (Fin (n + 5))) where
  toMonoidHom := schurAlternatingProjection n
  surjective := schurAlternatingProjection_surjective n

public theorem natCard_ker_schurAlternatingCovering (n : Nat) :
    Nat.card (schurAlternatingCovering n).toMonoidHom.ker = 2 := by
  simpa [schurAlternatingCovering] using
    natCard_ker_schurAlternatingProjection n

/-- Theorem 5.2.3(a), existence and kernel-order clause, with degree
parameterized as `n + 5`. -/
public theorem theorem_5_2_3_a_1 (n : Nat) :
    Nat.card (schurAlternatingCovering n).toMonoidHom.ker = 2 :=
  natCard_ker_schurAlternatingCovering n

/-- The universal-cover specialization of Theorem 5.2.3(a): two universal
coverings of the same alternating group are uniquely isomorphic over the
base.  The unrestricted Schur uniqueness statement requires the multiplier
classification input from Schur's theorem and is kept separate. -/
public theorem theorem_5_2_3_a_2_universal
    {G₁ G₂ : Type} [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (n : Nat)
    (f₁ : Covering G₁ (alternatingGroup (Fin (n + 5))))
    (f₂ : Covering G₂ (alternatingGroup (Fin (n + 5))))
    (hf₁ : Covering.IsUniversal.{0, 0, 0} f₁)
    (hf₂ : Covering.IsUniversal.{0, 0, 0} f₂) :
    ∃! e : G₁ ≃* G₂,
      f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  exact Covering.existsUnique_mulEquiv_of_isUniversal_sameBase f₁ f₂ hf₁ hf₂

set_option backward.isDefEq.respectTransparency false in
public theorem schurAdjacent_inv (n : Nat) (i : Fin (n + 4)) :
    (PresentedGroup.of (.adjacent i) : SchurPresentedGroup n)⁻¹ =
      schurCentral n * PresentedGroup.of (.adjacent i) := by
  let t : SchurPresentedGroup n := PresentedGroup.of (.adjacent i)
  let z := schurCentral n
  have ht2 : t * t = z := by
    simpa [t, z, pow_two] using schurAdjacent_sq n i
  have hzt : Commute z t := schurCentral_commutes_generator n (.adjacent i)
  apply (eq_inv_of_mul_eq_one_right (a := t) (b := z * t) ?_).symm
  calc
    t * (z * t) = (t * z) * t := by simp [mul_assoc]
    _ = (z * t) * t := by rw [hzt.eq.symm]
    _ = z * (t * t) := by simp [mul_assoc]
    _ = z * z := by rw [ht2]
    _ = 1 := by simpa [z, pow_two] using schurCentral_sq n

set_option backward.isDefEq.respectTransparency false in
public theorem schurAdjacent_far_sandwich (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (PresentedGroup.of (.adjacent i) : SchurPresentedGroup n) *
        PresentedGroup.of (.adjacent j) * PresentedGroup.of (.adjacent i) =
      PresentedGroup.of (.adjacent j) := by
  let a : SchurPresentedGroup n := PresentedGroup.of (.adjacent i)
  let b : SchurPresentedGroup n := PresentedGroup.of (.adjacent j)
  let z := schurCentral n
  have hab2 : (a * b) ^ 2 = z := schurAdjacent_far_mul_sq n hfar
  have hb2 : b * b = z := by
    simpa [b, z, pow_two] using schurAdjacent_sq n j
  apply mul_right_cancel (b := b)
  calc
    (a * b * a) * b = (a * b) ^ 2 := by simp [pow_two, mul_assoc]
    _ = z := hab2
    _ = b * b := hb2.symm

set_option backward.isDefEq.respectTransparency false in
public theorem schurAdjacent_braid (n : Nat) (i : Fin (n + 3)) :
    (PresentedGroup.of (.adjacent i.castSucc) : SchurPresentedGroup n) *
        PresentedGroup.of (.adjacent i.succ) *
          PresentedGroup.of (.adjacent i.castSucc) =
      PresentedGroup.of (.adjacent i.succ) *
        PresentedGroup.of (.adjacent i.castSucc) *
          PresentedGroup.of (.adjacent i.succ) := by
  let a : SchurPresentedGroup n := PresentedGroup.of (.adjacent i.castSucc)
  let b : SchurPresentedGroup n := PresentedGroup.of (.adjacent i.succ)
  let z := schurCentral n
  have hab3 : (a * b) ^ 3 = z := schurAdjacent_mul_pow_three n i
  have ha2 : a * a = z := by
    simpa [a, z, pow_two] using schurAdjacent_sq n i.castSucc
  have hb2 : b * b = z := by
    simpa [b, z, pow_two] using schurAdjacent_sq n i.succ
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  have hza : Commute z a := schurCentral_commutes_generator n (.adjacent i.castSucc)
  have hzb : Commute z b := schurCentral_commutes_generator n (.adjacent i.succ)
  have hzba : Commute z (b * a) := hzb.mul_right hza
  have hab_inv : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, schurAdjacent_inv, schurAdjacent_inv]
    calc
      (z * b) * (z * a) = z * (b * z) * a := by simp [mul_assoc]
      _ = z * (z * b) * a := by rw [hzb.eq.symm]
      _ = (z * z) * (b * a) := by simp [mul_assoc]
      _ = b * a := by rw [hz2]; simp
  have hab2 : (a * b) ^ 2 = z * (b * a) := by
    apply mul_right_cancel (b := a * b)
    calc
      (a * b) ^ 2 * (a * b) = (a * b) ^ 3 := by
        simp [pow_succ, mul_assoc]
      _ = z := hab3
      _ = (z * (a * b)⁻¹) * (a * b) := by simp [mul_assoc]
      _ = (z * (b * a)) * (a * b) := by rw [hab_inv]
  apply mul_right_cancel (b := b)
  calc
    (a * b * a) * b = (a * b) ^ 2 := by simp [pow_two, mul_assoc]
    _ = z * (b * a) := hab2
    _ = (b * a) * z := hzba.eq
    _ = b * a * (b * b) := by rw [hb2]
    _ = (b * a * b) * b := by simp [mul_assoc]

@[expose]
public def schurSuzukiGenerator (n : Nat) (i : Fin (n + 3)) :
    SchurAlternatingGroup n :=
  ⟨PresentedGroup.of (.adjacent (0 : Fin (n + 4))) *
      PresentedGroup.of (.adjacent i.succ), by
    have hi : i.castSucc ≠ i.succ := by
      exact ne_of_lt Fin.castSucc_lt_succ
    change schurSymmetricProjection n
        (PresentedGroup.of (.adjacent (0 : Fin (n + 4))) *
          PresentedGroup.of (.adjacent i.succ)) ∈
      alternatingGroup (Fin (n + 5))
    rw [map_mul, schurSymmetricProjection_adjacent,
      schurSymmetricProjection_adjacent, Equiv.Perm.mem_alternatingGroup,
      map_mul]
    simp [adjacentSwap, Equiv.Perm.sign_swap', hi]⟩

public theorem schurSuzukiGenerator_zero (n : Nat) :
    schurSuzukiGenerator n (0 : Fin (n + 3)) =
      schurAlternatingThreeCycle n (0 : Fin (n + 3)) := by
  apply Subtype.ext
  rfl

public theorem schurSuzukiGenerator_zero_pow_three (n : Nat) :
    schurSuzukiGenerator n (0 : Fin (n + 3)) ^ 3 = schurAlternatingCentral n := by
  rw [schurSuzukiGenerator_zero]
  exact schurAlternatingThreeCycle_pow_three n 0

public theorem schurSuzukiGenerator_tail_sq (n : Nat) (i : Fin (n + 3))
    (hi : i ≠ 0) :
    schurSuzukiGenerator n i ^ 2 = schurAlternatingCentral n := by
  apply Subtype.ext
  change ((PresentedGroup.of (.adjacent (0 : Fin (n + 4))) *
      PresentedGroup.of (.adjacent i.succ) : SchurPresentedGroup n) ^ 2 =
    schurCentral n)
  have hi' : 0 < i.val := by
    have hne : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext h
    omega
  have hfar : (0 : Fin (n + 4)).val + 1 < i.succ.val := by
    change 1 < i.val + 1
    omega
  exact schurAdjacent_far_mul_sq n (i := 0) (j := i.succ)
    (Or.inl hfar)

public theorem schurSuzukiGenerator_zero_succ_mul_pow_three (n : Nat) :
    (schurSuzukiGenerator n (0 : Fin (n + 3)) *
      schurSuzukiGenerator n ((0 : Fin (n + 2)).succ)) ^ 3 =
      schurAlternatingCentral n := by
  apply Subtype.ext
  let a : SchurPresentedGroup n := PresentedGroup.of (.adjacent (0 : Fin (n + 4)))
  let b : SchurPresentedGroup n := PresentedGroup.of (.adjacent (1 : Fin (n + 4)))
  let j : Fin (n + 4) := ⟨2, by omega⟩
  let c : SchurPresentedGroup n := PresentedGroup.of (.adjacent j)
  let z := schurCentral n
  change ((a * b) * (a * c)) ^ 3 = z
  have hac : a * c * a = c := by
    simpa [a, c, j] using schurAdjacent_far_sandwich n
      (i := (0 : Fin (n + 4))) (j := j)
      (Or.inl (by change 1 < 2; omega))
  have hza : Commute z a := schurCentral_commutes_generator n (.adjacent 0)
  have hp : (a * b) * (a * c) = a * (b * c) * a⁻¹ := by
    apply mul_right_cancel (b := a)
    calc
      ((a * b) * (a * c)) * a = a * b * (a * c * a) := by simp [mul_assoc]
      _ = (a * (b * c) * a⁻¹) * a := by rw [hac]; simp [mul_assoc]
  rw [hp]
  calc
    (a * (b * c) * a⁻¹) ^ 3 = a * (b * c) ^ 3 * a⁻¹ := by
      simp [pow_succ, mul_assoc]
    _ = a * z * a⁻¹ := by
      rw [show (b * c) ^ 3 = z by
        simpa [b, c, j, show j = (2 : Fin (n + 4)) by ext; rfl]
          using schurAdjacent_mul_pow_three n 1]
    _ = z := by
      rw [← hza.eq]
      simp

public theorem schurSuzukiGenerator_tail_mul_pow_three (n : Nat)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (schurSuzukiGenerator n i.castSucc * schurSuzukiGenerator n i.succ) ^ 3 =
      schurAlternatingCentral n := by
  apply Subtype.ext
  let a : SchurPresentedGroup n := PresentedGroup.of (.adjacent (0 : Fin (n + 4)))
  let b : SchurPresentedGroup n := PresentedGroup.of (.adjacent i.succ.castSucc)
  let c : SchurPresentedGroup n := PresentedGroup.of (.adjacent i.succ.succ)
  let z := schurCentral n
  change ((a * b) * (a * c)) ^ 3 = z
  have hi' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
  have hab : a * b * a = b := by
    simpa [a, b] using schurAdjacent_far_sandwich n
      (i := (0 : Fin (n + 4))) (j := i.succ.castSucc)
      (Or.inl (by change 1 < i.val + 1; omega))
  calc
    ((a * b) * (a * c)) ^ 3 = (b * c) ^ 3 := by rw [show (a * b) * (a * c) = b * c by
      calc
        (a * b) * (a * c) = (a * b * a) * c := by simp [mul_assoc]
        _ = b * c := by rw [hab]]
    _ = z := by
      simpa [b, c, z] using schurAdjacent_mul_pow_three n i.succ

public theorem schurSuzukiGenerator_tail_far_mul_sq (n : Nat)
    {i j : Fin (n + 3)} (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (schurSuzukiGenerator n i * schurSuzukiGenerator n j) ^ 2 =
      schurAlternatingCentral n := by
  apply Subtype.ext
  let a : SchurPresentedGroup n := PresentedGroup.of (.adjacent (0 : Fin (n + 4)))
  let b : SchurPresentedGroup n := PresentedGroup.of (.adjacent i.succ)
  let c : SchurPresentedGroup n := PresentedGroup.of (.adjacent j.succ)
  let z := schurCentral n
  change ((a * b) * (a * c)) ^ 2 = z
  have hib : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
  have hjb : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
  have hab : a * b * a = b := by
    simpa [a, b] using schurAdjacent_far_sandwich n
      (i := (0 : Fin (n + 4))) (j := i.succ)
      (Or.inl (by change 1 < i.val + 1; omega))
  have hbc : (b * c) ^ 2 = z := by
    simpa [b, c, z] using schurAdjacent_far_mul_sq n (i := i.succ) (j := j.succ)
      (by
        rcases hfar with h | h
        · left
          change i.val + 2 < j.val + 1
          omega
        · right
          change j.val + 2 < i.val + 1
          omega)
  calc
    ((a * b) * (a * c)) ^ 2 = (b * c) ^ 2 := by rw [show (a * b) * (a * c) = b * c by
      calc
        (a * b) * (a * c) = (a * b * a) * c := by simp [mul_assoc]
        _ = b * c := by rw [hab]]
    _ = z := hbc

@[expose]
public def alternatingSuzukiGenerator (n : Nat) (i : Fin (n + 3)) :
    alternatingGroup (Fin (n + 5)) :=
  schurAlternatingProjection n (schurSuzukiGenerator n i)

public theorem alternatingSuzukiGenerator_val (n : Nat) (i : Fin (n + 3)) :
    (alternatingSuzukiGenerator n i : Equiv.Perm (Fin (n + 5))) =
      adjacentSwap n 0 * adjacentSwap n i.succ := by
  change schurSymmetricProjection n
      (PresentedGroup.of (.adjacent (0 : Fin (n + 4))) *
        PresentedGroup.of (.adjacent i.succ)) = _
  rw [map_mul, schurSymmetricProjection_adjacent,
    schurSymmetricProjection_adjacent]

private theorem __ch5_SchurPresentation_suzukiTailPoints_nodup (n : Nat) (i : Fin (n + 3))
    (hi : i ≠ 0) :
    List.Nodup [(0 : Fin (n + 4)).castSucc, (0 : Fin (n + 4)).succ,
      i.succ.castSucc, i.succ.succ] := by
  have hi' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
  have hne {x y : Fin (n + 5)} (hxy : x.val ≠ y.val) : x ≠ y := by
    intro h
    exact hxy (congrArg Fin.val h)
  have h01 : (0 : Fin (n + 4)).castSucc ≠ (0 : Fin (n + 4)).succ :=
    ne_of_lt Fin.castSucc_lt_succ
  have h0c : (0 : Fin (n + 4)).castSucc ≠ i.succ.castSucc := by
    apply hne
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
    omega
  have h0d : (0 : Fin (n + 4)).castSucc ≠ i.succ.succ := by
    apply hne
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
    omega
  have h1c : (0 : Fin (n + 4)).succ ≠ i.succ.castSucc := by
    apply hne
    simp only [Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
    omega
  have h1d : (0 : Fin (n + 4)).succ ≠ i.succ.succ := by
    apply hne
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hcd : i.succ.castSucc ≠ i.succ.succ := ne_of_lt Fin.castSucc_lt_succ
  simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
    or_false, h01, h0c, h0d, h1c, h1d, hcd, not_false_eq_true, true_and]

public theorem alternatingSuzukiGenerator_tail_isConj (n : Nat) (hn : 1 ≤ n)
    {i j : Fin (n + 3)} (hi : i ≠ 0) (hj : j ≠ 0) :
    IsConj (alternatingSuzukiGenerator n i) (alternatingSuzukiGenerator n j) := by
  have hcti : ((alternatingSuzukiGenerator n i :
      Equiv.Perm (Fin (n + 5))).cycleType) = {2, 2} := by
    rw [alternatingSuzukiGenerator_val, adjacentSwap, adjacentSwap]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (__ch5_SchurPresentation_suzukiTailPoints_nodup n i hi)
  have hctj : ((alternatingSuzukiGenerator n j :
      Equiv.Perm (Fin (n + 5))).cycleType) = {2, 2} := by
    rw [alternatingSuzukiGenerator_val, adjacentSwap, adjacentSwap]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup
      (__ch5_SchurPresentation_suzukiTailPoints_nodup n j hj)
  apply alternatingGroup.isConj_of
  · exact Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcti.trans hctj.symm)
  · rw [← Equiv.Perm.sum_cycleType, hcti]
    simp
    omega

public theorem alternatingSuzukiGenerator_zero_pow_three (n : Nat) :
    alternatingSuzukiGenerator n (0 : Fin (n + 3)) ^ 3 = 1 := by
  rw [alternatingSuzukiGenerator, ← map_pow,
    schurSuzukiGenerator_zero_pow_three,
    schurAlternatingProjection_central]

public theorem alternatingSuzukiGenerator_tail_sq (n : Nat)
    (i : Fin (n + 3)) (hi : i ≠ 0) :
    alternatingSuzukiGenerator n i ^ 2 = 1 := by
  rw [alternatingSuzukiGenerator, ← map_pow,
    schurSuzukiGenerator_tail_sq n i hi,
    schurAlternatingProjection_central]

public theorem alternatingSuzukiGenerator_zero_succ_mul_pow_three (n : Nat) :
    (alternatingSuzukiGenerator n (0 : Fin (n + 3)) *
      alternatingSuzukiGenerator n ((0 : Fin (n + 2)).succ)) ^ 3 = 1 := by
  rw [alternatingSuzukiGenerator, alternatingSuzukiGenerator, ← map_mul, ← map_pow,
    schurSuzukiGenerator_zero_succ_mul_pow_three,
    schurAlternatingProjection_central]

public theorem alternatingSuzukiGenerator_tail_mul_pow_three (n : Nat)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (alternatingSuzukiGenerator n i.castSucc *
      alternatingSuzukiGenerator n i.succ) ^ 3 = 1 := by
  rw [alternatingSuzukiGenerator, alternatingSuzukiGenerator, ← map_mul, ← map_pow,
    schurSuzukiGenerator_tail_mul_pow_three n i hi,
    schurAlternatingProjection_central]

public theorem alternatingSuzukiGenerator_tail_far_mul_sq (n : Nat)
    {i j : Fin (n + 3)} (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j) ^ 2 = 1 := by
  rw [alternatingSuzukiGenerator, alternatingSuzukiGenerator, ← map_mul, ← map_pow,
    schurSuzukiGenerator_tail_far_mul_sq n hi hj hfar,
    schurAlternatingProjection_central]

public theorem alternatingSuzukiGenerator_tail_pair_val (n : Nat)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    ((alternatingSuzukiGenerator n i.castSucc *
      alternatingSuzukiGenerator n i.succ :
      alternatingGroup (Fin (n + 5))) : Equiv.Perm (Fin (n + 5))) =
      adjacentSwap n i.succ.castSucc * adjacentSwap n i.succ.succ := by
  change (alternatingSuzukiGenerator n i.castSucc : Equiv.Perm (Fin (n + 5))) *
      (alternatingSuzukiGenerator n i.succ : Equiv.Perm (Fin (n + 5))) = _
  rw [alternatingSuzukiGenerator_val, alternatingSuzukiGenerator_val]
  let a : Equiv.Perm (Fin (n + 5)) := adjacentSwap n 0
  let b : Equiv.Perm (Fin (n + 5)) := adjacentSwap n i.succ.castSucc
  let c : Equiv.Perm (Fin (n + 5)) := adjacentSwap n i.succ.succ
  have hi' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
  have hb : Commute a b := by
    apply __ch5_SchurPresentation_adjacentSwap_far_commute n
    left
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
    omega
  have hc : Commute a c := by
    apply __ch5_SchurPresentation_adjacentSwap_far_commute n
    left
    simp only [Fin.val_zero, Fin.val_succ]
    omega
  change (a * b) * (a * c) = b * c
  calc
    (a * b) * (a * c) = a * (b * a) * c := by simp [mul_assoc]
    _ = a * (a * b) * c := by rw [← hb.eq]
    _ = (a * a) * (b * c) := by simp [mul_assoc]
    _ = b * c := by
      rw [show a * a = 1 by
        simpa [a, pow_two] using adjacentSwap_sq n 0]
      simp

public theorem alternatingSuzukiGenerator_tail_pair_mem_closure (n : Nat)
    (i : Fin (n + 2)) (_hi : i ≠ 0) :
    alternatingSuzukiGenerator n i.castSucc *
      alternatingSuzukiGenerator n i.succ ∈
      Subgroup.closure (Set.range (alternatingSuzukiGenerator n)) := by
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
  · exact Subgroup.subset_closure ⟨i.succ, rfl⟩

public theorem alternatingSuzukiGenerator_tail_pair_isThreeCycle (n : Nat)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    Equiv.Perm.IsThreeCycle
      ((alternatingSuzukiGenerator n i.castSucc *
        alternatingSuzukiGenerator n i.succ :
        alternatingGroup (Fin (n + 5))) : Equiv.Perm (Fin (n + 5))) := by
  rw [alternatingSuzukiGenerator_tail_pair_val n i hi]
  let a : Fin (n + 5) := i.succ.castSucc.castSucc
  let b : Fin (n + 5) := i.succ.castSucc.succ
  let c : Fin (n + 5) := i.succ.succ.succ
  change Equiv.Perm.IsThreeCycle
    (Equiv.swap a b * Equiv.swap b c)
  have hab : a ≠ b := ne_of_lt Fin.castSucc_lt_succ
  have hac : a ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    simp only [a, c, Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hbc : b ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    simp only [b, c, Fin.val_castSucc, Fin.val_succ] at hv
    omega
  rw [adjacentThreeCycle_eq_common hab hac hbc]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab hbc.symm

public theorem adjacentSwap_mul_adjacentSwap_isThreeCycle (n : Nat)
    (k : Fin (n + 3)) :
    Equiv.Perm.IsThreeCycle
      (adjacentSwap n k.castSucc * adjacentSwap n k.succ) := by
  change Equiv.Perm.IsThreeCycle
    (Equiv.swap k.castSucc.castSucc k.castSucc.succ *
      Equiv.swap k.succ.castSucc k.succ.succ)
  rw [show k.castSucc.succ = k.succ.castSucc by rfl]
  have h1 : k.castSucc.castSucc ≠ k.succ.castSucc :=
    ne_of_lt k.castSucc.castSucc_lt_succ
  have h2 : k.castSucc.castSucc ≠ k.succ.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have h3 : k.succ.castSucc ≠ k.succ.succ :=
    ne_of_lt k.succ.castSucc_lt_succ
  rw [adjacentThreeCycle_eq_common h1 h2 h3]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same h2 h1 h3.symm

private theorem __ch5_SchurPresentation_suzukiStar_conjugate_step
    {Ω : Type*} [DecidableEq Ω] {a b c d : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (_hcd : c ≠ d) :
    (((Equiv.swap a b * Equiv.swap c d) *
        (Equiv.swap a b * Equiv.swap a c) *
        (Equiv.swap a b * Equiv.swap c d)⁻¹)⁻¹) =
      Equiv.swap a b * Equiv.swap a d := by
  let s : Equiv.Perm Ω := Equiv.swap a b * Equiv.swap c d
  have hconj (x y : Ω) :
      s * Equiv.swap x y * s⁻¹ = Equiv.swap (s x) (s y) := by
    rw [Equiv.mul_swap_eq_swap_mul]
    simp [mul_assoc]
  have hsa : s a = b := by
    simp [s, Equiv.swap_apply_of_ne_of_ne hac had]
  have hsb : s b = a := by
    simp [s, Equiv.swap_apply_of_ne_of_ne hbc hbd]
  have hsc : s c = d := by
    simp [s, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hprod :
      s * (Equiv.swap a b * Equiv.swap a c) * s⁻¹ =
        Equiv.swap b a * Equiv.swap b d := by
    calc
      s * (Equiv.swap a b * Equiv.swap a c) * s⁻¹ =
          (s * Equiv.swap a b * s⁻¹) *
            (s * Equiv.swap a c * s⁻¹) := by simp [mul_assoc]
      _ = Equiv.swap (s a) (s b) * Equiv.swap (s a) (s c) := by
        rw [hconj, hconj]
      _ = Equiv.swap b a * Equiv.swap b d := by rw [hsa, hsb, hsc]
  change (s * (Equiv.swap a b * Equiv.swap a c) * s⁻¹)⁻¹ = _
  rw [hprod, mul_inv_rev]
  simp only [Equiv.swap_inv]
  exact (commonThreeCycle_rotate hab had hbd).symm

/-- Suzuki's generators from presentation (2.15) generate the full alternating
group.  The proof obtains all star three-cycles based at `0,1`: the first one
is the inverse of generator zero, and each later one is an inverse conjugate
of its predecessor by a tail generator. -/
public theorem alternatingSuzukiGenerator_closure_eq_top (n : Nat) :
    Subgroup.closure (Set.range (alternatingSuzukiGenerator n)) = ⊤ := by
  let H := Subgroup.closure (Set.range (alternatingSuzukiGenerator n))
  have hgen (i : Fin (n + 3)) : alternatingSuzukiGenerator n i ∈ H :=
    Subgroup.subset_closure ⟨i, rfl⟩
  have hstar (c : Fin (n + 5)) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
      (⟨Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 c,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          (by simp) hc0.symm hc1.symm).mem_alternatingGroup⟩ :
        alternatingGroup (Fin (n + 5))) ∈ H := by
    induction c using Fin.induction with
    | zero => exact (hc0 rfl).elim
    | succ c ih =>
        by_cases hc_zero : c = 0
        · subst c
          exact (hc1 rfl).elim
        by_cases hc_one : c = 1
        · subst c
          have hinv := H.inv_mem (hgen (0 : Fin (n + 3)))
          convert hinv using 1
          apply Subtype.ext
          let z : Fin (n + 5) := (1 : Fin (n + 4)).succ
          change Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 z =
            ((alternatingSuzukiGenerator n (0 : Fin (n + 3)) :
              alternatingGroup (Fin (n + 5))) : Equiv.Perm (Fin (n + 5)))⁻¹
          rw [alternatingSuzukiGenerator_val]
          change Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 z =
            (Equiv.swap 0 1 * Equiv.swap 1 z)⁻¹
          rw [mul_inv_rev]
          simp only [Equiv.swap_inv]
          have hz0 : (0 : Fin (n + 5)) ≠ z := by
            intro h
            have hv := congrArg Fin.val h
            have hlt : 2 < n + 5 := by omega
            norm_num [z, Nat.mod_eq_of_lt hlt] at hv
          have hz1 : (1 : Fin (n + 5)) ≠ z := by
            intro h
            have hv := congrArg Fin.val h
            have hlt : 2 < n + 5 := by omega
            norm_num [z, Nat.mod_eq_of_lt hlt] at hv
          calc
            Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 z =
                Equiv.swap 1 z * Equiv.swap 1 0 :=
              commonThreeCycle_rotate (by simp) hz0 hz1
            _ = Equiv.swap 1 z * Equiv.swap 0 1 := by
              rw [Equiv.swap_comm 1 0]
        · have hc_cast_zero : c.castSucc ≠ (0 : Fin (n + 5)) := by
            intro h
            apply hc_zero
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa using hv
          have hc_cast_one : c.castSucc ≠ (1 : Fin (n + 5)) := by
            intro h
            apply hc_one
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa using hv
          have hp := ih hc_cast_zero hc_cast_one
          let i : Fin (n + 3) := Fin.pred c hc_zero
          let s := alternatingSuzukiGenerator n i
          let p : alternatingGroup (Fin (n + 5)) :=
            ⟨Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 c.castSucc,
              (Equiv.Perm.isThreeCycle_swap_mul_swap_same
                (by simp) hc_cast_zero.symm hc_cast_one.symm).mem_alternatingGroup⟩
          have hs : s ∈ H := hgen i
          have hp' : p ∈ H := by simpa [p] using hp
          have hmem : (s * p * s⁻¹)⁻¹ ∈ H :=
            H.inv_mem (H.mul_mem (H.mul_mem hs hp') (H.inv_mem hs))
          convert hmem using 1
          apply Subtype.ext
          have hi : i.succ = c := Fin.succ_pred c hc_zero
          change Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 c.succ =
            (((s : Equiv.Perm (Fin (n + 5))) *
              (p : Equiv.Perm (Fin (n + 5))) *
              (s : Equiv.Perm (Fin (n + 5)))⁻¹)⁻¹)
          rw [show (s : Equiv.Perm (Fin (n + 5))) =
              Equiv.swap 0 1 * Equiv.swap c.castSucc c.succ by
            dsimp [s]
            rw [alternatingSuzukiGenerator_val, adjacentSwap, adjacentSwap, hi]
            congr 1]
          change Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 c.succ =
            (((Equiv.swap 0 1 * Equiv.swap c.castSucc c.succ) *
              (Equiv.swap 0 1 * Equiv.swap 0 c.castSucc) *
              (Equiv.swap 0 1 * Equiv.swap c.castSucc c.succ)⁻¹)⁻¹)
          symm
          apply __ch5_SchurPresentation_suzukiStar_conjugate_step
          all_goals
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_zero, Fin.val_one, Fin.val_castSucc, Fin.val_succ] at hv
            omega
  apply top_unique
  rw [← starThreeCycles_closure_eq_top
    (a := (0 : Fin (n + 5))) (b := (1 : Fin (n + 5))) (by simp)]
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨c, hc0, hc1, hgval⟩ := hg
  have heq : g =
      (⟨Equiv.swap (0 : Fin (n + 5)) 1 * Equiv.swap 0 c,
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same
          (by simp) hc0.symm hc1.symm).mem_alternatingGroup⟩ :
        alternatingGroup (Fin (n + 5))) := by
    apply Subtype.ext
    simpa using hgval
  rw [heq]
  exact hstar c hc0 hc1

/-- The free-group map induced by Suzuki's generators is onto the alternating
group. -/
public theorem alternatingSuzukiGenerator_lift_surjective (n : Nat) :
    Function.Surjective (FreeGroup.lift (alternatingSuzukiGenerator n)) := by
  rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure,
    alternatingSuzukiGenerator_closure_eq_top]

end SchurPresentation

end GLS3.Chapter5
/- END Theory.SchurPresentation -/

/- BEGIN Theory.QuasisimpleSubgroupOf -/
namespace GLS3.Chapter5

/-- Viewing a quasisimple subgroup inside a larger subgroup preserves its
group structure and quasisimplicity. -/
public theorem isQuasisimple_subgroupOf
    {G : Type*} [Group G] (I C : Subgroup G)
    [IsQuasisimple I] (hI : I ≤ C) :
    IsQuasisimple (I.subgroupOf C) := by
  let e : I ≃* I.subgroupOf C :=
    { toFun := fun i => ⟨⟨i.1, hI i.2⟩, i.2⟩
      invFun := fun i => ⟨i.1.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let : Nontrivial (I ⧸ Subgroup.center I) :=
    (inferInstance : IsQuasisimple I).simple.toNontrivial
  let : Nontrivial I :=
    (QuotientGroup.mk'_surjective (Subgroup.center I)).nontrivial
  let : Nontrivial (I.subgroupOf C) := e.injective.nontrivial
  have hker : e.toMonoidHom.ker ≤ Subgroup.center I := by
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact bot_le
  exact isQuasisimple_of_surjective_of_ker_le_center
    e.toMonoidHom e.surjective hker

end GLS3.Chapter5
/- END Theory.QuasisimpleSubgroupOf -/

/- BEGIN Theory.QuasisimpleSubnormalAlternatingEqualsTop -/
namespace GLS3.Chapter5

/-- A quasisimple subnormal subgroup of an alternating group is the whole
alternating group; in particular the degree is at least five. -/
public theorem quasisimple_subnormal_alternating_eq_top
    (n : Nat) (J : Subgroup (alternatingGroup (Fin n)))
    [IsQuasisimple J] (hJ : J.IsSubnormal) :
    J = ⊤ ∧ 5 ≤ n := by
  let : Nontrivial (J ⧸ Subgroup.center J) :=
    (inferInstance : IsQuasisimple J).simple.toNontrivial
  let : Nontrivial J :=
    (QuotientGroup.mk'_surjective (Subgroup.center J)).nontrivial
  have hJne : J ≠ ⊥ := J.nontrivial_iff_ne_bot.mp inferInstance
  by_cases hn : 5 ≤ n
  · let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup (alternatingGroup (Fin n))) hJ with
      hbot | htop
    · exact False.elim (hJne hbot)
    · exact ⟨htop, hn⟩
  · have hn4 : n ≤ 4 := by omega
    by_cases hn3 : n ≤ 3
    · let : IsMulCommutative (alternatingGroup (Fin n)) :=
        alternatingGroup.isMulCommutative_of_card_le_three (by simpa using hn3)
      let : IsMulCommutative J := IsMulCommutative.of_comm fun a b => by
        apply Subtype.ext
        exact isMulCommutative_iff.mp
          (inferInstance : IsMulCommutative (alternatingGroup (Fin n))) a.1 b.1
      exact False.elim
        (Group.IsPerfect.not_isMulCommutative J inferInstance)
    · have hn4eq : n = 4 := by omega
      have hJle : J ≤ _root_.commutator (alternatingGroup (Fin n)) :=
        perfect_subgroup_le_ambient_commutator J
      have hcommEq : _root_.commutator (alternatingGroup (Fin n)) =
          alternatingGroup.kleinFour (Fin n) := by
        exact (alternatingGroup.kleinFour_eq_commutator
          (by simpa using hn4eq)).symm
      let : IsKleinFour (alternatingGroup.kleinFour (Fin n)) :=
        alternatingGroup.kleinFour_isKleinFour (by simpa using hn4eq)
      let : IsMulCommutative J := IsMulCommutative.of_comm fun a b => by
        let aK : alternatingGroup.kleinFour (Fin n) :=
          ⟨a.1, by rw [← hcommEq]; exact hJle a.2⟩
        let bK : alternatingGroup.kleinFour (Fin n) :=
          ⟨b.1, by rw [← hcommEq]; exact hJle b.2⟩
        apply Subtype.ext
        have hab := congrArg Subtype.val
          (isMulCommutative_iff.mp
            (IsKleinFour.isMulCommutative : IsMulCommutative
              (alternatingGroup.kleinFour (Fin n))) aK bK)
        simpa [aK, bK] using hab
      exact False.elim
        (Group.IsPerfect.not_isMulCommutative J inferInstance)

end GLS3.Chapter5
/- END Theory.QuasisimpleSubnormalAlternatingEqualsTop -/

/- BEGIN Theory.QuasisimpleSubnormalStableAbelianExclusion -/
namespace GLS3.Chapter5

/-- A quasisimple subnormal subgroup cannot act stably and nontrivially on a
nontrivial normal abelian subgroup. -/
public theorem not_isSubnormal_of_nontrivial_normal_abelian_le_commutator
    {G : Type*} [Group G] (M I : Subgroup G)
    [IsMulCommutative M] [IsQuasisimple I]
    (hMnormal : I ≤ Subgroup.normalizer M)
    (hMne : M ≠ ⊥) (hstable : M ≤ ⁅M, I⁆) :
    ¬ I.IsSubnormal := by
  intro hI
  have hMI : M ≤ I :=
    le_of_isSubnormal_of_le_commutator M I hI hstable
  let J : Subgroup I := M.subgroupOf I
  have : J.Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer hMI |>.mpr hMnormal
  rcases normal_eq_top_or_le_center_of_isQuasisimple J with htop | hcenter
  · have hIM : I ≤ M := Subgroup.subgroupOf_eq_top.mp htop
    let : Nontrivial (I ⧸ Subgroup.center I) :=
      (inferInstance : IsQuasisimple I).simple.toNontrivial
    let : Nontrivial I :=
      (QuotientGroup.mk'_surjective (Subgroup.center I)).nontrivial
    let : IsMulCommutative I := IsMulCommutative.of_comm fun a b => by
      let aM : M := ⟨a.1, hIM a.2⟩
      let bM : M := ⟨b.1, hIM b.2⟩
      apply Subtype.ext
      have hab := congrArg (fun z : M => z.1)
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative M) aM bM)
      simpa [aM, bM] using hab
    exact Group.IsPerfect.not_isMulCommutative I inferInstance
  · have hcomm : ⁅M, I⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      let mI : I := ⟨m, hMI hm⟩
      have hmJ : mI ∈ J := hm
      have hmcenter := Subgroup.mem_center_iff.mp (hcenter hmJ)
      exact congrArg Subtype.val (hmcenter ⟨i, hi⟩)
    apply hMne
    apply le_antisymm
    · simpa [hcomm] using hstable
    · exact bot_le

end GLS3.Chapter5
/- END Theory.QuasisimpleSubnormalStableAbelianExclusion -/

/- BEGIN Theory.CentralizerRotationInDirectFactor -/
namespace GLS3.Chapter5

/-- In a direct product of a faithful semidirect factor with a commuting
factor, the centralizer of the abelian normal subgroup is exactly the product
of that subgroup with the commuting factor. -/
public theorem centralizer_inf_semidirect_sup_factor_eq
    {G : Type*} [Group G] (R L H : Subgroup G)
    [IsMulCommutative R]
    (hLnormalizes : L ≤ Subgroup.normalizer R)
    (hfaithful : Disjoint L (Subgroup.centralizer (R : Set G)))
    (hdisjoint : Disjoint (R ⊔ L) H)
    (hcommute : ∀ a : ↥(R ⊔ L), ∀ b : H, Commute a.1 b.1) :
    Subgroup.centralizer (R : Set G) ⊓ ((R ⊔ L) ⊔ H) = R ⊔ H := by
  have hcentralH1 :
      Subgroup.centralizer (R : Set G) ⊓ (R ⊔ L) = R :=
    centralizer_inf_sup_eq_left_of_disjoint_complement
      R L hLnormalizes hfaithful
  apply le_antisymm
  · intro g hg
    obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute_apply
      (R ⊔ L) H hdisjoint hcommute
    let q : ↥(R ⊔ L) × H := e.symm ⟨g, hg.2⟩
    have hqeq : q.1.1 * q.2.1 = g := by
      have hback := e.apply_symm_apply ⟨g, hg.2⟩
      rw [he q] at hback
      exact congrArg Subtype.val hback
    have hq2central : q.2.1 ∈
        Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hcommute
        ⟨r, (show R ≤ R ⊔ L from le_sup_left) hr⟩ q.2).eq
    have hq1central : q.1.1 ∈
        Subgroup.centralizer (R : Set G) := by
      have hgcentral := hg.1
      have hrewrite : q.1.1 = g * q.2.1⁻¹ := by
        rw [← hqeq]
        simp
      rw [hrewrite]
      exact (Subgroup.centralizer (R : Set G)).mul_mem hgcentral
        ((Subgroup.centralizer (R : Set G)).inv_mem hq2central)
    have hq1R : q.1.1 ∈ R := by
      exact (show Subgroup.centralizer (R : Set G) ⊓ (R ⊔ L) ≤ R
        from hcentralH1.le) ⟨hq1central, q.1.2⟩
    rw [← hqeq]
    exact Subgroup.mul_mem_sup hq1R q.2.2
  · apply sup_le
    · intro r hr
      have hrcentral : r ∈
          Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact congrArg Subtype.val
          (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R)
            ⟨s, hs⟩ ⟨r, hr⟩)
      exact ⟨hrcentral,
        (show R ≤ (R ⊔ L) ⊔ H from le_sup_left.trans le_sup_left) hr⟩
    · intro h hh
      have hhcentral : h ∈
          Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact (hcommute
          ⟨r, (show R ≤ R ⊔ L from le_sup_left) hr⟩ ⟨h, hh⟩).eq
      exact ⟨hhcentral,
        (show H ≤ (R ⊔ L) ⊔ H from le_sup_right) hh⟩

end GLS3.Chapter5
/- END Theory.CentralizerRotationInDirectFactor -/

/- BEGIN Theory.FixedSubgroupImageIndexTwo -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

/-- If a surjection has central kernel of order two, then failure of fixed-point
surjectivity for conjugation by an involution has index exactly two. -/
public theorem fixedSubgroup_image_index_eq_two_of_failure
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (hkerCard : Nat.card f.ker = 2)
    (y : G)
    (hneq :
      (automorphismFixedSubgroup (MulAut.conj y)).map f ≠
        automorphismFixedSubgroup (MulAut.conj (f y))) :
    ∃ _ :
        (automorphismFixedSubgroup (MulAut.conj y)).map f ≤
          automorphismFixedSubgroup (MulAut.conj (f y)),
      (((automorphismFixedSubgroup (MulAut.conj y)).map f).subgroupOf
          (automorphismFixedSubgroup (MulAut.conj (f y)))).index = 2 := by
  let C := automorphismFixedSubgroup (MulAut.conj y)
  let Cbar := automorphismFixedSubgroup (MulAut.conj (f y))
  have hle : C.map f ≤ Cbar := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' := ha
    change y * a * y⁻¹ = a at ha'
    change f y * f a * (f y)⁻¹ = f a
    simpa using congrArg f ha'
  let E := Cbar.comap f
  have hCE : C ≤ E := by
    intro a ha
    exact hle ⟨a, ha, rfl⟩
  let q : E →* Cbar :=
    (f.comp E.subtype).codRestrict Cbar (fun a => a.2)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := hf b.1
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact b.2
    refine ⟨⟨a, haE⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hcKer : ∀ a : E, ⁅a.1, y⁆ ∈ f.ker := by
    intro a
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    have ha := a.2
    change f y * f a.1 * (f y)⁻¹ = f a.1 at ha
    have hcomm : Commute (f y) (f a.1) := by
      rw [commute_iff_eq]
      have h := congrArg (fun z : H => z * f y) ha
      simpa [mul_assoc] using h
    exact hcomm.symm
  have hcCenter : ∀ a : E, ⁅a.1, y⁆ ∈ Subgroup.center G :=
    fun a => hker (hcKer a)
  let deltaCenter : E →* Subgroup.center G :=
    centralCommutatorHom E.subtype y hcCenter
  let delta : E →* f.ker := {
    toFun := fun a => ⟨(deltaCenter a).1, hcKer a⟩
    map_one' := by
      apply Subtype.ext
      change (deltaCenter 1).1 = 1
      exact congrArg Subtype.val (map_one deltaCenter)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change (deltaCenter (a * b)).1 =
        (deltaCenter a).1 * (deltaCenter b).1
      exact congrArg Subtype.val (map_mul deltaCenter a b) }
  have hdeltaKer : delta.ker = C.subgroupOf E := by
    ext a
    constructor
    · intro ha
      have haOne : ⁅a.1, y⁆ = 1 := by
        have h := MonoidHom.mem_ker.mp ha
        exact congrArg Subtype.val h
      have hcomm : Commute a.1 y :=
        commutatorElement_eq_one_iff_commute.mp haOne
      change y * a.1 * y⁻¹ = a.1
      rw [← hcomm.eq, mul_inv_cancel_right]
    · intro ha
      have haC : a.1 ∈ C := ha
      have haFixed := haC
      change y * a.1 * y⁻¹ = a.1 at haFixed
      have hcomm : Commute y a.1 := by
        rw [commute_iff_eq]
        have h := congrArg (fun z : G => z * y) haFixed
        simpa [mul_assoc] using h
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change ⁅a.1, y⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr hcomm.symm
  have hdeltaRangeNe : delta.range ≠ ⊥ := by
    intro hrange
    apply hneq
    apply le_antisymm hle
    intro b hb
    obtain ⟨a, ha⟩ := hf b
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact hb
    let aE : E := ⟨a, haE⟩
    have hdeltaOne : delta aE = 1 := by
      have hmem : delta aE ∈ delta.range := ⟨aE, rfl⟩
      rw [hrange] at hmem
      exact Subgroup.mem_bot.mp hmem
    have haComm : Commute a y := by
      apply commutatorElement_eq_one_iff_commute.mp
      exact congrArg Subtype.val hdeltaOne
    have haC : a ∈ C := by
      change y * a * y⁻¹ = a
      rw [← haComm.eq, mul_inv_cancel_right]
    exact ⟨a, haC, ha⟩
  have hdeltaRangeCard : Nat.card delta.range = 2 := by
    have hRangeDvdKer : Nat.card delta.range ∣ Nat.card f.ker := by
      simpa [Subgroup.card_top] using
        (Subgroup.card_dvd_of_le
          (show delta.range ≤ (⊤ : Subgroup f.ker) from le_top))
    rw [hkerCard] at hRangeDvdKer
    rcases Nat.dvd_prime Nat.prime_two |>.mp hRangeDvdKer with hOne | hTwo
    · have hbot : delta.range = ⊥ := by
        exact Subgroup.eq_bot_of_card_eq delta.range hOne
      exact (hdeltaRangeNe hbot).elim
    · exact hTwo
  have hCindexE : (C.subgroupOf E).index = 2 := by
    calc
      (C.subgroupOf E).index = delta.ker.index :=
        congrArg Subgroup.index hdeltaKer.symm
      _ = Nat.card delta.range := Subgroup.index_ker delta
      _ = 2 := hdeltaRangeCard
  have hqker : q.ker ≤ C.subgroupOf E := by
    intro a ha
    have hfa : f a.1 = 1 := by
      have h := MonoidHom.mem_ker.mp ha
      exact congrArg Subtype.val h
    have haCenter : a.1 ∈ Subgroup.center G := by
      apply hker
      exact MonoidHom.mem_ker.mpr hfa
    change y * a.1 * y⁻¹ = a.1
    have hcomm : Commute y a.1 :=
      Subgroup.mem_center_iff.mp haCenter y
    rw [hcomm.eq, mul_inv_cancel_right]
  have hmap : (C.subgroupOf E).map q = (C.map f).subgroupOf Cbar := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      change f a.1 ∈ C.map f
      exact ⟨a.1, ha, rfl⟩
    · intro hb
      change b.1 ∈ C.map f at hb
      obtain ⟨a, haC, ha⟩ := hb
      have haE : a ∈ E := hCE haC
      let aE : E := ⟨a, haE⟩
      refine ⟨aE, ?_, ?_⟩
      · exact haC
      · apply Subtype.ext
        exact ha
  refine ⟨hle, ?_⟩
  rw [← hmap]
  exact (Subgroup.index_map_eq (C.subgroupOf E) hq hqker).trans hCindexE

end GLS3.Chapter5
/- END Theory.FixedSubgroupImageIndexTwo -/

/- BEGIN Theory.ElementaryAbelianQuotientExtraspecial -/
noncomputable section

namespace GLS3.Chapter5

/-- A finite `2`-group with center of order two is extraspecial or abelian when
its quotient by the center is explicitly realized as an `F₂`-vector group. -/
public theorem isExtraspecialTwoSubgroup_or_center_eq_top_of_vector_quotient
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hcenterCard : Nat.card (Subgroup.center P) = 2)
    (q : P →* Multiplicative V) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.center P) :
    IsExtraspecialTwoSubgroup P ∨ Subgroup.center P = ⊤ := by
  apply isExtraspecialTwoSubgroup_or_center_eq_top P hP hcenterCard
  rw [← hker]
  have hPhi := frattini_le_comap_frattini_of_surjective hq
  rw [frattini_multiplicative_zmod_two_module_eq_bot] at hPhi
  exact hPhi

/-- The surjectivity hypothesis is unnecessary when only the containment of
the Frattini subgroup in the kernel is used. -/
public theorem isExtraspecialTwoSubgroup_or_center_eq_top_of_vector_hom
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hcenterCard : Nat.card (Subgroup.center P) = 2)
    (q : P →* Multiplicative V)
    (hker : q.ker = Subgroup.center P) :
    IsExtraspecialTwoSubgroup P ∨ Subgroup.center P = ⊤ := by
  apply isExtraspecialTwoSubgroup_or_center_eq_top P hP hcenterCard
  rw [← hker]
  exact frattini_le_ker_of_hom_to_multiplicative_zmod_two_module q

end GLS3.Chapter5
/- END Theory.ElementaryAbelianQuotientExtraspecial -/

/- BEGIN Theory.CentralElementaryAbelianFourComplement -/
noncomputable section

namespace GLS3.Chapter5

/-- A prescribed central subgroup `Z` of order two inside a four-element
`F₂`-vector subgroup `X` has an ambient cyclic complement of order two. -/
public theorem exists_order_two_complement_subgroup
    {P V : Type*} [Group P] [Finite P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (X Z : Subgroup P) (hZX : Z ≤ X)
    (e : X ≃* Multiplicative V)
    (hXcard : Nat.card X = 4) (hZcard : Nat.card Z = 2) :
    ∃ Z1 : Subgroup P,
      Z ⊔ Z1 = X ∧ Z ⊓ Z1 = ⊥ ∧ Z1 ≤ X ∧
      Nat.card Z1 = 2 ∧ IsCyclic Z1 := by
  have hZXcard : Nat.card (Z.subgroupOf X) = 2 := by
    calc
      Nat.card (Z.subgroupOf X) = Nat.card Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv
      _ = 2 := hZcard
  obtain ⟨C, hsupC, hinfC, hCcard, hCcyclic⟩ :=
    exists_order_two_complement_of_vector_group e (Z.subgroupOf X)
      hXcard hZXcard
  let Z1 : Subgroup P := C.map X.subtype
  have hZ1le : Z1 ≤ X := by
    rintro y ⟨c, hc, rfl⟩
    exact c.2
  have hsup : Z ⊔ Z1 = X := by
    change Z ⊔ C.map X.subtype = X
    rw [← Subgroup.map_subgroupOf_eq_of_le hZX, ← Subgroup.map_sup,
      hsupC]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hinf : Z ⊓ Z1 = ⊥ := by
    change Z ⊓ C.map X.subtype = ⊥
    rw [← Subgroup.map_subgroupOf_eq_of_le hZX,
      ← Subgroup.map_inf _ _ _ X.subtype_injective, hinfC,
      Subgroup.map_bot]
  have hZ1card : Nat.card Z1 = 2 := by
    change Nat.card (C.map X.subtype) = 2
    calc
      Nat.card (C.map X.subtype) = Nat.card C :=
        Nat.card_congr (Subgroup.equivMapOfInjective C X.subtype
          X.subtype_injective).symm.toEquiv
      _ = 2 := hCcard
  refine ⟨Z1, hsup, hinf, hZ1le, hZ1card, ?_⟩
  exact isCyclic_of_prime_card hZ1card

end GLS3.Chapter5
/- END Theory.CentralElementaryAbelianFourComplement -/

/- BEGIN Theory.AutomorphismFixedSubgroupImageIndexTwo -/
noncomputable section

namespace GLS3.Chapter5

/-- For compatible automorphisms across a surjection with central kernel of
order two, a proper fixed-point image has index exactly two. -/
public theorem automorphismFixedSubgroup_image_index_eq_two_of_failure
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (hkerCard : Nat.card f.ker = 2)
    (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    (hneq :
      (automorphismFixedSubgroup alpha).map f ≠
        automorphismFixedSubgroup beta) :
    ∃ _hle :
        (automorphismFixedSubgroup alpha).map f ≤
          automorphismFixedSubgroup beta,
      (((automorphismFixedSubgroup alpha).map f).subgroupOf
          (automorphismFixedSubgroup beta)).index = 2 := by
  let C := automorphismFixedSubgroup alpha
  let Cbar := automorphismFixedSubgroup beta
  have hle : C.map f ≤ Cbar := by
    rintro _ ⟨a, ha, rfl⟩
    change beta (f a) = f a
    rw [← hcompat]
    exact congrArg f ha
  let E := Cbar.comap f
  have hCE : C ≤ E := by
    intro a ha
    exact hle ⟨a, ha, rfl⟩
  let q : E →* Cbar :=
    (f.comp E.subtype).codRestrict Cbar (fun a => a.2)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := hf b.1
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact b.2
    refine ⟨⟨a, haE⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hcKer : ∀ a : E, alpha a.1 * a.1⁻¹ ∈ f.ker := by
    intro a
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcompat]
    have ha := a.2
    change beta (f a.1) = f a.1 at ha
    rw [ha, mul_inv_cancel]
  have hcCenter : ∀ a : E,
      alpha a.1 * a.1⁻¹ ∈ Subgroup.center G :=
    fun a => hker (hcKer a)
  let deltaCenter : E →* Subgroup.center G :=
    automorphismDefectHom E.subtype alpha hcCenter
  let delta : E →* f.ker := {
    toFun := fun a => ⟨(deltaCenter a).1, by
      change alpha a.1 * a.1⁻¹ ∈ f.ker
      exact hcKer a⟩
    map_one' := by
      apply Subtype.ext
      change (deltaCenter 1).1 = 1
      exact congrArg Subtype.val (map_one deltaCenter)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change (deltaCenter (a * b)).1 =
        (deltaCenter a).1 * (deltaCenter b).1
      exact congrArg Subtype.val (map_mul deltaCenter a b) }
  have hdeltaKer : delta.ker = C.subgroupOf E := by
    ext a
    constructor
    · intro ha
      have haOne : alpha a.1 * a.1⁻¹ = 1 := by
        have h := MonoidHom.mem_ker.mp ha
        exact congrArg Subtype.val h
      change alpha a.1 = a.1
      have h := congrArg (fun z : G => z * a.1) haOne
      simpa [mul_assoc] using h
    · intro ha
      have haC : a.1 ∈ C := ha
      change alpha a.1 = a.1 at haC
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change alpha a.1 * a.1⁻¹ = 1
      rw [haC, mul_inv_cancel]
  have hdeltaRangeNe : delta.range ≠ ⊥ := by
    intro hrange
    apply hneq
    apply le_antisymm hle
    intro b hb
    obtain ⟨a, ha⟩ := hf b
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact hb
    let aE : E := ⟨a, haE⟩
    have hdeltaOne : delta aE = 1 := by
      have hmem : delta aE ∈ delta.range := ⟨aE, rfl⟩
      rw [hrange] at hmem
      exact Subgroup.mem_bot.mp hmem
    have haFixed : alpha a = a := by
      have hdefect : alpha a * a⁻¹ = 1 :=
        congrArg Subtype.val hdeltaOne
      have h := congrArg (fun z : G => z * a) hdefect
      simpa [mul_assoc] using h
    exact ⟨a, haFixed, ha⟩
  have hdeltaRangeCard : Nat.card delta.range = 2 := by
    have hRangeDvdKer : Nat.card delta.range ∣ Nat.card f.ker := by
      simpa [Subgroup.card_top] using
        (Subgroup.card_dvd_of_le
          (show delta.range ≤ (⊤ : Subgroup f.ker) from le_top))
    rw [hkerCard] at hRangeDvdKer
    rcases (Nat.dvd_prime Nat.prime_two).mp hRangeDvdKer with hOne | hTwo
    · have hbot : delta.range = ⊥ :=
        Subgroup.eq_bot_of_card_eq delta.range hOne
      exact (hdeltaRangeNe hbot).elim
    · exact hTwo
  have hCindexE : (C.subgroupOf E).index = 2 := by
    calc
      (C.subgroupOf E).index = delta.ker.index :=
        congrArg Subgroup.index hdeltaKer.symm
      _ = Nat.card delta.range := Subgroup.index_ker delta
      _ = 2 := hdeltaRangeCard
  have hqker : q.ker ≤ C.subgroupOf E := by
    intro a ha
    have hfa : f a.1 = 1 := by
      have h := MonoidHom.mem_ker.mp ha
      exact congrArg Subtype.val h
    change alpha a.1 = a.1
    have haKer : a.1 ∈ f.ker := MonoidHom.mem_ker.mpr hfa
    have hAlphaKer : alpha a.1 ∈ f.ker := by
      rw [MonoidHom.mem_ker, hcompat, hfa, map_one]
    have hnononeUnique : ∀ u v : f.ker,
        u ≠ 1 → v ≠ 1 → u = v := by
      obtain ⟨u, v, huv, huvUniv⟩ := Nat.card_eq_two_iff.mp hkerCard
      intro c d hc hd
      have hone : (1 : f.ker) = u ∨ (1 : f.ker) = v := by
        have hmem : (1 : f.ker) ∈ ({u, v} : Set f.ker) := by
          rw [huvUniv]
          exact Set.mem_univ 1
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
      have hcuv : c = u ∨ c = v := by
        have hmem : c ∈ ({u, v} : Set f.ker) := by
          rw [huvUniv]
          exact Set.mem_univ c
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
      have hduv : d = u ∨ d = v := by
        have hmem : d ∈ ({u, v} : Set f.ker) := by
          rw [huvUniv]
          exact Set.mem_univ d
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
      rcases hone with hone | hone <;> rcases hcuv with hcuv | hcuv <;>
        rcases hduv with hduv | hduv
      all_goals subst_vars
      all_goals first | rfl | contradiction
    by_cases haOne : a.1 = 1
    · simp [haOne]
    have hAlphaOne : alpha a.1 ≠ 1 := by
      intro h
      apply haOne
      apply alpha.injective
      rw [h, map_one]
    have heq : (⟨alpha a.1, hAlphaKer⟩ : f.ker) = ⟨a.1, haKer⟩ :=
      hnononeUnique _ _ (by simpa using hAlphaOne) (by simpa using haOne)
    exact congrArg Subtype.val heq
  have hmap : (C.subgroupOf E).map q = (C.map f).subgroupOf Cbar := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      change f a.1 ∈ C.map f
      exact ⟨a.1, ha, rfl⟩
    · intro hb
      change b.1 ∈ C.map f at hb
      obtain ⟨a, haC, ha⟩ := hb
      have haE : a ∈ E := hCE haC
      let aE : E := ⟨a, haE⟩
      refine ⟨aE, ?_, ?_⟩
      · exact haC
      · apply Subtype.ext
        exact ha
  refine ⟨hle, ?_⟩
  rw [← hmap]
  exact (Subgroup.index_map_eq (C.subgroupOf E) hq hqker).trans hCindexE

end GLS3.Chapter5
/- END Theory.AutomorphismFixedSubgroupImageIndexTwo -/

/- BEGIN Theory.AutomorphismFixedSubgroupImageNormal -/
noncomputable section

namespace GLS3.Chapter5

/-- Under a surjection with central kernel, the image of a fixed subgroup is
normal in the fixed subgroup of the compatible quotient automorphism. -/
public theorem automorphismFixedSubgroup_image_normal
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    (hle : (automorphismFixedSubgroup alpha).map f ≤
      automorphismFixedSubgroup beta) :
    (((automorphismFixedSubgroup alpha).map f).subgroupOf
      (automorphismFixedSubgroup beta)).Normal := by
  let C := automorphismFixedSubgroup alpha
  let Cbar := automorphismFixedSubgroup beta
  let E := Cbar.comap f
  have hCE : C ≤ E := by
    intro a ha
    exact hle ⟨a, ha, rfl⟩
  let q : E →* Cbar :=
    (f.comp E.subtype).codRestrict Cbar (fun a => a.2)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := hf b.1
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact b.2
    refine ⟨⟨a, haE⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hcKer : ∀ a : E, alpha a.1 * a.1⁻¹ ∈ f.ker := by
    intro a
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcompat]
    have ha := a.2
    change beta (f a.1) = f a.1 at ha
    rw [ha, mul_inv_cancel]
  have hcCenter : ∀ a : E,
      alpha a.1 * a.1⁻¹ ∈ Subgroup.center G :=
    fun a => hker (hcKer a)
  let deltaCenter : E →* Subgroup.center G :=
    automorphismDefectHom E.subtype alpha hcCenter
  let delta : E →* f.ker :=
    { toFun := fun a => ⟨(deltaCenter a).1, hcKer a⟩
      map_one' := by
        apply Subtype.ext
        change (deltaCenter 1).1 = 1
        exact congrArg Subtype.val (map_one deltaCenter)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change (deltaCenter (a * b)).1 =
          (deltaCenter a).1 * (deltaCenter b).1
        exact congrArg Subtype.val (map_mul deltaCenter a b) }
  have hdeltaKer : delta.ker = C.subgroupOf E := by
    ext a
    constructor
    · intro ha
      have haOne : alpha a.1 * a.1⁻¹ = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
      change alpha a.1 = a.1
      have h := congrArg (fun z : G => z * a.1) haOne
      simpa [mul_assoc] using h
    · intro ha
      have haC : a.1 ∈ C := ha
      change alpha a.1 = a.1 at haC
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change alpha a.1 * a.1⁻¹ = 1
      rw [haC, mul_inv_cancel]
  have hmap : (C.subgroupOf E).map q = (C.map f).subgroupOf Cbar := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      change f a.1 ∈ C.map f
      exact ⟨a.1, ha, rfl⟩
    · intro hb
      change b.1 ∈ C.map f at hb
      obtain ⟨a, haC, ha⟩ := hb
      let aE : E := ⟨a, hCE haC⟩
      refine ⟨aE, haC, ?_⟩
      apply Subtype.ext
      exact ha
  rw [← hmap, ← hdeltaKer]
  exact (inferInstance : delta.ker.Normal).map q hq

end GLS3.Chapter5
/- END Theory.AutomorphismFixedSubgroupImageNormal -/

/- BEGIN KGroup.GLS3.Chapter5.theorem_5_2_2 -/
universe __ch5_theorem_5_2_2_u

/- Source: theorem_5_2_2_a.lean -/

namespace GLS3.Chapter5

public theorem theorem_5_2_2_a_split {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] (x : Equiv.Perm Ω) :
    (⋃ i ∈ Finset.Icc 1 (Fintype.card Ω), orbitLengthSet x i) = Set.univ ∧
      (↑(Finset.Icc 1 (Fintype.card Ω)) : Set ℕ).PairwiseDisjoint
        (orbitLengthSet x) :=
  theorem_5_2_2_a x

end GLS3.Chapter5

/- Source: theorem_5_2_2_b.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_b_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] (x : Equiv.Perm Ω) :=
  theorem_5_2_2_b x

end GLS3.Chapter5

/- Source: theorem_5_2_2_c.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_c_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :=
  theorem_5_2_2_c x

end GLS3.Chapter5

-- These legacy public wrappers remain reducible definitions for API compatibility.
-- A future cleanup can migrate the proposition-valued wrappers to theorems.
section legacyPublicPropDefinitions
set_option linter.defProp false

/- Source: theorem_5_2_2_d_1.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_d_1_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_d_1 x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_2_a.lean -/

namespace GLS3.Chapter5

public theorem theorem_5_2_2_d_2_a_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (a b : cycleRotationSubgroup x) :
    a * b = b * a :=
  theorem_5_2_2_d_2_a x a b

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_2_b.lean -/

namespace GLS3.Chapter5

public theorem theorem_5_2_2_d_2_b_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : cycleRotationSubgroup x) :
    a ^ orderOf x = 1 :=
  theorem_5_2_2_d_2_b x hx a

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_2_c.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_d_2_c_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_d_2_c x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_3_a.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_d_3_a_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_d_3_a x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_3_b.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_d_3_b_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_d_3_b x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_d_4.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_d_4_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    := theorem_5_2_2_d_4 x

end GLS3.Chapter5

/- Source: theorem_5_2_2_e_1.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_e_1_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_e_1 x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_e_2.lean -/

namespace GLS3.Chapter5

public theorem theorem_5_2_2_e_2_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :
    orderOf (primeCycleNormalizerGenerator x hx) = orderOf x - 1 :=
  theorem_5_2_2_e_2 x hx

end GLS3.Chapter5

/- Source: theorem_5_2_2_e_3_a.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_e_3_a_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (a : CycleRotationGroup x) :=
  theorem_5_2_2_e_3_a x hx a

end GLS3.Chapter5

/- Source: theorem_5_2_2_e_3_b.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_e_3_b_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) (z : ℤ)
    (hz : primeCycleNormalizerGenerator x hx ^ z ≠ 1)
    (r : cycleRotationSubgroup x)
    (hcomm : Commute (primeCycleNormalizerGenerator x hx ^ z) r.1.1) :=
  theorem_5_2_2_e_3_b x hx z hz r hcomm

end GLS3.Chapter5

/- Source: theorem_5_2_2_e_4.lean -/

namespace GLS3.Chapter5

public noncomputable def theorem_5_2_2_e_4_split
    {Ω : Type __ch5_theorem_5_2_2_u} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω)
    (hx : (orderOf x).Prime) :=
  theorem_5_2_2_e_4 x hx

end GLS3.Chapter5

end legacyPublicPropDefinitions
/- END KGroup.GLS3.Chapter5.theorem_5_2_2 -/

/- BEGIN Theory.CyclePermutationCentralizerRotationDisjoint -/
namespace GLS3.Chapter5

/-- The chosen cycle-permuting complement acts faithfully on the rotation
subgroup. -/
public theorem cyclePermutationSubgroup_inf_centralizer_cycleRotation_eq_bot
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (x : Equiv.Perm Ω) :
    cyclePermutationSubgroup x ⊓
        Subgroup.centralizer (cycleRotationSubgroup x : Set _) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro l hl
  rcases hl.1 with ⟨q, hq⟩
  have hlker : l ∈ (Equiv.Perm.OnCycleFactors.toPermHom x).ker := by
    rw [Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff]
    intro c hc
    let cC : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)) :=
      ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr
        (Equiv.Perm.self_mem_cycle_factors_commute hc).eq⟩
    have hcR : cC ∈
        cycleRotationSubgroup x := by
      rw [mem_cycleRotationSubgroup_iff]
      constructor
      · rw [Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff]
        intro d hd
        by_cases hcd : c = d
        · subst d
          exact Commute.refl c
        · exact Equiv.Perm.cycleFactorsFinset_mem_commute x hc hd hcd
      · intro ω
        apply Equiv.Perm.notMem_support.mp
        intro hωc
        exact (Equiv.Perm.mem_support.mp
          (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hωc)) ω.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hl.2 _ hcR
    exact (congrArg Subtype.val hcomm).symm
  have hqone : q = 1 := by
    have hsplit := congrArg Subtype.val
      ((cycleCentralizerSplitting x).rightHom_splitting q)
    apply Subtype.ext
    calc
      q.1 = ((cycleCentralizerExtension x).rightHom
          ((cycleCentralizerSplitting x) q)).1 := hsplit.symm
      _ = (Equiv.Perm.OnCycleFactors.toPermHom x)
          ((cycleCentralizerSplitting x) q) := rfl
      _ = (Equiv.Perm.OnCycleFactors.toPermHom x) l :=
        congrArg (Equiv.Perm.OnCycleFactors.toPermHom x) hq
      _ = 1 := MonoidHom.mem_ker.mp hlker
  subst q
  simpa using hq.symm

end GLS3.Chapter5
/- END Theory.CyclePermutationCentralizerRotationDisjoint -/

/- BEGIN Theory.InvolutionCycleRotationSign -/
noncomputable section

open scoped BigOperators

namespace GLS3.Chapter5
universe __ch5_InvolutionCycleRotationSign_u

/-- Coordinates on the independent rotations of the nontrivial cycles of an
involution. Each cycle rotation is identified with its exponent in `ZMod 2`.-/
@[expose]
public noncomputable def involutionCycleRotationCoordinates
    {Ω : Type __ch5_InvolutionCycleRotationSign_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    CycleRotationGroup x ≃*
      ((c : x.cycleFactorsFinset) → Multiplicative (ZMod 2)) := by
  apply MulEquiv.piCongrRight
  intro c
  exact (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
    (by
      simpa [hx] using
        (cycleFactorZPowers_card_of_primeOrder x
          (by simpa [hx] using Nat.prime_two) c))).symm

@[simp]
public theorem involutionCycleRotationCoordinates_apply
    {Ω : Type __ch5_InvolutionCycleRotationSign_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (a : CycleRotationGroup x) (c : x.cycleFactorsFinset) :
    involutionCycleRotationCoordinates x hx a c =
      (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
        (by
          simpa [hx] using
            (cycleFactorZPowers_card_of_primeOrder x
              (by simpa [hx] using Nat.prime_two) c))).symm (a c) := rfl

private theorem __ch5_InvolutionCycleRotationSign_involutionCycleRotationCoordinate_sign
    {Ω : Type __ch5_InvolutionCycleRotationSign_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c : x.cycleFactorsFinset) (a : Subgroup.zpowers c.1) :
    Equiv.Perm.sign a.1 = (-1 : ℤˣ) ^
      (Multiplicative.toAdd
        ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
          (by
            simpa [hx] using
              (cycleFactorZPowers_card_of_primeOrder x
                (by simpa [hx] using Nat.prime_two) c))).symm a)) := by
  let e : Multiplicative (ZMod 2) ≃* Subgroup.zpowers c.1 :=
    zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (by
        simpa [hx] using
          (cycleFactorZPowers_card_of_primeOrder x
            (by simpa [hx] using Nat.prime_two) c))
  let z : ZMod 2 := Multiplicative.toAdd (e.symm a)
  have ha : a = e (Multiplicative.ofAdd z) :=
    (e.apply_symm_apply a).symm
  change Equiv.Perm.sign a.1 = (-1 : ℤˣ) ^ z
  have hzlt : z.val < 2 := ZMod.val_lt z
  have hz01 : z.val = 0 ∨ z.val = 1 := by omega
  rcases hz01 with hzval | hzval
  · have hz : z = 0 := by
      apply ZMod.val_injective 2
      simpa using hzval
    rw [ha, hz]
    simp [e]
  · have hz : z = 1 := by
      apply ZMod.val_injective 2
      rw [ZMod.val_one]
      exact hzval
    rw [ha, hz]
    have hcCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
    have hcard : c.1.support.card = 2 :=
      (cycleFactor_support_card_eq_orderOf_of_primeOrder x
        (by simpa [hx] using Nat.prime_two) c).trans hx
    rw [show e (Multiplicative.ofAdd (1 : ZMod 2)) =
        cycleFactorGenerator c by simp [e]]
    change Equiv.Perm.sign c.1 = (-1 : ℤˣ) ^ (1 : ZMod 2)
    rw [hcCycle.sign, hcard]
    norm_num

/-- For an involution, the sign of an independent cycle rotation is `-1`
raised to the sum of its `ZMod 2` rotation coordinates. Thus its even rotation
subgroup is exactly the coefficient-sum-zero subspace. -/
public theorem involutionCycleRotation_sign
    {Ω : Type __ch5_InvolutionCycleRotationSign_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (a : CycleRotationGroup x) :
    Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) =
      (-1 : ℤˣ) ^
        (∑ c, Multiplicative.toAdd
          ((involutionCycleRotationCoordinates x hx) a c)) := by
  rw [show Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) =
      ∏ c, Equiv.Perm.sign (a c).1 by
    change Equiv.Perm.sign
      (Equiv.Perm.OnCycleFactors.kerParam x (1, a)) = _
    rw [Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply]
    simp]
  simp_rw [show ∀ c, Equiv.Perm.sign (a c).1 = (-1 : ℤˣ) ^
      (Multiplicative.toAdd
        ((involutionCycleRotationCoordinates x hx) a c)) by
    intro c
    exact __ch5_InvolutionCycleRotationSign_involutionCycleRotationCoordinate_sign x hx c (a c)]
  have hpow (s : Finset x.cycleFactorsFinset) :
      (∏ c ∈ s, (-1 : ℤˣ) ^
        Multiplicative.toAdd
          ((involutionCycleRotationCoordinates x hx) a c)) =
      (-1 : ℤˣ) ^
        (∑ c ∈ s, Multiplicative.toAdd
          ((involutionCycleRotationCoordinates x hx) a c)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        rw [Finset.prod_insert hc, Finset.sum_insert hc, uzpow_add, ih]
  simpa using hpow Finset.univ

end GLS3.Chapter5
/- END Theory.InvolutionCycleRotationSign -/
