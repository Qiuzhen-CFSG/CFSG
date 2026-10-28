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

public import Theory.Alternating.Reduction
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.InvolutionCycleAlternatingEmbedding -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionCycleAlternatingEmbedding_u

/-- The alternating group on the set of nontrivial cycles of an involution,
embedded through the natural cycle-permutation complement. -/
@[expose]
public noncomputable def involutionCycleAlternatingEmbedding
    {Ω : Type __ch5_InvolutionCycleAlternatingEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    alternatingGroup x.cycleFactorsFinset →* alternatingGroup Ω where
  toFun σ :=
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm σ.1
    ⟨l.1.1, Equiv.Perm.mem_alternatingGroup.mpr
      (involutionCyclePermutation_sign x hx l)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

/-- Reindex the cycle set by `Fin (q+5)` before applying the natural
alternating cycle embedding. -/
@[expose]
public noncomputable def involutionCycleAlternatingEmbeddingFin
    {Ω : Type __ch5_InvolutionCycleAlternatingEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (q : Nat)
    (eFin : x.cycleFactorsFinset ≃ Fin (q + 5)) :
    alternatingGroup (Fin (q + 5)) →* alternatingGroup Ω :=
  (involutionCycleAlternatingEmbedding x hx).comp
    eFin.altCongrHom.symm.toMonoidHom

/-- The natural alternating cycle embedding is injective after any finite
reindexing of the cycle factors. -/
public theorem involutionCycleAlternatingEmbeddingFin_injective
    {Ω : Type __ch5_InvolutionCycleAlternatingEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (q : Nat)
    (eFin : x.cycleFactorsFinset ≃ Fin (q + 5)) :
    Function.Injective
      (involutionCycleAlternatingEmbeddingFin x hx q eFin) := by
  let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
  have hbase : Function.Injective (involutionCycleAlternatingEmbedding x hx) := by
    intro a b hab
    have hval := congrArg (fun z : alternatingGroup Ω => z.1) hab
    have hl : e.symm a.1 = e.symm b.1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [involutionCycleAlternatingEmbedding, e] using hval
    apply Subtype.ext
    exact e.symm.injective hl
  exact hbase.comp eFin.altCongrHom.symm.injective

end GLS3.Chapter5
/- END Theory.InvolutionCycleAlternatingEmbedding -/

/- BEGIN Theory.EvenCycleRotationsSignKernelEquiv -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_EvenCycleRotationsSignKernelEquiv_u

/-- The intersection of the ambient cycle-rotation subgroup with the even
centralizer is the intrinsic even cycle-rotation subgroup. -/
public noncomputable def evenCycleRotationsSignKernelEquiv
    {Ω : Type __ch5_EvenCycleRotationsSignKernelEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    (cycleRotationSubgroup x).comap Z.subtype ≃*
      evenInvolutionCycleRotations x := by
  dsimp only
  let e := cycleRotationGroupMulEquivSubgroup x
  exact {
    toFun := fun z => ⟨e.symm ⟨z.1.1, z.2⟩, by
      rw [mem_evenInvolutionCycleRotations]
      change Equiv.Perm.sign (e (e.symm ⟨z.1.1, z.2⟩)).1.1 = 1
      rw [e.apply_symm_apply]
      exact MonoidHom.mem_ker.mp z.1.2⟩
    invFun := fun a => ⟨⟨(e a.1).1, by
      rw [MonoidHom.mem_ker]
      change Equiv.Perm.sign (e a.1).1.1 = 1
      exact (mem_evenInvolutionCycleRotations x a.1).mp a.2⟩, (e a.1).2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z.1.1, z.2⟩)
    right_inv := by
      intro a
      apply Subtype.ext
      exact e.symm_apply_apply a.1
    map_mul' := by
      intro a b
      apply Subtype.ext
      change e.symm ⟨(a * b).1.1, _⟩ =
        e.symm ⟨a.1.1, _⟩ * e.symm ⟨b.1.1, _⟩
      rw [← e.symm.map_mul]
      congr 1
  }

@[simp]
public theorem evenCycleRotationsSignKernelEquiv_apply_coe
    {Ω : Type __ch5_EvenCycleRotationsSignKernelEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (z : (cycleRotationSubgroup x).comap
      (Equiv.Perm.sign.comp
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker.subtype) :
    cycleRotationToCentralizer x
      ((evenCycleRotationsSignKernelEquiv x z).1) = z.1.1 := by
  let e := cycleRotationGroupMulEquivSubgroup x
  change e (e.symm ⟨z.1.1, z.2⟩) = z.1.1
  exact congrArg (fun q : cycleRotationSubgroup x => q.1)
    (e.apply_symm_apply ⟨z.1.1, z.2⟩)

end GLS3.Chapter5
/- END Theory.EvenCycleRotationsSignKernelEquiv -/

/- BEGIN Theory.FixedPointPermutationSignKernelEquiv -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_FixedPointPermutationSignKernelEquiv_u

/-- The fixed-point factor in the even centralizer is the alternating group
on the fixed points. -/
@[expose]
public noncomputable def fixedPointPermutationSignKernelEquiv
    {Ω : Type __ch5_FixedPointPermutationSignKernelEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    (fixedPointPermutationSubgroup x).comap Z.subtype ≃*
      alternatingGroup (Function.fixedPoints x) := by
  dsimp only
  let e := theorem_5_2_2_d_4 x
  exact {
    toFun := fun z => ⟨e ⟨z.1.1, z.2⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]
      rw [← fixedPointPermutation_sign x ⟨z.1.1, z.2⟩]
      exact MonoidHom.mem_ker.mp z.1.2⟩
    invFun := fun a => ⟨⟨(e.symm a.1).1, by
      rw [MonoidHom.mem_ker]
      change Equiv.Perm.sign (e.symm a.1).1.1 = 1
      rw [fixedPointPermutation_sign x (e.symm a.1), e.apply_symm_apply]
      exact Equiv.Perm.mem_alternatingGroup.mp a.2⟩, (e.symm a.1).2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      exact congrArg Subtype.val (e.symm_apply_apply ⟨z.1.1, z.2⟩)
    right_inv := by
      intro a
      apply Subtype.ext
      exact e.apply_symm_apply a.1
    map_mul' := by
      intro a b
      apply Subtype.ext
      change e ⟨(a * b).1.1, _⟩ =
        e ⟨a.1.1, _⟩ * e ⟨b.1.1, _⟩
      rw [← e.map_mul]
      congr 1
  }

end GLS3.Chapter5
/- END Theory.FixedPointPermutationSignKernelEquiv -/

/- BEGIN Theory.InvolutionRotationPermutationKernelPullback -/
namespace GLS3.Chapter5
universe __ch5_InvolutionRotationPermutationKernelPullback_u

/-- For an involution, the even part of the rotation-permutation factor is the
join of the even rotations and the full cycle-permuting complement. -/
public theorem involutionRotationPermutationKernelPullback
    {Ω : Type __ch5_InvolutionRotationPermutationKernelPullback_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    let R := cycleRotationSubgroup x
    let L := cyclePermutationSubgroup x
    let H := R ⊔ L
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    H.comap Z.subtype = RZ ⊔ LZ := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let H : Subgroup C := R ⊔ L
  let RZ : Subgroup Z := R.comap Z.subtype
  let LZ : Subgroup Z := L.comap Z.subtype
  have hLχ : L ≤ χ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact involutionCyclePermutation_sign x hx ⟨l, hl⟩
  have hLnorm : L ≤ Subgroup.normalizer R :=
    cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x
  apply le_antisymm
  · intro z hz
    have hzH : z.1 ∈ (↑H : Set C) := hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hLnorm] at hzH
    rcases hzH with ⟨r, hr, l, hl, hrl⟩
    have hlχ : χ l = 1 := MonoidHom.mem_ker.mp (hLχ hl)
    have hzχ : χ z.1 = 1 := MonoidHom.mem_ker.mp z.2
    have hrχ : χ r = 1 := by
      rw [← hrl, map_mul, hlχ, mul_one] at hzχ
      exact hzχ
    let rz : Z := ⟨r, MonoidHom.mem_ker.mpr hrχ⟩
    let lz : Z := ⟨l, hLχ hl⟩
    have hzl : z = rz * lz := Subtype.ext hrl.symm
    rw [hzl]
    exact (RZ ⊔ LZ).mul_mem
      ((le_sup_left : RZ ≤ RZ ⊔ LZ) hr)
      ((le_sup_right : LZ ≤ RZ ⊔ LZ) hl)
  · apply sup_le
    · intro z hz
      exact (le_sup_left : R ≤ H) hz
    · intro z hz
      exact (le_sup_right : L ≤ H) hz

end GLS3.Chapter5
/- END Theory.InvolutionRotationPermutationKernelPullback -/

/- BEGIN Theory.OddPrimeMultiplierBound -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-! # Exclusion of prime divisors at least five

Strong induction on the alternating degree combines the point-stabilizer
reduction, the nontransitive orbit reduction, and the imprimitive prime-power
endpoint.  It proves the odd-prime part of A1 33.15: no prime at least five
divides an alternating Schur multiplier.
-/

/-- No prime `p ≥ 5` divides the kernel of the universal central covering of
an alternating group. -/
public theorem not_dvd_natCard_ker_alternatingFreeCentralCovering_of_five_le_prime
    (p n : Nat) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hpker
    by_cases hn0 : n = 0
    · subst n
      rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two] at hpker
      exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) hpker
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hpPred : ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker := by
      apply ih
      omega
    have hpdeg : p ∣ n + 5 :=
      prime_dvd_degree_of_dvd_multiplier_of_not_dvd_predecessor
        n hn1 hpker hpPred
    let f := alternatingFreeCentralCovering n
    obtain ⟨X, hX, fbar, _hXker, hbarSurj, hbarCenter, hbarP, hpbar⟩ :=
      exists_pPrimary_quotient_central_extension
        f.toMonoidHom f.surjective f.ker_le_center hpker
    let : X.Normal := hX
    let P : Sylow p (AlternatingFreeCentralDerived n ⧸ X) := default
    have hsmall : ∀ d : Nat, 5 ≤ d → d < n + 5 →
        ¬ p ∣ Nat.card
          (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker := by
      intro d hd5 hdn
      apply ih
      omega
    obtain ⟨r, hr⟩ :=
      exists_degree_eq_prime_pow_of_inductive_not_dvd
        (p := p) (by omega) hp5 (n + 5) (by omega) hpdeg
        fbar hbarSurj hbarCenter hbarP hpbar P hsmall
    have htwo : 2 * p ≤ n + 5 :=
      two_mul_prime_le_degree_of_dvd_natCard_ker_alternatingFreeCentralCovering
        n p hpker
    have hr2 : 2 ≤ r := by
      by_contra hrnot
      have hrCases : r = 0 ∨ r = 1 := by omega
      rcases hrCases with rfl | rfl
      · simp at hr htwo
      · simp at hr htwo
        omega
    let s := r - 1
    have hs : 0 < s := by omega
    let d := p ^ s
    have hps : p ≤ d := by
      dsimp [d]
      simpa only [pow_one] using (pow_le_pow_right₀ hp.one_le hs)
    have hd5 : 5 ≤ d := hp5.trans hps
    let qBase := d - 5
    let qTop := p - 5
    have hqBase : qBase + 5 = d := Nat.sub_add_cancel hd5
    have hqTop : qTop + 5 = p := Nat.sub_add_cancel hp5
    have hpow : qBase + 5 = (qTop + 5) ^ s := by
      rw [hqBase, hqTop]
    have hrsucc : r = s + 1 := by omega
    have hm : n + 5 = (qTop + 5) * (qBase + 5) := by
      calc
        n + 5 = p ^ r := hr
        _ = p ^ (s + 1) := by rw [hrsucc]
        _ = p * p ^ s := by rw [pow_succ']
        _ = (qTop + 5) * (qBase + 5) := by rw [hqTop, hqBase]
    have hdlt : d < n + 5 := by
      rw [hm, hqTop, hqBase]
      exact lt_mul_of_one_lt_left (pow_pos hp.pos s) hp.one_lt
    have hplt : p < n + 5 := by
      rw [hm, hqTop, hqBase]
      exact lt_mul_of_one_lt_right hp.pos (by omega : 1 < d)
    have hpBase : ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering qBase).toMonoidHom.ker := by
      exact hsmall d hd5 hdlt
    have hpTop : ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering qTop).toMonoidHom.ker := by
      exact hsmall p hp5 hplt
    have hbot := kernel_eq_bot_of_alternatingImprimitive_primePower_degree
      qBase qTop s (n + 5) (by simpa [hqTop] using hp) hs hpow hm
      fbar hbarSurj hbarCenter (by simpa [hqTop] using hbarP)
      (by simpa [hqTop] using hpBase) (by simpa [hqTop] using hpTop)
    rw [hbot, Subgroup.card_bot] at hpbar
    exact hp.ne_one (Nat.dvd_one.mp hpbar)

end GLS3.Chapter5.SchurPresentation
/- END Theory.OddPrimeMultiplierBound -/

/- BEGIN Theory.OrderThreeLift -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

/-! ## Order-three lifts

Every order-three alternating permutation is a product of pairwise disjoint
three-cycles.  The root-`A_5` splitting gives order-three lifts of the cycle
factors.  In a central extension, commutators of those lifts are central; the
class-two cube identity then shows that their ordered product again has cube
one.  Thus every order-three element, not only a single three-cycle, has an
order-three lift through a central 3-primary extension.
-/

private theorem
    __ch5_OrderThreeLift_commutator_cube_eq_one_of_cube_mem_center_of_commutator_mem_center
    {G : Type*} [Group G] {x y : G}
    (hxCube : x * x * x ∈ Subgroup.center G)
    (hc : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x, y⁆ * ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
  let c := ⁅x, y⁆
  have hpowComm : Commute (x * x * x) y :=
    (Subgroup.mem_center_iff.mp hxCube y).symm
  have hconj (a : G) : a * c * a⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc a, mul_inv_cancel_right]
  have hcomm := hpowComm.commutator_eq
  change ⁅x * x * x, y⁆ = 1 at hcomm
  rw [commutatorElement_mul_left_eq_conj_mul, hconj,
    commutatorElement_mul_left_eq_conj_mul, hconj] at hcomm
  simpa [c, mul_assoc] using hcomm

private theorem __ch5_OrderThreeLift_mul_cube_eq_one_of_cube_eq_one_of_commutator_mem_center
    {G : Type*} [Group G] {x y : G}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hc : ⁅x, y⁆ ∈ Subgroup.center G) :
    (x * y) ^ 3 = 1 := by
  let c := ⁅x, y⁆
  have hx' : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx
  have hy' : y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy
  have hc3 : c * c * c = 1 := by
    apply __ch5_OrderThreeLift_commutator_cube_eq_one_of_cube_mem_center_of_commutator_mem_center
    · rw [hx']
      exact one_mem _
    · exact hc
  have hcx : Commute c x := (Subgroup.mem_center_iff.mp hc x).symm
  have hcy : Commute c y := (Subgroup.mem_center_iff.mp hc y).symm
  have hxy : x * y = c * (y * x) := by
    dsimp [c]
    simp [commutatorElement_def, mul_assoc]
  have hyx : y * x = c⁻¹ * (x * y) := by
    calc
      y * x = c⁻¹ * (c * (y * x)) := by group
      _ = c⁻¹ * (x * y) := by rw [← hxy]
  have hcinvx : Commute c⁻¹ x := hcx.inv_left
  have hcinvy : Commute c⁻¹ y := hcy.inv_left
  have hxcinv : x * c⁻¹ = c⁻¹ * x := hcinvx.symm.eq
  have hycinv : y * c⁻¹ = c⁻¹ * y := hcinvy.symm.eq
  have hyyx : (y * y) * x = (c⁻¹ * c⁻¹) * (x * (y * y)) := by
    calc
      (y * y) * x = y * (y * x) := by group
      _ = y * (c⁻¹ * (x * y)) := by rw [hyx]
      _ = c⁻¹ * (y * x) * y := by
        rw [← mul_assoc y c⁻¹, hycinv]
        group
      _ = c⁻¹ * (c⁻¹ * (x * y)) * y := by rw [hyx]
      _ = (c⁻¹ * c⁻¹) * (x * (y * y)) := by group
  have hxxci2 : (x * x) * (c⁻¹ * c⁻¹) =
      (c⁻¹ * c⁻¹) * (x * x) := by
    exact ((hcinvx.mul_left hcinvx).mul_right
      (hcinvx.mul_left hcinvx)).symm.eq
  calc
    (x * y) ^ 3 = x * (y * x) * y * x * y := by
      simp only [pow_succ]
      group
    _ = x * (c⁻¹ * (x * y)) * y * x * y := by rw [hyx]
    _ = c⁻¹ * (x * x) * (y * y) * x * y := by
      rw [← mul_assoc x c⁻¹, hxcinv]
      group
    _ = c⁻¹ * (x * x) * (((y * y) * x) * y) := by group
    _ = c⁻¹ * (x * x) *
        (((c⁻¹ * c⁻¹) * (x * (y * y))) * y) := by rw [hyyx]
    _ = c⁻¹ * (((x * x) * (c⁻¹ * c⁻¹)) *
        (x * (y * y))) * y := by group
    _ = c⁻¹ * (((c⁻¹ * c⁻¹) * (x * x)) *
        (x * (y * y))) * y := by rw [hxxci2]
    _ = c⁻¹ * c⁻¹ * c⁻¹ * (x * x * x) * (y * y * y) := by group
    _ = c⁻¹ * c⁻¹ * c⁻¹ := by rw [hx', hy']; simp
    _ = 1 := by
      have h := congrArg Inv.inv hc3
      simpa [mul_inv_rev, mul_assoc] using h

private theorem __ch5_OrderThreeLift_exists_list_threeCycle_lift_cube_eq_one
    {H : Type*} [Group H] [Finite H]
    (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (l : List (Equiv.Perm (Fin (n + 5))))
    (hthree : ∀ a ∈ l, Equiv.Perm.IsThreeCycle a)
    (hcomm : l.Pairwise Commute) :
    ∃ y : H, (f y).1 = l.prod ∧ y ^ 3 = 1 := by
  induction l with
  | nil =>
      exact ⟨1, by simp, by simp⟩
  | cons a l ih =>
      have haThree : Equiv.Perm.IsThreeCycle a := hthree a (by simp)
      let aA : alternatingGroup (Fin (n + 5)) :=
        ⟨a, haThree.mem_alternatingGroup⟩
      obtain ⟨ya, hya, hordya⟩ :=
        exists_threeCycle_lift_order_three n f hf hker hker3 aA haThree
      have hya3 : ya ^ 3 = 1 := by
        rw [← hordya]
        exact pow_orderOf_eq_one ya
      have hthreeTail : ∀ b ∈ l, Equiv.Perm.IsThreeCycle b := by
        intro b hb
        exact hthree b (by simp [hb])
      have hcommHead : ∀ b ∈ l, Commute a b :=
        (List.pairwise_cons.mp hcomm).1
      have hcommTail : l.Pairwise Commute :=
        (List.pairwise_cons.mp hcomm).2
      obtain ⟨yl, hyl, hyl3⟩ := ih hthreeTail hcommTail
      have haProd : Commute a l.prod :=
        Commute.list_prod_right l a hcommHead
      have hcommKer : ⁅ya, yl⁆ ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        rw [map_commutatorElement]
        apply Subtype.ext
        change ⁅(f ya).1, (f yl).1⁆ = 1
        rw [hya, hyl]
        exact haProd.commutator_eq
      refine ⟨ya * yl, ?_,
        __ch5_OrderThreeLift_mul_cube_eq_one_of_cube_eq_one_of_commutator_mem_center
          hya3 hyl3 (hker hcommKer)⟩
      rw [map_mul]
      change (f ya).1 * (f yl).1 = a * l.prod
      rw [hya, hyl]

private theorem __ch5_OrderThreeLift_isThreeCycle_of_mem_cycleFactors_of_cube_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hσ3 : σ ^ 3 = 1)
    {c : Equiv.Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    Equiv.Perm.IsThreeCycle c := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcCycle : Equiv.Perm.IsCycle c :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  have hcardMem : c.support.card ∈ σ.cycleType := by
    have hle := Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset hc
    apply Multiset.mem_of_le hle
    rw [hcCycle.cycleType]
    simp
  have hcard : c.support.card = 3 :=
    (Equiv.Perm.pow_prime_eq_one_iff.mp hσ3) _ hcardMem
  exact card_support_eq_three_iff.mp hcard

/-- Every order-three element of an alternating group has an order-three lift
through a finite central extension with 3-primary kernel. -/
public theorem exists_order_three_lift
    {H : Type*} [Group H] [Finite H]
    (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (a : alternatingGroup (Fin (n + 5)))
    (ha : orderOf a = 3) :
    ∃ y : H, f y = a ∧ orderOf y = 3 := by
  let σ : Equiv.Perm (Fin (n + 5)) := a
  have hσ3 : σ ^ 3 = 1 := by
    have ha3 : a ^ 3 = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one a
    simpa [σ] using congrArg Subtype.val ha3
  obtain ⟨l, hlNodup, hlEq⟩ := σ.cycleFactorsFinset.exists_list_nodup_eq
  have hlData :=
    (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hlNodup).mp hlEq.symm
  have hlThree : ∀ c ∈ l, Equiv.Perm.IsThreeCycle c := by
    intro c hc
    apply __ch5_OrderThreeLift_isThreeCycle_of_mem_cycleFactors_of_cube_eq_one σ hσ3
    rw [← hlEq]
    simpa using hc
  have hlComm : l.Pairwise Commute :=
    hlData.2.1.imp Equiv.Perm.Disjoint.commute
  obtain ⟨y, hfyPerm, hy3⟩ :=
    __ch5_OrderThreeLift_exists_list_threeCycle_lift_cube_eq_one
      n f hf hker hker3 l hlThree hlComm
  have hfy : f y = a := by
    apply Subtype.ext
    exact hfyPerm.trans hlData.2.2
  have ha1 : a ≠ 1 := by
    intro haOne
    rw [haOne, orderOf_one] at ha
    omega
  have hy1 : y ≠ 1 := by
    intro hyOne
    subst y
    apply ha1
    simpa using hfy.symm
  exact ⟨y, hfy, orderOf_eq_prime hy3 hy1⟩

/-- Degree-normalized form of `exists_order_three_lift`, for an independently
named alternating degree at least five. -/
public theorem exists_order_three_lift_of_five_le
    {H : Type*} [Group H] [Finite H]
    (m : Nat) (hm : 5 ≤ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (a : alternatingGroup (Fin m))
    (ha : orderOf a = 3) :
    ∃ y : H, f y = a ∧ orderOf y = 3 := by
  let q := m - 5
  let e : Fin (q + 5) ≃ Fin m := finCongr (Nat.sub_add_cancel hm)
  let eA := e.symm.altCongrHom
  let f' : H →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f
  let a' : alternatingGroup (Fin (q + 5)) := eA a
  have hf'ker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f eA.toMonoidHom eA.injective
  have hf'surj : Function.Surjective f' := eA.surjective.comp hf
  have hf'center : f'.ker ≤ Subgroup.center H := by
    rw [hf'ker]
    exact hker
  have hf'3 : IsPGroup 3 f'.ker := by
    rw [hf'ker]
    exact hker3
  have ha' : orderOf a' = 3 := by
    exact (orderOf_injective eA.toMonoidHom eA.injective a).trans ha
  obtain ⟨y, hfy, hy⟩ :=
    exists_order_three_lift q f' hf'surj hf'center hf'3 a' ha'
  refine ⟨y, ?_, hy⟩
  apply eA.injective
  exact hfy

end GLS3.Chapter5.SchurPresentation
/- END Theory.OrderThreeLift -/

/- BEGIN Theory.ThreeReduction -/
noncomputable section

/- Source: ThreeCycleInvariantReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Relabeling a three-point invariant subset

An arbitrary three-element subset and its complement give an equivalence from
the standard `3 + (q+5)` decomposition to the ambient degree `((q+3)+5)`.
Conjugating the alternating action by the resulting ambient relabeling reduces
its preservation to the standard three-point block endpoint.
-/

/-- A relabeling from the standard `3 + (q+5)` decomposition whose first
block has image exactly `S`. -/
public noncomputable def threeBlockRelabelingEquiv
    (q : Nat) (S : Set (Fin ((q + 3) + 5)))
    (hS : Nat.card S = 3)
    (hSc : Nat.card (Sᶜ : Set (Fin ((q + 3) + 5))) = q + 5) :
    Fin (3 + (q + 5)) ≃ Fin ((q + 3) + 5) := by
  classical
  let eS : Fin 3 ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin (q + 5) ≃ (Sᶜ : Set (Fin ((q + 3) + 5))) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  exact finSumFinEquiv.symm.trans
    ((eS.sumCongr eSc).trans (Equiv.Set.sumCompl S))

/-- The relabeling constructed from `S` sends the standard first block to
`S`. -/
public theorem image_finFirstBlock_threeBlockRelabelingEquiv
    (q : Nat) (S : Set (Fin ((q + 3) + 5)))
    (hS : Nat.card S = 3)
    (hSc : Nat.card (Sᶜ : Set (Fin ((q + 3) + 5))) = q + 5) :
    threeBlockRelabelingEquiv q S hS hSc '' finFirstBlock 3 (q + 5) = S := by
  classical
  let eS : Fin 3 ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin (q + 5) ≃ (Sᶜ : Set (Fin ((q + 3) + 5))) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    simp [threeBlockRelabelingEquiv]
  · intro hx
    obtain ⟨i, hi⟩ := eS.surjective ⟨x, hx⟩
    refine ⟨Fin.castAdd (q + 5) i, ⟨i, rfl⟩, ?_⟩
    simpa [threeBlockRelabelingEquiv, eS, eSc] using congrArg Subtype.val hi

/-- A nontrivial central 3-kernel prevents a Sylow image from preserving an
arbitrary three-element subset, provided the complementary alternating
factor's multiplier has no 3-part. -/
public theorem not_sylow_image_mapsTo_three_subset_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3ker : 3 ∣ Nat.card f.ker)
    (h3M : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker)
    (P : Sylow 3 H)
    (S : Set (Fin ((q + 3) + 5)))
    (hS : Nat.card S = 3)
    (hSc : Nat.card (Sᶜ : Set (Fin ((q + 3) + 5))) = q + 5) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((q + 3) + 5) → Fin ((q + 3) + 5)) S S := by
  intro hmaps
  let eS := threeBlockRelabelingEquiv q S hS hSc
  let e0 : Fin (3 + (q + 5)) ≃ Fin ((q + 3) + 5) := finCongr (by omega)
  let u : Fin ((q + 3) + 5) ≃ Fin ((q + 3) + 5) := eS.symm.trans e0
  let uA := u.altCongrHom
  let f' : H →* alternatingGroup (Fin ((q + 3) + 5)) :=
    uA.toMonoidHom.comp f
  have hf'ker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f uA.toMonoidHom uA.injective
  have hf'surj : Function.Surjective f' := uA.surjective.comp hf
  have hf'center : f'.ker ≤ Subgroup.center H := by
    rw [hf'ker]
    exact hker
  have hf'3 : IsPGroup 3 f'.ker := by
    rw [hf'ker]
    exact hker3
  have h3ker' : 3 ∣ Nat.card f'.ker := by
    rw [hf'ker]
    exact h3ker
  have hu : u '' S = threeBlockFirstBlock q := by
    rw [← image_finFirstBlock_threeBlockRelabelingEquiv q S hS hSc]
    change u '' (eS '' finFirstBlock 3 (q + 5)) =
      e0 '' finFirstBlock 3 (q + 5)
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [u]⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨eS y, ⟨y, hy, rfl⟩, ?_⟩
      simp [u]
  apply not_sylow_image_mapsTo_threeBlockFirstBlock_of_not_dvd_multiplier
    q f' hf'surj hf'center hf'3 h3ker' h3M P
  intro x y hy
  rw [← hu] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := hy
  change u ((f (x : H) : Equiv.Perm _) (u.symm (u z))) ∈ u '' S
  rw [u.symm_apply_apply]
  exact ⟨_, hmaps x hz, rfl⟩

end GLS3.Chapter5.SchurPresentation

/- Source: ThreeOrbitReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- A Sylow 3-action preserving a six-element set also preserves a
three-element subset. If no orbit inside the six-set has size three, every
point of the set is fixed and any three chosen points work. -/
public theorem exists_invariant_three_subset_of_invariant_six_subset
    (m : Nat)
    (Q : Sylow 3 (alternatingGroup (Fin m)))
    (S : Set (Fin m))
    (hS : Nat.card S = 6)
    (hmaps : ∀ q : Q, Set.MapsTo
      ((q : alternatingGroup (Fin m)) : Fin m → Fin m) S S) :
    ∃ T : Set (Fin m),
      Nat.card T = 3 ∧ T ⊆ S ∧
        ∀ q : Q, Set.MapsTo
          ((q : alternatingGroup (Fin m)) : Fin m → Fin m) T T := by
  classical
  by_cases horbit : ∃ y : Fin m, y ∈ S ∧ Nat.card (MulAction.orbit Q y) = 3
  · obtain ⟨y, hyS, hycard⟩ := horbit
    refine ⟨MulAction.orbit Q y, hycard, ?_, ?_⟩
    · intro z hz
      obtain ⟨q, rfl⟩ := MulAction.mem_orbit_iff.mp hz
      exact hmaps q hyS
    · intro q
      exact MulAction.mapsTo_smul_orbit q y
  · have hfixed : ∀ y : Fin m, y ∈ S →
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
      have hrlt : r < 2 := by
        by_contra hrnot
        have hpow : 3 ^ 2 ≤ 3 ^ r :=
          pow_le_pow_right₀ (by omega : 1 ≤ 3) (by omega)
        rw [← hr] at hpow
        omega
      have hrCases : r = 0 ∨ r = 1 := by omega
      rcases hrCases with rfl | rfl
      · simpa only [Nat.card_eq_fintype_card, pow_zero] using hr
      · exfalso
        apply horbit
        exact ⟨y, hyS, by simpa only [pow_one] using hr⟩
    let eS : Fin 6 ≃ S :=
      (Fintype.equivFinOfCardEq (by
        simpa [Nat.card_eq_fintype_card] using hS)).symm
    let j : Fin 3 → Fin m := fun i =>
      (eS (Fin.castLE (by omega : 3 ≤ 6) i) : S)
    have hj : Function.Injective j := by
      intro i k hik
      apply Fin.castLE_injective (by omega : 3 ≤ 6)
      apply eS.injective
      exact Subtype.ext hik
    let T : Set (Fin m) := Set.range j
    refine ⟨T, ?_, ?_, ?_⟩
    · simp only [T, Nat.card_coe_set_eq, Set.ncard_range_of_injective hj]
      exact Nat.card_fin 3
    · rintro x ⟨i, rfl⟩
      exact (eS (Fin.castLE (by omega : 3 ≤ 6) i)).2
    · intro q x hx
      obtain ⟨i, rfl⟩ := hx
      have hfix := MulAction.mem_fixedPoints.mp
        (hfixed (j i) (eS (Fin.castLE (by omega : 3 ≤ 6) i)).2) q
      change q • j i ∈ T
      rw [hfix]
      exact ⟨i, rfl⟩

/-- Total-degree wrapper for the invariant three-subset exclusion. -/
public theorem not_sylow_image_mapsTo_three_subset_of_total_eq
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m q : Nat) (hm : m = (q + 3) + 5)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3ker : 3 ∣ Nat.card f.ker)
    (h3M : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker)
    (P : Sylow 3 H)
    (S : Set (Fin m))
    (hS : Nat.card S = 3)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = q + 5) :
    ¬ ∀ x : P, Set.MapsTo (f (x : H) : Fin m → Fin m) S S := by
  subst m
  exact not_sylow_image_mapsTo_three_subset_of_not_dvd_multiplier
    q f hf hker hker3 h3ker h3M P S hS hSc

/-- In degree at least twelve, a nontransitive Sylow-3 image is excluded
by the inductive absence of 3-parts in all smaller nonexceptional alternating
multipliers. -/
public theorem false_of_not_pretransitive_sylow_image_three_of_inductive_not_dvd
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (m : Nat) (hm12 : 12 ≤ m) (h3deg : 3 ∣ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3ker : 3 ∣ Nat.card f.ker)
    (P : Sylow 3 H)
    (hnotTrans : ¬ MulAction.IsPretransitive
      (P.mapSurjective hf) (Fin m))
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m → d ≠ 6 → d ≠ 7 →
      ¬ 3 ∣ Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker) :
    False := by
  let Q : Sylow 3 (alternatingGroup (Fin m)) := P.mapSurjective hf
  have h3Base : 3 ∣ Nat.card (alternatingGroup (Fin m)) :=
    prime_dvd_card_of_dvd_card_ker f hf hker h3ker
  have hQne : (Q : Subgroup (alternatingGroup (Fin m))) ≠ ⊥ :=
    Q.ne_bot_of_dvd_card h3Base
  obtain ⟨q, hqQ, hq1⟩ : ∃ q : alternatingGroup (Fin m),
      q ∈ (Q : Subgroup (alternatingGroup (Fin m))) ∧ q ≠ 1 := by
    by_contra h
    push Not at h
    apply hQne
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact h q hq
  let qQ : Q := ⟨q, hqQ⟩
  obtain ⟨y, hqy⟩ : ∃ y : Fin m, qQ • y ≠ y := by
    by_contra h
    push Not at h
    apply hq1
    apply Subtype.ext
    ext y
    have hy := h y
    change (q : Equiv.Perm (Fin m)) y = y at hy
    exact congrArg Fin.val hy
  have hproper : MulAction.orbit Q y ≠ Set.univ := by
    intro htop
    exact hnotTrans
      ((MulAction.isPretransitive_iff_orbit_eq_univ y).mpr htop)
  let S : Set (Fin m) := MulAction.orbit Q y
  let a := Nat.card S
  let b := Nat.card (Sᶜ : Set (Fin m))
  let : Fintype (MulAction.orbit Q y) := Fintype.ofFinite _
  have hsum : m = a + b := by
    have h := Set.ncard_add_ncard_compl S
    simpa [a, b, Nat.card_fin, add_comm] using h.symm
  have hmapsS : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S := by
    intro x
    let qx : Q := ⟨f (x : H), ⟨x, x.2, rfl⟩⟩
    exact MulAction.mapsTo_smul_orbit qx y
  have hmapsSc : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) Sᶜ Sᶜ := by
    intro x z hz
    rw [Set.mem_compl_iff] at hz ⊢
    intro hfzS
    have hback := hmapsS (x⁻¹) hfzS
    apply hz
    simpa using hback
  have hyNotFixed : y ∉ MulAction.fixedPoints Q (Fin m) := by
    intro hy
    exact hqy (MulAction.mem_fixedPoints.mp hy qQ)
  have ha1 : a ≠ 1 := by
    intro ha
    apply hyNotFixed
    rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
    simpa [a, S, Nat.card_eq_fintype_card] using ha
  obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
  have hra : a = 3 ^ r := by
    simpa [a, S] using hr
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    apply ha1
    simpa only [pow_zero] using hra
  have h3a : 3 ∣ a := by
    rw [hra]
    exact dvd_pow_self 3 hr0
  have haPos : 0 < a := by
    exact (show S.Nonempty from ⟨y, MulAction.mem_orbit_self y⟩).ncard_pos
  have h3b : 3 ∣ b := by
    have : 3 ∣ a + b := by
      rw [← hsum]
      exact h3deg
    exact (Nat.dvd_add_iff_right h3a).mpr this
  have hScNonempty : (Sᶜ : Set (Fin m)).Nonempty := by
    apply Set.ssubset_univ_iff_nonempty_compl.mp
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, hproper⟩
  have hbPos : 0 < b := hScNonempty.ncard_pos
  have haLt : a < m := by omega
  have hbLt : b < m := by omega
  let qRest := m - 8
  have hmRest : m = (qRest + 3) + 5 := by
    dsimp [qRest]
    omega
  have hrestDegree : qRest + 5 = m - 3 := by
    dsimp [qRest]
    omega
  have h3MRest : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering qRest).toMonoidHom.ker := by
    have h := hsmall (m - 3) (by omega) (by omega) (by omega) (by omega)
    have hq : (m - 3) - 5 = qRest := by
      dsimp [qRest]
      omega
    rw [hq] at h
    exact h
  by_cases ha3 : a = 3
  · apply not_sylow_image_mapsTo_three_subset_of_total_eq
      m qRest hmRest f hf hker hker3 h3ker h3MRest P S ha3
    · rw [hrestDegree]
      omega
    · exact hmapsS
  by_cases hb3 : b = 3
  · apply not_sylow_image_mapsTo_three_subset_of_total_eq
      m qRest hmRest f hf hker hker3 h3ker h3MRest P Sᶜ hb3
    · rw [hrestDegree]
      simpa only [compl_compl] using
        (show Nat.card S = m - 3 by omega)
    · exact hmapsSc
  by_cases hb6 : b = 6
  · obtain ⟨T, hT3, hTS, hmapsTQ⟩ :=
      exists_invariant_three_subset_of_invariant_six_subset
        m Q Sᶜ hb6 (by
          intro q z hz
          obtain ⟨x, hxP, hx⟩ := q.2
          have hz' := hmapsSc ⟨x, hxP⟩ hz
          change ((q : alternatingGroup (Fin m)) : Fin m → Fin m) z ∈ Sᶜ
          rw [← hx]
          exact hz')
    have hmapsT : ∀ x : P,
        Set.MapsTo (f (x : H) : Fin m → Fin m) T T := by
      intro x
      let qx : Q := ⟨f (x : H), ⟨x, x.2, rfl⟩⟩
      exact hmapsTQ qx
    apply not_sylow_image_mapsTo_three_subset_of_total_eq
      m qRest hmRest f hf hker hker3 h3ker h3MRest P T hT3
    · rw [hrestDegree]
      have hcard := Set.ncard_add_ncard_compl T
      have hT3' : T.ncard = 3 := by
        simpa only [Nat.card_coe_set_eq] using hT3
      rw [hT3', Nat.card_fin] at hcard
      simpa only [Nat.card_coe_set_eq] using (show Tᶜ.ncard = m - 3 by omega)
    · exact hmapsT
  have ha9 : 9 ≤ a := by
    have hr1 : r ≠ 1 := by
      intro hrone
      apply ha3
      rw [hra, hrone, pow_one]
    have hr2 : 2 ≤ r := by omega
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ r := pow_le_pow_right₀ (by omega : 1 ≤ 3) hr2
      _ = a := hra.symm
  have hb9 : 9 ≤ b := by
    obtain ⟨k, hk⟩ := h3b
    have hkPos : 0 < k := by omega
    have hk3 : 3 ≤ k := by
      by_contra hknot
      have hkCases : k = 1 ∨ k = 2 := by omega
      rcases hkCases with rfl | rfl
      · exact hb3 (by omega)
      · exact hb6 (by omega)
    omega
  have h3MA := hsmall a (by omega) haLt (by omega) (by omega)
  have h3MB := hsmall b (by omega) hbLt (by omega) (by omega)
  apply not_sylow_image_mapsTo_subset_of_total_eq_of_five_le_of_not_dvd_multipliers
    (p := 3) (by decide) m a b hsum (by omega) (by omega)
    f hf hker hker3 h3ker h3MA h3MB P S rfl rfl
  exact hmapsS

end GLS3.Chapter5.SchurPresentation

/- Source: ThreeDegreeEight.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- The universal central covering of `A₈` has kernel order not divisible by
three. A nontrivial Sylow-3 image has a moved orbit of size exactly three, so
the three-block exclusion reduces the complementary factor to `A₅`. -/
public theorem not_dvd_natCard_ker_alternatingFreeCentralCovering_three_degree_eight :
    ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering 3).toMonoidHom.ker := by
  intro h3M
  let f := alternatingFreeCentralCovering 3
  obtain ⟨X, hX, fbar, _hXker, hbarSurj, hbarCenter, hbarP, h3bar⟩ :=
    exists_pPrimary_quotient_central_extension
      f.toMonoidHom f.surjective f.ker_le_center h3M
  let : X.Normal := hX
  let P : Sylow 3 (AlternatingFreeCentralDerived 3 ⧸ X) := default
  let Q : Sylow 3 (alternatingGroup (Fin (3 + 5))) :=
    P.mapSurjective hbarSurj
  have h3Base : 3 ∣ Nat.card (alternatingGroup (Fin (3 + 5))) :=
    prime_dvd_card_of_dvd_card_ker fbar hbarSurj hbarCenter h3bar
  have hQne : (Q : Subgroup (alternatingGroup (Fin (3 + 5)))) ≠ ⊥ :=
    Q.ne_bot_of_dvd_card h3Base
  obtain ⟨q, hqQ, hq1⟩ : ∃ q : alternatingGroup (Fin (3 + 5)),
      q ∈ (Q : Subgroup (alternatingGroup (Fin (3 + 5)))) ∧ q ≠ 1 := by
    by_contra h
    push Not at h
    apply hQne
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact h q hq
  let qQ : Q := ⟨q, hqQ⟩
  obtain ⟨y, hqy⟩ : ∃ y : Fin (3 + 5), qQ • y ≠ y := by
    by_contra h
    push Not at h
    apply hq1
    apply Subtype.ext
    ext y
    have hy := h y
    change (q : Equiv.Perm (Fin (3 + 5))) y = y at hy
    exact congrArg Fin.val hy
  let : Fintype (MulAction.orbit Q y) := Fintype.ofFinite _
  have hyNotFixed : y ∉ MulAction.fixedPoints Q (Fin (3 + 5)) := by
    intro hy
    exact hqy (MulAction.mem_fixedPoints.mp hy qQ)
  have horbitNeOne : Nat.card (MulAction.orbit Q y) ≠ 1 := by
    intro hcard
    apply hyNotFixed
    rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
    simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
  have hle : Nat.card (MulAction.orbit Q y) ≤ 8 := by
    rw [Nat.card_coe_set_eq]
    simpa using Set.ncard_le_ncard
      (show MulAction.orbit Q y ⊆ (Set.univ : Set (Fin (3 + 5))) from
        Set.subset_univ _)
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    apply horbitNeOne
    simpa only [pow_zero] using hr
  have hrlt2 : r < 2 := by
    by_contra hrnot
    have hpow : 3 ^ 2 ≤ 3 ^ r :=
      pow_le_pow_right₀ (by omega : 1 ≤ 3) (by omega)
    rw [← hr] at hpow
    omega
  have hr1 : r = 1 := by omega
  have horbit3 : Nat.card (MulAction.orbit Q y) = 3 := by
    rw [hr, hr1, pow_one]
  let S : Set (Fin (3 + 5)) := MulAction.orbit Q y
  have hScard : Nat.card S = 3 := by
    exact horbit3
  have hSccard : Nat.card (Sᶜ : Set (Fin (3 + 5))) = 5 := by
    have hcard : S.ncard + Sᶜ.ncard = 8 := by
      simpa using Set.ncard_add_ncard_compl S
    have hS3 : S.ncard = 3 := by
      simpa only [Nat.card_coe_set_eq] using hScard
    rw [hS3] at hcard
    simpa only [Nat.card_coe_set_eq] using
      (show Sᶜ.ncard = 5 by omega)
  have h3M0 : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering 0).toMonoidHom.ker := by
    rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two]
    all_goals decide
  apply not_sylow_image_mapsTo_three_subset_of_not_dvd_multiplier
    0 fbar hbarSurj hbarCenter hbarP h3bar h3M0 P S hScard hSccard
  intro x
  let qx : Q := ⟨fbar (x : AlternatingFreeCentralDerived 3 ⧸ X),
    ⟨x, x.2, rfl⟩⟩
  exact MulAction.mapsTo_smul_orbit qx y

end GLS3.Chapter5.SchurPresentation
/- END Theory.ThreeReduction -/

/- BEGIN Theory.InvolutionCycleAlternatingEmbeddingEquivInjective -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionCycleAlternatingEmbeddingEquivInjective_u __ch5_InvolutionCycleAlternatingEmbeddingEquivInjective_v

/-- The natural alternating cycle embedding remains injective after an
arbitrary finite reindexing of the cycle factors. -/
public theorem involutionCycleAlternatingEmbedding_comp_altCongr_injective
    {Ω : Type __ch5_InvolutionCycleAlternatingEmbeddingEquivInjective_u} [Fintype Ω] [DecidableEq Ω]
    {ι : Type __ch5_InvolutionCycleAlternatingEmbeddingEquivInjective_v} [Fintype ι] [DecidableEq ι]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (e : x.cycleFactorsFinset ≃ ι) :
    Function.Injective
      ((involutionCycleAlternatingEmbedding x hx).comp
        e.altCongrHom.symm.toMonoidHom) := by
  let cycleEquiv := theorem_5_2_2_d_3_a x
    (by simpa [hx] using Nat.prime_two)
  have hbase : Function.Injective
      (involutionCycleAlternatingEmbedding x hx) := by
    intro a b hab
    have hval := congrArg (fun z : alternatingGroup Ω => z.1) hab
    have hl : cycleEquiv.symm a.1 = cycleEquiv.symm b.1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [involutionCycleAlternatingEmbedding, cycleEquiv] using hval
    apply Subtype.ext
    exact cycleEquiv.symm.injective hl
  exact hbase.comp e.altCongrHom.symm.injective

end GLS3.Chapter5
/- END Theory.InvolutionCycleAlternatingEmbeddingEquivInjective -/

/- BEGIN Theory.InvolutionCycleAlternatingRootSupportEight -/
noncomputable section

namespace GLS3.Chapter5

open SchurPresentation.RootFourSubgroup
universe __ch5_InvolutionCycleAlternatingRootSupportEight_u

/-- The standard root involution in the reindexed alternating cycle factor
moves eight points in the original involution action. -/
public theorem involutionCycleAlternatingEmbeddingFin_root_support_card
    {Ω : Type __ch5_InvolutionCycleAlternatingRootSupportEight_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (q : Nat)
    (eFin : x.cycleFactorsFinset ≃ Fin (q + 5)) :
    ((involutionCycleAlternatingEmbeddingFin x hx q eFin)
      (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5)))).1.support.card = 8 := by
  change ((theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)).symm
    ((eFin.altCongrHom.symm
      (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5)))).1)).1.1.support.card = 8
  have harg :
      ((eFin.altCongrHom.symm
        (⟨rho1 q, rho1_mem_alternating q⟩ :
          alternatingGroup (Fin (q + 5)))).1) =
        eFin.symm.permCongr (rho1 q) := rfl
  rw [harg]
  exact involutionCyclePermutation_root_support_card x hx q eFin

end GLS3.Chapter5
/- END Theory.InvolutionCycleAlternatingRootSupportEight -/

/- BEGIN Theory.FixedPointPermutationSignKernelSupport -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_FixedPointPermutationSignKernelSupport_u

public theorem fixedPointPermutationSignKernelEquiv_support_card
    {Ω : Type __ch5_FixedPointPermutationSignKernelSupport_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (z : let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω));
      let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype;
      let Z := χ.ker;
      (fixedPointPermutationSubgroup x).comap Z.subtype) :
    (fixedPointPermutationSignKernelEquiv x z).1.support.card =
      z.1.1.1.support.card := by
  let i : fixedPointPermutationSubgroup x := ⟨z.1.1, z.2⟩
  let __ch5_FixedPointPermutationSignKernelSupport_u : Equiv.Perm (Function.fixedPoints x) :=
    (theorem_5_2_2_d_4 x) i
  have hi : i = (fixedPointPermMulEquivSubgroup x) __ch5_FixedPointPermutationSignKernelSupport_u := by
    apply (theorem_5_2_2_d_4 x).injective
    simp [__ch5_FixedPointPermutationSignKernelSupport_u, theorem_5_2_2_d_4]
  have hcoe : i.1.1 = Equiv.Perm.ofSubtype __ch5_FixedPointPermutationSignKernelSupport_u := by
    rw [hi]
    exact fixedPointPermToCentralizer_coe x __ch5_FixedPointPermutationSignKernelSupport_u
  change __ch5_FixedPointPermutationSignKernelSupport_u.support.card = i.1.1.support.card
  rw [hcoe, Equiv.Perm.support_ofSubtype, Finset.card_map]

end GLS3.Chapter5
/- END Theory.FixedPointPermutationSignKernelSupport -/

/- BEGIN Theory.InvolutionRotationSignKernelEquivTraceZero -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionRotationSignKernelEquivTraceZero_u

/-- After numbering an involution's nontrivial cycles, the rotation part of
the even centralizer is the multiplicative trace-zero module. -/
@[expose]
public noncomputable def involutionRotationSignKernelEquivTraceZero
    {Ω : Type __ch5_InvolutionRotationSignKernelEquivTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    (cycleRotationSubgroup x).comap Z.subtype ≃*
      Multiplicative ↥(traceZeroTwoSubgroup r) := by
  dsimp only
  exact (evenCycleRotationsSignKernelEquiv x).trans
    (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e)

@[simp]
public theorem involutionRotationSignKernelEquivTraceZero_apply
    {Ω : Type __ch5_InvolutionRotationSignKernelEquivTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r)
    (z : (cycleRotationSubgroup x).comap
      (Equiv.Perm.sign.comp
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker.subtype) :
    involutionRotationSignKernelEquivTraceZero x hx r e z =
      evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e
        (evenCycleRotationsSignKernelEquiv x z) := rfl

end GLS3.Chapter5
/- END Theory.InvolutionRotationSignKernelEquivTraceZero -/

/- BEGIN Theory.ThreeImprimitive -/
noncomputable section

/- Source: ThreePowerSemidirectExtension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Three-fold alternating-power semidirect extensions

For the imprimitive `p=3` branch, the base is a three-fold direct power of a
perfect alternating group, while the top factor is the cyclic group `A_3`.
The base multiplier hypothesis supplies its section.  Once an explicit top
section is provided, the generic semidirect compatibility theorem combines
the two sections.
-/

set_option backward.isDefEq.respectTransparency false in
/-- A central extension of `(A_(q+5))^3 ⋊ A_3` splits when its base direct
power splits and a section of the top `A_3` factor has been supplied. -/
public theorem
    exists_threePowerSemidirect_section_isComplement'_of_top_section
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (q : Nat)
    (φ : alternatingGroup (Fin 3) →*
      MulAut (Fin 3 → alternatingGroup (Fin (q + 5))))
    (f : H →* (Fin 3 → alternatingGroup (Fin (q + 5))) ⋊[φ]
      alternatingGroup (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpBase : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker)
    (sA : alternatingGroup (Fin 3) →* H)
    (hsA : f.comp sA = SemidirectProduct.inr) :
    ∃ s, f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  let N := Fin 3 → alternatingGroup (Fin (q + 5))
  let EB := semidirectBasePreimage φ f
  let rB := semidirectBasePreimageProjection φ f
  have hrBsurj : Function.Surjective rB :=
    semidirectBasePreimageProjection_surjective φ f hf
  have hrBker : rB.ker ≤ Subgroup.center EB :=
    semidirectBasePreimageProjection_ker_le_center φ f hker
  have hrBp : IsPGroup p rB.ker := by
    rw [semidirectBasePreimageProjection_ker_eq_comap]
    exact hkerp.comap_subtype
  obtain ⟨tB, htB, _⟩ :=
    exists_directPower_section_isComplement'_of_not_dvd_multiplier
      q 3 rB hrBsurj hrBker hrBp hpBase
  let sN : N →* H := EB.subtype.comp tB
  have hsN : f.comp sN = SemidirectProduct.inl := by
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext
    · have hx := DFunLike.congr_fun htB x
      change rB (tB x) = x at hx
      exact hx
    · exact MonoidHom.mem_ker.mp (tB x).2
  let : Group.IsPerfect (alternatingGroup (Fin (q + 5))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N := {
    commutator_eq_top := by
      change ⁅(⊤ : Subgroup N), ⊤⁆ = ⊤
      rw [← Subgroup.pi_top
        (f := fun _ : Fin 3 => alternatingGroup (Fin (q + 5))) Set.univ]
      rw [Subgroup.commutator_pi_pi_of_finite]
      congr 1
      funext i
      exact Group.IsPerfect.commutator_eq_top }
  exact exists_semidirectProduct_section_isComplement'_of_component_sections
    φ f hker sN sA hsN hsA

end GLS3.Chapter5.SchurPresentation

/- Source: ThreeImprimitiveSubextension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## The three-block imprimitive subextension

The base `(A_d)^3` splits by the inductive multiplier hypothesis.  The top
`A_3` generator maps to an order-three element of the ambient alternating
group, so `exists_order_three_lift_of_five_le` supplies an order-three lift.
This gives the top section needed by the generic semidirect splitting theorem.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The restricted central extension over the standard
`(A_(q+5))^3 ⋊ A_3` subgroup splits when the base alternating multiplier has
no 3-part. -/
public theorem
    exists_alternatingThreeImprimitivePreimage_section_isComplement'
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin (3 * (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3Base : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    ∃ s : alternatingImprimitiveGroup 3 (q + 5) →*
        alternatingImprimitivePreimage 3 (q + 5) f,
      (alternatingImprimitivePreimageProjection 3 (q + 5) f).comp s =
        MonoidHom.id _ ∧
      (alternatingImprimitivePreimageProjection 3 (q + 5) f).ker.IsComplement'
        s.range := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let E := alternatingImprimitivePreimage 3 (q + 5) f
  let r := alternatingImprimitivePreimageProjection 3 (q + 5) f
  let i := alternatingImprimitiveFinHom 3 (q + 5)
  have hrSurj : Function.Surjective r :=
    alternatingImprimitivePreimageProjection_surjective 3 (q + 5) f hf
  have hrCenter : r.ker ≤ Subgroup.center E :=
    alternatingImprimitivePreimageProjection_ker_le_center 3 (q + 5) f hker
  have hr3 : IsPGroup 3 r.ker := by
    rw [alternatingImprimitivePreimageProjection_ker_eq_comap]
    exact hker3.comap_subtype
  let g : alternatingGroup (Fin 3) := a3Generator
  let top : alternatingImprimitiveGroup 3 (q + 5) :=
    SemidirectProduct.inr g
  have hinr : Function.Injective
      (SemidirectProduct.inr : alternatingGroup (Fin 3) →*
        alternatingImprimitiveGroup 3 (q + 5)) := by
    intro a b hab
    exact congrArg SemidirectProduct.right hab
  have htop : orderOf top = 3 :=
    (orderOf_injective
      (SemidirectProduct.inr : alternatingGroup (Fin 3) →*
        alternatingImprimitiveGroup 3 (q + 5)) hinr g).trans
      a3Generator_orderOf
  let a : alternatingGroup (Fin (3 * (q + 5))) := i top
  have ha : orderOf a = 3 :=
    (orderOf_injective i (alternatingImprimitiveFinHom_injective 3 (q + 5))
      top).trans htop
  obtain ⟨y, hfy, hordy⟩ := exists_order_three_lift_of_five_le
    (3 * (q + 5)) (by omega) f hf hker hker3 a ha
  have hyE : y ∈ E := by
    change f y ∈ i.range
    exact ⟨top, hfy.symm⟩
  let yE : E := ⟨y, hyE⟩
  have hordyE : orderOf yE = 3 :=
    (Subgroup.orderOf_coe yE).symm.trans hordy
  obtain ⟨tA, htAg⟩ := exists_cyclic_section_of_order_three
    g a3_card a3Generator_orderOf yE hordyE
  have hryE : r yE = top := by
    let e := MonoidHom.ofInjective
      (alternatingImprimitiveFinHom_injective 3 (q + 5))
    change e.symm ⟨f y, hyE⟩ = top
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hfy
  have htA : r.comp tA =
      (SemidirectProduct.inr : alternatingGroup (Fin 3) →*
        alternatingImprimitiveGroup 3 (q + 5)) := by
    apply MonoidHom.ext
    intro x
    have hx : x ∈ Subgroup.zpowers g := by
      change x ∈ Subgroup.zpowers a3Generator
      rw [a3Generator_zpowers_eq_top]
      trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk, map_zpow, map_zpow]
    simp only [MonoidHom.comp_apply]
    rw [htAg, hryE]
  exact exists_threePowerSemidirect_section_isComplement'_of_top_section
    q (alternatingBlockAction 3 (q + 5)) r hrSurj hrCenter hr3 h3Base tA htA

end GLS3.Chapter5.SchurPresentation

/- Source: ThreeImprimitiveSylow.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Sylow 3-subgroups in the three-block imprimitive subgroup -/

/-- The 3-part of an alternating-group order is the 3-part of the
corresponding factorial. -/
public theorem alternating_card_factorization_eq_factorial_three
    (n : Nat) (hn : 2 ≤ n) :
    (Nat.card (alternatingGroup (Fin n))).factorization 3 =
      n.factorial.factorization 3 := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h3two : ¬ 3 ∣ 2 := by norm_num
  have h := congrArg (fun m : Nat => m.factorization 3)
    (two_mul_nat_card_alternatingGroup (α := Fin n))
  rw [Nat.factorization_mul (by decide) Nat.card_pos.ne'] at h
  simp only [Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h3two, zero_add,
    Nat.card_perm, Nat.card_fin] at h
  exact h

/-- For a positive exponent, the standard three-block imprimitive subgroup
and the ambient alternating group have the same 3-part. -/
public theorem alternatingThreeImprimitiveGroup_factorization_eq_ambient
    (s : Nat) (hs : 0 < s) :
    (Nat.card (alternatingImprimitiveGroup 3 (3 ^ s))).factorization 3 =
      (Nat.card (alternatingGroup (Fin (3 * 3 ^ s)))).factorization 3 := by
  have h3s : 3 ≤ 3 ^ s := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ 3) hs)
  have hd2 : 2 ≤ 3 ^ s := by omega
  have h3d2 : 2 ≤ 3 * 3 ^ s := by omega
  have h3fact : (3 : Nat).factorial.factorization 3 = 1 := by
    simpa using (Nat.factorization_factorial_mul (n := 1) (by decide : Nat.Prime 3))
  rw [alternatingImprimitiveGroup_card,
    Nat.factorization_mul (pow_ne_zero _ Nat.card_pos.ne') Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    alternating_card_factorization_eq_factorial_three (3 ^ s) hd2,
    alternating_card_factorization_eq_factorial_three 3 (by omega),
    alternating_card_factorization_eq_factorial_three (3 * 3 ^ s) h3d2,
    h3fact, Nat.factorization_factorial_mul (by decide : Nat.Prime 3)]
  exact factorial_power_factorization_relation 3 s (by decide)

/-- The standard `(A_(3^s))^3 ⋊ A_3` image contains an ambient Sylow
3-subgroup. -/
public theorem exists_sylow_three_le_alternatingImprimitiveFinHom_range
    (s : Nat) (hs : 0 < s) :
    ∃ P : Sylow 3 (alternatingGroup (Fin (3 * 3 ^ s))),
      (P : Subgroup (alternatingGroup (Fin (3 * 3 ^ s)))) ≤
        (alternatingImprimitiveFinHom 3 (3 ^ s)).range := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Nonempty (Fin (3 ^ s)) := ⟨⟨0, pow_pos (by omega) s⟩⟩
  let : Finite (alternatingImprimitiveGroup 3 (3 ^ s)) :=
    Finite.of_equiv
      ((Fin 3 → alternatingGroup (Fin (3 ^ s))) × alternatingGroup (Fin 3))
      (SemidirectProduct.equivProd
        (φ := alternatingBlockAction 3 (3 ^ s))).symm
  let Q : Sylow 3 (alternatingImprimitiveGroup 3 (3 ^ s)) :=
    Classical.choice Sylow.nonempty
  let K : Subgroup (alternatingGroup (Fin (3 * 3 ^ s))) :=
    (Q : Subgroup (alternatingImprimitiveGroup 3 (3 ^ s))).map
      (alternatingImprimitiveFinHom 3 (3 ^ s))
  have hinj : Function.Injective (alternatingImprimitiveFinHom 3 (3 ^ s)) :=
    alternatingImprimitiveFinHom_injective 3 (3 ^ s)
  have hKcard : Nat.card K =
      3 ^ (Nat.card (alternatingGroup (Fin (3 * 3 ^ s)))).factorization 3 := by
    change Nat.card ((Q : Subgroup (alternatingImprimitiveGroup 3 (3 ^ s))).map
      (alternatingImprimitiveFinHom 3 (3 ^ s))) = _
    rw [Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity Q,
      alternatingThreeImprimitiveGroup_factorization_eq_ambient s hs]
  let P : Sylow 3 (alternatingGroup (Fin (3 * 3 ^ s))) := Sylow.ofCard K hKcard
  refine ⟨P, ?_⟩
  change K ≤ (alternatingImprimitiveFinHom 3 (3 ^ s)).range
  exact Subgroup.map_le_range _ _

/-- Version with a separately named block degree. -/
public theorem exists_sylow_three_le_alternatingImprimitiveFinHom_range_of_eq_pow
    (d s : Nat) (hs : 0 < s) (hd : d = 3 ^ s) :
    ∃ P : Sylow 3 (alternatingGroup (Fin (3 * d))),
      (P : Subgroup (alternatingGroup (Fin (3 * d)))) ≤
        (alternatingImprimitiveFinHom 3 d).range := by
  subst d
  exact exists_sylow_three_le_alternatingImprimitiveFinHom_range s hs

end GLS3.Chapter5.SchurPresentation

/- Source: ThreeImprimitiveEndpoint.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## The transitive 3-power endpoint -/

/-- If the block degree is a positive power of three and its alternating
multiplier has no 3-part, the three-block imprimitive restriction splits and
the global central 3-kernel is trivial. -/
public theorem kernel_eq_bot_of_alternatingThreeImprimitive_primePower
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q s : Nat) (hs : 0 < s)
    (hpow : q + 5 = 3 ^ s)
    (f : H →* alternatingGroup (Fin (3 * (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3Base : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    f.ker = ⊥ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨S, hS⟩ :
      ∃ S : Sylow 3 (alternatingGroup (Fin (3 * (q + 5)))),
        (S : Subgroup _) ≤
          (alternatingImprimitiveFinHom 3 (q + 5)).range := by
    exact exists_sylow_three_le_alternatingImprimitiveFinHom_range_of_eq_pow
      (q + 5) s hs hpow
  have hSrange : (S : Subgroup _) ≤ f.range := by
    intro x hx
    exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
  let P : Sylow 3 H := S.comapOfKerIsPGroup f hker3 hSrange
  let E := alternatingImprimitivePreimage 3 (q + 5) f
  have hPE : (P : Subgroup H) ≤ E := by
    intro x hx
    change f x ∈ (alternatingImprimitiveFinHom 3 (q + 5)).range
    apply hS
    exact hx
  obtain ⟨t, -, hcomp⟩ :=
    exists_alternatingThreeImprimitivePreimage_section_isComplement'
      q f hf hker hker3 h3Base
  exact kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
    f hker hker3 P E hPE t.range (by
      rw [← alternatingImprimitivePreimageProjection_ker_eq_comap]
      exact hcomp)

/-- Relabeled form for an independently named ambient degree. -/
public theorem kernel_eq_bot_of_alternatingThreeImprimitive_primePower_degree
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q s m : Nat) (hs : 0 < s)
    (hpow : q + 5 = 3 ^ s)
    (hm : m = 3 * (q + 5))
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3Base : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    f.ker = ⊥ := by
  let e : Fin m ≃ Fin (3 * (q + 5)) := finCongr hm
  let f' : H →* alternatingGroup (Fin (3 * (q + 5))) :=
    e.altCongrHom.toMonoidHom.comp f
  have hfker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f e.altCongrHom.toMonoidHom
      e.altCongrHom.injective
  have hf'surj : Function.Surjective f' := e.altCongrHom.surjective.comp hf
  have hf'center : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hf'3 : IsPGroup 3 f'.ker := by
    rw [hfker]
    exact hker3
  have hbot := kernel_eq_bot_of_alternatingThreeImprimitive_primePower
    q s hs hpow f' hf'surj hf'center hf'3 h3Base
  rwa [hfker] at hbot

end GLS3.Chapter5.SchurPresentation
/- END Theory.ThreeImprimitive -/

/- BEGIN Theory.InvolutionOddRotationWitness -/
noncomputable section

open scoped BigOperators

namespace GLS3.Chapter5
universe __ch5_InvolutionOddRotationWitness_u

/-- Every nontrivial involution has an odd order-two element in its independent
cycle-rotation subgroup. -/
public theorem exists_odd_involution_mem_cycleRotationSubgroup
    {Ω : Type __ch5_InvolutionOddRotationWitness_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    ∃ r0 : C, r0 ∈ cycleRotationSubgroup x ∧ χ r0 = -1 ∧ r0 ^ 2 = 1 := by
  dsimp only
  have hxprime : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hcycles : x.cycleFactorsFinset.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hxne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp h)
  obtain ⟨c, hc⟩ := hcycles
  let c0 : x.cycleFactorsFinset := ⟨c, hc⟩
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) := fun d =>
    if d = c0 then Multiplicative.ofAdd 1 else 1
  let a : CycleRotationGroup x := E.symm v
  let r0 := cycleRotationToCentralizer x a
  have haCoord : E a = v := E.apply_symm_apply v
  have hr0χ : Equiv.Perm.sign r0.1 = -1 := by
    rw [involutionCycleRotation_sign x hx a]
    rw [show (∑ d, Multiplicative.toAdd (E a d)) = 1 by
      rw [haCoord]
      classical
      rw [Fintype.sum_eq_single c0]
      · simp [v]
      · intro d hne
        simp [v, hne]]
    norm_num
  have ha2 : a ^ 2 = 1 := by
    simpa [hx] using
      cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hxprime a
  refine ⟨r0, ⟨a, rfl⟩, hr0χ, ?_⟩
  apply Subtype.ext
  change r0.1 ^ 2 = 1
  rw [show r0.1 ^ 2 = (cycleRotationToCentralizer x (a ^ 2)).1 by
    exact cycleRotationToCentralizer_pow_coe x a 2]
  rw [ha2, map_one]
  rfl

end GLS3.Chapter5
/- END Theory.InvolutionOddRotationWitness -/

/- BEGIN Theory.NineImprimitive -/
noncomputable section

/- Source: NineBlockNormalizer.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

public abbrev nineImprimitiveGroup := alternatingImprimitiveGroup 3 3

/-- A standard blockwise three-cycle in the degree-nine imprimitive group. -/
@[expose]
public def nineBaseGenerator (i : Fin 3) : nineImprimitiveGroup :=
  SemidirectProduct.inl (Pi.mulSingle i a3Generator)

/-- The standard three-cycle permuting the three blocks. -/
@[expose]
public def nineTopGenerator : nineImprimitiveGroup :=
  SemidirectProduct.inr a3Generator

@[expose]
public def nineBaseAmbient (i : Fin 3) : alternatingGroup (Fin 9) :=
  alternatingImprimitiveFinHom 3 3 (nineBaseGenerator i)

@[expose]
public def nineTopAmbient : alternatingGroup (Fin 9) :=
  alternatingImprimitiveFinHom 3 3 nineTopGenerator

/-- Swap blocks zero and two and add one internal transposition in the fixed
block, producing an even permutation of the nine points. -/
@[expose]
public def nineBlockSwapProdPerm : Equiv.Perm (Fin 3 × Fin 3) :=
  blockBasePermHom (Fin 3) (Fin 3)
      (Pi.mulSingle (1 : Fin 3) (Equiv.swap (0 : Fin 3) (1 : Fin 3))) *
    blockTopPermHom (Fin 3) (Fin 3) (Equiv.swap (0 : Fin 3) (2 : Fin 3))

@[expose]
public def nineBlockSwapAmbient : alternatingGroup (Fin 9) :=
  ⟨finProdFinEquiv.permCongr nineBlockSwapProdPerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [Equiv.Perm.sign_permCongr]
    simp [nineBlockSwapProdPerm, blockBasePermHom, blockTopPermHom,
      Equiv.Perm.sign_prodCongrRight, Equiv.Perm.sign_prodCongrLeft,
      Pi.mulSingle]
    rw [Fin.prod_univ_three]
    simp [Function.update, show (2 : Fin 3) ≠ 1 by decide]
    simp [pow_succ]⟩

public theorem nineTopAmbient_orderOf : orderOf nineTopAmbient = 3 := by
  have hinr : Function.Injective
      (SemidirectProduct.inr : alternatingGroup (Fin 3) →* nineImprimitiveGroup) := by
    intro a b hab
    exact congrArg SemidirectProduct.right hab
  have htop : orderOf nineTopGenerator = 3 :=
    (orderOf_injective
      (SemidirectProduct.inr : alternatingGroup (Fin 3) →* nineImprimitiveGroup)
      hinr a3Generator).trans a3Generator_orderOf
  exact (orderOf_injective (alternatingImprimitiveFinHom 3 3)
    (alternatingImprimitiveFinHom_injective 3 3) nineTopGenerator).trans htop

public theorem nineBaseAmbient_orderOf (i : Fin 3) :
    orderOf (nineBaseAmbient i) = 3 := by
  have hsingle : orderOf (Pi.mulSingle i a3Generator :
      Fin 3 → alternatingGroup (Fin 3)) = 3 := by
    have hinj : Function.Injective
        (MonoidHom.mulSingle (fun _ : Fin 3 => alternatingGroup (Fin 3)) i) := by
      intro x y hxy
      exact Pi.mulSingle_injective i hxy
    exact (orderOf_injective
      (MonoidHom.mulSingle (fun _ : Fin 3 => alternatingGroup (Fin 3)) i)
      hinj a3Generator).trans a3Generator_orderOf
  have hinl : Function.Injective
      (SemidirectProduct.inl : (Fin 3 → alternatingGroup (Fin 3)) →*
        nineImprimitiveGroup) := by
    intro a b hab
    exact congrArg SemidirectProduct.left hab
  have hbase : orderOf (nineBaseGenerator i) = 3 :=
    (orderOf_injective
      (SemidirectProduct.inl : (Fin 3 → alternatingGroup (Fin 3)) →*
        nineImprimitiveGroup) hinl (Pi.mulSingle i a3Generator)).trans hsingle
  exact (orderOf_injective (alternatingImprimitiveFinHom 3 3)
    (alternatingImprimitiveFinHom_injective 3 3) (nineBaseGenerator i)).trans hbase

public theorem nineTop_conj_base_zero :
    nineTopAmbient * nineBaseAmbient 0 * nineTopAmbient⁻¹ =
      nineBaseAmbient 2 := by
  all_goals decide
public theorem nineTop_conj_base_two :
    nineTopAmbient * nineBaseAmbient 2 * nineTopAmbient⁻¹ =
      nineBaseAmbient 1 := by
  all_goals decide
public theorem nineTop_conj_base_one :
    nineTopAmbient * nineBaseAmbient 1 * nineTopAmbient⁻¹ =
      nineBaseAmbient 0 := by
  all_goals decide
public theorem nineBlockAction_base_zero :
    (alternatingBlockAction 3 3 a3Generator)
        (Pi.mulSingle 0 a3Generator) =
      Pi.mulSingle 2 a3Generator := by
  have hI : nineTopGenerator * nineBaseGenerator 0 * nineTopGenerator⁻¹ =
      nineBaseGenerator 2 := by
    apply alternatingImprimitiveFinHom_injective 3 3
    simpa [nineTopAmbient, nineBaseAmbient] using nineTop_conj_base_zero
  have h := SemidirectProduct.inl_aut
    (φ := alternatingBlockAction 3 3) a3Generator
      (Pi.mulSingle 0 a3Generator)
  have h' : SemidirectProduct.inl
      ((alternatingBlockAction 3 3 a3Generator) (Pi.mulSingle 0 a3Generator)) =
      nineBaseGenerator 2 := h.trans (by
        simpa [nineTopGenerator, nineBaseGenerator] using hI)
  exact congrArg SemidirectProduct.left h'

public theorem nineBlockAction_base_two :
    (alternatingBlockAction 3 3 a3Generator)
        (Pi.mulSingle 2 a3Generator) =
      Pi.mulSingle 1 a3Generator := by
  have hI : nineTopGenerator * nineBaseGenerator 2 * nineTopGenerator⁻¹ =
      nineBaseGenerator 1 := by
    apply alternatingImprimitiveFinHom_injective 3 3
    simpa [nineTopAmbient, nineBaseAmbient] using nineTop_conj_base_two
  have h := SemidirectProduct.inl_aut
    (φ := alternatingBlockAction 3 3) a3Generator
      (Pi.mulSingle 2 a3Generator)
  have h' : SemidirectProduct.inl
      ((alternatingBlockAction 3 3 a3Generator) (Pi.mulSingle 2 a3Generator)) =
      nineBaseGenerator 1 := h.trans (by
        simpa [nineTopGenerator, nineBaseGenerator] using hI)
  exact congrArg SemidirectProduct.left h'

public theorem nineBlockAction_base_one :
    (alternatingBlockAction 3 3 a3Generator)
        (Pi.mulSingle 1 a3Generator) =
      Pi.mulSingle 0 a3Generator := by
  have hI : nineTopGenerator * nineBaseGenerator 1 * nineTopGenerator⁻¹ =
      nineBaseGenerator 0 := by
    apply alternatingImprimitiveFinHom_injective 3 3
    simpa [nineTopAmbient, nineBaseAmbient] using nineTop_conj_base_one
  have h := SemidirectProduct.inl_aut
    (φ := alternatingBlockAction 3 3) a3Generator
      (Pi.mulSingle 1 a3Generator)
  have h' : SemidirectProduct.inl
      ((alternatingBlockAction 3 3 a3Generator) (Pi.mulSingle 1 a3Generator)) =
      nineBaseGenerator 0 := h.trans (by
        simpa [nineTopGenerator, nineBaseGenerator] using hI)
  exact congrArg SemidirectProduct.left h'

public theorem nineBlockSwap_conj_base_zero :
    nineBlockSwapAmbient * nineBaseAmbient 0 * nineBlockSwapAmbient⁻¹ =
      nineBaseAmbient 2 := by
  all_goals decide
public theorem nineBlockSwap_conj_base_two :
    nineBlockSwapAmbient * nineBaseAmbient 2 * nineBlockSwapAmbient⁻¹ =
      nineBaseAmbient 0 := by
  all_goals decide
public theorem nineBaseAmbient_zero_two_commute :
    Commute (nineBaseAmbient 0) (nineBaseAmbient 2) := by
  change nineBaseAmbient 0 * nineBaseAmbient 2 =
    nineBaseAmbient 2 * nineBaseAmbient 0
  all_goals decide
end GLS3.Chapter5.SchurPresentation

/- Source: NineImprimitiveSubextension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement
open scoped Pointwise

/-! ## The degree-nine imprimitive subextension

The Sylow three-subgroup of `A₉` lies in `(A₃)³ ⋊ A₃`.  Although its base
is not perfect, an explicit even block normalizer forces the chosen coordinate
lifts to commute.  Their cyclic sections then combine equivariantly with an
order-three lift of the top block cycle.
-/

private theorem __ch5_NineImprimitive_commutatorElement_mul_center
    {E : Type*} [Group E] (kx ky dx dy : E)
    (hkx : kx ∈ Subgroup.center E) (hky : ky ∈ Subgroup.center E) :
    ⁅kx * dx, ky * dy⁆ = ⁅dx, dy⁆ := by
  have hkxComm (z : E) : Commute kx z := by
    change kx * z = z * kx
    exact (Subgroup.mem_center_iff.mp hkx z).symm
  have hkyComm (z : E) : Commute ky z := by
    change ky * z = z * ky
    exact (Subgroup.mem_center_iff.mp hky z).symm
  calc
    ⁅kx * dx, ky * dy⁆ =
        kx * ⁅dx, ky * dy⁆ * kx⁻¹ * ⁅kx, ky * dy⁆ :=
      commutatorElement_mul_left_eq_conj_mul kx dx (ky * dy)
    _ = ⁅dx, ky * dy⁆ := by
      rw [(hkxComm (ky * dy)).commutator_eq]
      simp [(hkxComm ⁅dx, ky * dy⁆).eq, mul_assoc]
    _ = ⁅dx, ky⁆ * ky * ⁅dx, dy⁆ * ky⁻¹ :=
      commutatorElement_mul_right_eq_mul_conj dx ky dy
    _ = ⁅dx, dy⁆ := by
      rw [(hkyComm dx).symm.commutator_eq]
      simp [(hkyComm ⁅dx, dy⁆).eq, mul_assoc]

private theorem __ch5_NineImprimitive_exists_nine_top_base_lifts_commute
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 9))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker) :
    ∃ t x0 : H,
      f t = nineTopAmbient ∧ orderOf t = 3 ∧
      f x0 = nineBaseAmbient 0 ∧ orderOf x0 = 3 ∧
      Commute x0 (t * x0 * t⁻¹) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t, hft, hordt⟩ := exists_order_three_lift_of_five_le
    9 (by omega) f hf hker hker3 nineTopAmbient nineTopAmbient_orderOf
  obtain ⟨x0, hfx0, hordx0⟩ := exists_order_three_lift_of_five_le
    9 (by omega) f hf hker hker3 (nineBaseAmbient 0)
      (nineBaseAmbient_orderOf 0)
  let x2 := t * x0 * t⁻¹
  have hfx2 : f x2 = nineBaseAmbient 2 := by
    dsimp [x2]
    rw [map_mul, map_mul, map_inv, hft, hfx0]
    exact nineTop_conj_base_zero
  obtain ⟨z, hfz⟩ := hf nineBlockSwapAmbient
  let k0 := z * x0 * z⁻¹ * x2⁻¹
  let k2 := z * x2 * z⁻¹ * x0⁻¹
  have hk0 : k0 ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [k0]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfz, hfx0, hfx2,
      nineBlockSwap_conj_base_zero]
    simp
  have hk2 : k2 ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [k2]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfz, hfx0, hfx2,
      nineBlockSwap_conj_base_two]
    simp
  have hx0conj : z * x0 * z⁻¹ = k0 * x2 := by
    dsimp [k0]
    group
  have hx2conj : z * x2 * z⁻¹ = k2 * x0 := by
    dsimp [k2]
    group
  let c := ⁅x0, x2⁆
  have hcKer : c ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [c]
    rw [map_commutatorElement, hfx0, hfx2]
    exact nineBaseAmbient_zero_two_commute.commutator_eq
  have hcCenter : c ∈ Subgroup.center H := hker hcKer
  have hfix : z * c * z⁻¹ = c := by
    have hzcomm := Subgroup.mem_center_iff.mp hcCenter z
    rw [hzcomm]
    simp
  have hconj : z * c * z⁻¹ = c⁻¹ := by
    calc
      z * c * z⁻¹ = ⁅z * x0 * z⁻¹, z * x2 * z⁻¹⁆ := by
        exact conjugate_commutatorElement x0 x2 z
      _ = ⁅k0 * x2, k2 * x0⁆ := by rw [hx0conj, hx2conj]
      _ = ⁅x2, x0⁆ := __ch5_NineImprimitive_commutatorElement_mul_center
        k0 k2 x2 x0 (hker hk0) (hker hk2)
      _ = c⁻¹ := by exact (commutatorElement_inv x0 x2).symm
  have hcinv : c = c⁻¹ := hfix.symm.trans hconj
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [hcinv]
    exact mul_inv_cancel c
  have hcOne : c = 1 := by
    by_contra hc
    let cK : f.ker := ⟨c, hcKer⟩
    have hcKne : cK ≠ 1 := by
      intro h
      exact hc (congrArg Subtype.val h)
    have h3ordK : 3 ∣ orderOf cK := hker3.dvd_orderOf hcKne
    have h3ord : 3 ∣ orderOf c := by
      rw [← Subgroup.orderOf_coe cK] at h3ordK
      simpa [cK] using h3ordK
    have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h32 : 3 ∣ 2 := h3ord.trans hord2
    norm_num at h32
  refine ⟨t, x0, hft, hordt, hfx0, hordx0, ?_⟩
  exact commutatorElement_eq_one_iff_commute.mp hcOne

private theorem __ch5_NineImprimitive_a3MonoidHom_ext
    {K : Type*} [Group K]
    {u v : alternatingGroup (Fin 3) →* K}
    (h : u a3Generator = v a3Generator) : u = v := by
  apply MonoidHom.ext
  intro a
  have ha : a ∈ Subgroup.zpowers a3Generator := by
    rw [a3Generator_zpowers_eq_top]
    trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [map_zpow, map_zpow, h]

set_option linter.unusedSimpArgs false in
/-- Every finite central three-primary extension splits over the standard
degree-nine imprimitive subgroup `(A₃)³ ⋊ A₃`. -/
public theorem exists_nineImprimitivePreimage_section_isComplement'
    {H : Type} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 9))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker) :
    ∃ s : nineImprimitiveGroup →*
        alternatingImprimitivePreimage 3 3 f,
      (alternatingImprimitivePreimageProjection 3 3 f).comp s =
        MonoidHom.id _ ∧
      (alternatingImprimitivePreimageProjection 3 3 f).ker.IsComplement'
        s.range := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let E := alternatingImprimitivePreimage 3 3 f
  let r := alternatingImprimitivePreimageProjection 3 3 f
  let i := alternatingImprimitiveFinHom 3 3
  obtain ⟨tH, x0H, hft, hordtH, hfx0, hordx0H, hcommH⟩ :=
    __ch5_NineImprimitive_exists_nine_top_base_lifts_commute f hf hker hker3
  have htmem : tH ∈ E := ⟨nineTopGenerator, hft.symm⟩
  have hx0mem : x0H ∈ E := ⟨nineBaseGenerator 0, hfx0.symm⟩
  let t : E := ⟨tH, htmem⟩
  let x0 : E := ⟨x0H, hx0mem⟩
  have hr_of_image (y : H) (a : nineImprimitiveGroup)
      (hy : f y = i a) (hyE : y ∈ E) : r ⟨y, hyE⟩ = a := by
    let e := MonoidHom.ofInjective
      (alternatingImprimitiveFinHom_injective 3 3)
    change e.symm ⟨f y, hyE⟩ = a
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hy
  have hrt : r t = nineTopGenerator := by
    exact hr_of_image tH nineTopGenerator hft htmem
  have hrx0 : r x0 = nineBaseGenerator 0 := by
    exact hr_of_image x0H (nineBaseGenerator 0) hfx0 hx0mem
  let x2 : E := t * x0 * t⁻¹
  let x1 : E := t * x2 * t⁻¹
  have hrx2 : r x2 = nineBaseGenerator 2 := by
    dsimp [x2]
    rw [map_mul, map_mul, map_inv, hrt, hrx0]
    apply alternatingImprimitiveFinHom_injective 3 3
    simpa [nineTopAmbient, nineBaseAmbient] using nineTop_conj_base_zero
  have hrx1 : r x1 = nineBaseGenerator 1 := by
    dsimp [x1]
    rw [map_mul, map_mul, map_inv, hrt, hrx2]
    apply alternatingImprimitiveFinHom_injective 3 3
    simpa [nineTopAmbient, nineBaseAmbient] using nineTop_conj_base_two
  have hordt : orderOf t = 3 :=
    (Subgroup.orderOf_coe t).symm.trans hordtH
  have hordx0 : orderOf x0 = 3 :=
    (Subgroup.orderOf_coe x0).symm.trans hordx0H
  have hcomm02 : Commute x0 x2 := by
    change x0 * x2 = x2 * x0
    apply Subtype.ext
    exact hcommH.eq
  have ht3 : t ^ 3 = 1 := by
    rw [← hordt]
    exact pow_orderOf_eq_one t
  have ht3' : t * t * t = 1 := by
    simpa [pow_succ, mul_assoc] using ht3
  have hti3' : t⁻¹ * t⁻¹ * t⁻¹ = 1 := by
    have h := congrArg Inv.inv ht3'
    simpa [mul_inv_rev, mul_assoc] using h
  have htx1 : t * x1 * t⁻¹ = x0 := by
    dsimp [x1, x2]
    calc
      t * (t * (t * x0 * t⁻¹) * t⁻¹) * t⁻¹ =
          (t * t * t) * x0 * (t⁻¹ * t⁻¹ * t⁻¹) := by group
      _ = x0 := by rw [ht3', hti3']; simp
  have hcomm21 : Commute x2 x1 := by
    have h := hcomm02.map (MulAut.conj t).toMonoidHom
    simpa [MulAut.conj_apply, x2, x1] using h
  have hcomm10 : Commute x1 x0 := by
    have h := hcomm21.map (MulAut.conj t).toMonoidHom
    simpa [MulAut.conj_apply, x1, htx1] using h
  let g : alternatingGroup (Fin 3) := a3Generator
  obtain ⟨s0, hs0g⟩ := exists_cyclic_section_of_order_three
    g a3_card a3Generator_orderOf x0 hordx0
  let s2 : alternatingGroup (Fin 3) →* E :=
    (MulAut.conj t).toMonoidHom.comp s0
  let s1 : alternatingGroup (Fin 3) →* E :=
    (MulAut.conj t).toMonoidHom.comp s2
  obtain ⟨sA, hsAg⟩ := exists_cyclic_section_of_order_three
    g a3_card a3Generator_orderOf t hordt
  let sCoord : (j : Fin 3) → alternatingGroup (Fin 3) →* E :=
    fun j => if j = 0 then s0 else if j = 1 then s1 else s2
  have hsCoordg (j : Fin 3) :
      sCoord j g = if j = 0 then x0 else if j = 1 then x1 else x2 := by
    fin_cases j <;>
      simp [sCoord, s1, s2, g, hs0g, MulAut.conj_apply, x1, x2]
  have hcoordGen : Pairwise fun j k : Fin 3 =>
      Commute (sCoord j g) (sCoord k g) := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      simp_all [sCoord, s1, s2, g, hs0g, MulAut.conj_apply, x1, x2,
        hcomm02, hcomm21, hcomm10,
        hcomm02.symm, hcomm21.symm, hcomm10.symm]
  have hcoord : Pairwise fun j k : Fin 3 => ∀ a b,
      Commute (sCoord j a) (sCoord k b) := by
    intro j k hjk a b
    have ha : a ∈ Subgroup.zpowers g := by
      change a ∈ Subgroup.zpowers a3Generator
      rw [a3Generator_zpowers_eq_top]
      trivial
    have hb : b ∈ Subgroup.zpowers g := by
      change b ∈ Subgroup.zpowers a3Generator
      rw [a3Generator_zpowers_eq_top]
      trivial
    obtain ⟨u, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨v, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [map_zpow, map_zpow]
    exact (hcoordGen hjk).zpow_zpow u v
  let sN : (Fin 3 → alternatingGroup (Fin 3)) →* E :=
    MonoidHom.noncommPiCoprod sCoord hcoord
  have hsCoord (j : Fin 3) : r.comp (sCoord j) =
      (SemidirectProduct.inl :
        (Fin 3 → alternatingGroup (Fin 3)) →* nineImprimitiveGroup).comp
        (MonoidHom.mulSingle
          (fun _ : Fin 3 => alternatingGroup (Fin 3)) j) := by
    apply __ch5_NineImprimitive_a3MonoidHom_ext
    fin_cases j <;>
      simp [sCoord, s1, s2, g, hs0g, MulAut.conj_apply,
        x1, x2, hrx0, hrx1, hrx2, map_mul, map_inv,
        nineBaseGenerator]
  have hsN : r.comp sN =
      (SemidirectProduct.inl :
        (Fin 3 → alternatingGroup (Fin 3)) →* nineImprimitiveGroup) := by
    apply MonoidHom.pi_ext
    intro j a
    have hj := DFunLike.congr_fun (hsCoord j) a
    simpa [sN, MonoidHom.comp_apply] using hj
  have hsA : r.comp sA =
      (SemidirectProduct.inr :
        alternatingGroup (Fin 3) →* nineImprimitiveGroup) := by
    apply __ch5_NineImprimitive_a3MonoidHom_ext
    simp [g, hsAg, hrt, nineTopGenerator]
  have hcompatG :
      sN.comp ((alternatingBlockAction 3 3) g).toMonoidHom =
        (MulAut.conj (sA g)).toMonoidHom.comp sN := by
    apply MonoidHom.pi_ext
    intro j a
    let u : alternatingGroup (Fin 3) →* E :=
      (sN.comp ((alternatingBlockAction 3 3) g).toMonoidHom).comp
        (MonoidHom.mulSingle
          (fun _ : Fin 3 => alternatingGroup (Fin 3)) j)
    let v : alternatingGroup (Fin 3) →* E :=
      ((MulAut.conj (sA g)).toMonoidHom.comp sN).comp
        (MonoidHom.mulSingle
          (fun _ : Fin 3 => alternatingGroup (Fin 3)) j)
    have huv : u = v := by
      apply __ch5_NineImprimitive_a3MonoidHom_ext
      fin_cases j <;>
        simp [u, v, sN, sCoord, s1, s2, g, hsAg, hs0g,
          MonoidHom.comp_apply, MulAut.conj_apply, x1, x2,
          htx1,
          nineBlockAction_base_zero, nineBlockAction_base_one,
          nineBlockAction_base_two]
    exact DFunLike.congr_fun huv a
  let C : Subgroup (alternatingGroup (Fin 3)) := {
    carrier := {a | ∀ n,
      sN ((alternatingBlockAction 3 3) a n) =
        sA a * sN n * (sA a)⁻¹}
    one_mem' := by intro n; simp
    mul_mem' := by
      intro a b ha hb n
      change sN (((alternatingBlockAction 3 3) (a * b)) n) = _
      rw [map_mul, map_mul]
      change sN ((alternatingBlockAction 3 3 a)
        ((alternatingBlockAction 3 3 b) n)) = _
      rw [ha, hb]
      group
    inv_mem' := by
      intro a ha n
      change sN ((alternatingBlockAction 3 3 a⁻¹) n) = _
      rw [map_inv, map_inv]
      change sN (((alternatingBlockAction 3 3 a)⁻¹ n)) =
        (sA a)⁻¹ * sN n * ((sA a)⁻¹)⁻¹
      have h := ha (((alternatingBlockAction 3 3 a)⁻¹) n)
      have hcancel : (alternatingBlockAction 3 3 a)
          (((alternatingBlockAction 3 3 a)⁻¹) n) = n := by
        exact (alternatingBlockAction 3 3 a).apply_symm_apply n
      rw [hcancel] at h
      rw [h]
      group
  }
  have hgC : g ∈ C := by
    intro n
    have h := DFunLike.congr_fun hcompatG n
    simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h
  have hCtop : C = ⊤ := by
    apply top_unique
    rw [← a3Generator_zpowers_eq_top]
    exact Subgroup.zpowers_le.mpr hgC
  have hcompat (a : alternatingGroup (Fin 3)) :
      sN.comp ((alternatingBlockAction 3 3) a).toMonoidHom =
        (MulAut.conj (sA a)).toMonoidHom.comp sN := by
    apply MonoidHom.ext
    intro n
    have ha : a ∈ C := by rw [hCtop]; trivial
    simpa [MonoidHom.comp_apply, MulAut.conj_apply] using ha n
  let s : nineImprimitiveGroup →* E :=
    SemidirectProduct.lift sN sA hcompat
  have hsec : r.comp s = MonoidHom.id nineImprimitiveGroup := by
    apply SemidirectProduct.hom_ext
    · rw [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inl, hsN]
      rfl
    · rw [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inr, hsA]
      rfl
  have hdisj : Disjoint r.ker s.range := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    obtain ⟨y, rfl⟩ := hxR
    have hy : y = 1 := by
      have hxy : r (s y) = y := DFunLike.congr_fun hsec y
      have hrone : r (s y) = 1 := MonoidHom.mem_ker.mp hxK
      exact hxy.symm.trans hrone
    rw [hy]
    exact map_one s
  have hmul : (r.ker : Set E) * (s.range : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    let y := s (r x)
    let k := x * y⁻¹
    have hyr : r y = r x := DFunLike.congr_fun hsec (r x)
    have hk : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, hyr]
      exact mul_inv_cancel _
    have hy : y ∈ s.range := ⟨r x, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨k, hk, y, hy, by simp [k]⟩
  exact ⟨s, hsec,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

end GLS3.Chapter5.SchurPresentation

/- Source: NineImprimitiveEndpoint.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## The degree-nine imprimitive endpoint -/

/-- A finite perfect central extension of `A₉` with three-primary kernel is
trivial.  The standard `(A₃)³ ⋊ A₃` subgroup contains an ambient Sylow
three-subgroup, while its full preimage splits by the explicit normalizer
argument. -/
public theorem kernel_eq_bot_of_nineImprimitive
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin 9))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker) :
    f.ker = ⊥ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨S, hS⟩ :
      ∃ S : Sylow 3 (alternatingGroup (Fin 9)),
        (S : Subgroup _) ≤ (alternatingImprimitiveFinHom 3 3).range := by
    simpa [pow_one] using
      (exists_sylow_three_le_alternatingImprimitiveFinHom_range 1 (by omega))
  have hSrange : (S : Subgroup _) ≤ f.range := by
    intro x hx
    exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
  let P : Sylow 3 H := S.comapOfKerIsPGroup f hker3 hSrange
  let E := alternatingImprimitivePreimage 3 3 f
  have hPE : (P : Subgroup H) ≤ E := by
    intro x hx
    change f x ∈ (alternatingImprimitiveFinHom 3 3).range
    apply hS
    exact hx
  obtain ⟨t, -, hcomp⟩ :=
    exists_nineImprimitivePreimage_section_isComplement'
      f hf hker hker3
  exact kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
    f hker hker3 P E hPE t.range (by
      rw [← alternatingImprimitivePreimageProjection_ker_eq_comap]
      exact hcomp)

/-- The universal central covering of `A₉` has kernel order prime to three. -/
public theorem
    not_dvd_natCard_ker_alternatingFreeCentralCovering_three_degree_nine :
    ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering 4).toMonoidHom.ker := by
  intro h3M
  let f := alternatingFreeCentralCovering 4
  obtain ⟨X, hX, fbar, _hXker, hbarSurj, hbarCenter, hbarP, h3bar⟩ :=
    exists_pPrimary_quotient_central_extension
      f.toMonoidHom f.surjective f.ker_le_center h3M
  let : X.Normal := hX
  have hbot := kernel_eq_bot_of_nineImprimitive
    fbar hbarSurj hbarCenter hbarP
  rw [hbot, Subgroup.card_bot] at h3bar
  exact Nat.prime_three.ne_one (Nat.dvd_one.mp h3bar)

end GLS3.Chapter5.SchurPresentation
/- END Theory.NineImprimitive -/

/- BEGIN Theory.FixedPointOddInvolutionWitness -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_FixedPointOddInvolutionWitness_u

/-- Two fixed points provide an odd order-two element in the fixed-point
symmetric factor. -/
public theorem exists_odd_involution_mem_fixedPointPermutationSubgroup
    {Ω : Type __ch5_FixedPointOddInvolutionWitness_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (hs : 2 ≤ Fintype.card (Function.fixedPoints x)) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    ∃ i0 : C, i0 ∈ fixedPointPermutationSubgroup x ∧ χ i0 = -1 ∧ i0 ^ 2 = 1 := by
  dsimp only
  obtain ⟨__ch5_FixedPointOddInvolutionWitness_u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card
    (by omega : 1 < Fintype.card (Function.fixedPoints x))
  let σ : Equiv.Perm (Function.fixedPoints x) := Equiv.swap __ch5_FixedPointOddInvolutionWitness_u v
  let i0 := fixedPointPermToCentralizer x σ
  have hi0χ : Equiv.Perm.sign i0.1 = -1 := by
    change Equiv.Perm.sign ((fixedPointPermToCentralizer x σ).1) = -1
    rw [fixedPointPermToCentralizer_coe, Equiv.Perm.sign_ofSubtype]
    simp [σ, huv]
  refine ⟨i0, ⟨σ, rfl⟩, hi0χ, ?_⟩
  dsimp [i0]
  rw [← map_pow]
  simp [σ, pow_two, Equiv.swap_mul_self __ch5_FixedPointOddInvolutionWitness_u v]

end GLS3.Chapter5
/- END Theory.FixedPointOddInvolutionWitness -/

/- BEGIN Theory.ThreeMultiplierBound -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-! # Exclusion of the three-primary multiplier part

Strong induction on the alternating degree combines the degree-eight and
degree-nine base cases, the nontransitive orbit reduction, and the transitive
three-power imprimitive endpoint.
-/

/-- Except in degrees six and seven, three does not divide the kernel of the
universal central covering of an alternating group. -/
public theorem not_dvd_natCard_ker_alternatingFreeCentralCovering_three
    (n : Nat) (hn6 : n + 5 ≠ 6) (hn7 : n + 5 ≠ 7) :
    ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h3M
    by_cases hn0 : n = 0
    · subst n
      rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two] at h3M
      omega
    by_cases hn1 : n = 1
    · subst n
      exact hn6 (by norm_num)
    by_cases hn2 : n = 2
    · subst n
      exact hn7 (by norm_num)
    by_cases hn3 : n = 3
    · subst n
      exact
        not_dvd_natCard_ker_alternatingFreeCentralCovering_three_degree_eight h3M
    by_cases hn4 : n = 4
    · subst n
      exact
        not_dvd_natCard_ker_alternatingFreeCentralCovering_three_degree_nine h3M
    have hn5 : 5 ≤ n := by omega
    have h3Pred : ¬ 3 ∣ Nat.card
        (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker := by
      apply ih
      · omega
      · omega
      · omega
    have h3deg : 3 ∣ n + 5 :=
      prime_dvd_degree_of_dvd_multiplier_of_not_dvd_predecessor
        n (by omega) h3M h3Pred
    have hm12 : 12 ≤ n + 5 := by
      obtain ⟨k, hk⟩ := h3deg
      omega
    let f := alternatingFreeCentralCovering n
    obtain ⟨X, hX, fbar, _hXker, hbarSurj, hbarCenter, hbarP, h3bar⟩ :=
      exists_pPrimary_quotient_central_extension
        f.toMonoidHom f.surjective f.ker_le_center h3M
    let : X.Normal := hX
    let P : Sylow 3 (AlternatingFreeCentralDerived n ⧸ X) := default
    have hsmall : ∀ d : Nat, 5 ≤ d → d < n + 5 → d ≠ 6 → d ≠ 7 →
        ¬ 3 ∣ Nat.card
          (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker := by
      intro d hd5 hdn hd6 hd7
      apply ih
      · omega
      · simpa [Nat.sub_add_cancel hd5] using hd6
      · simpa [Nat.sub_add_cancel hd5] using hd7
    by_cases htrans : MulAction.IsPretransitive
        (P.mapSurjective hbarSurj) (Fin (n + 5))
    · let Q : Sylow 3 (alternatingGroup (Fin (n + 5))) :=
        P.mapSurjective hbarSurj
      let : MulAction.IsPretransitive Q (Fin (n + 5)) := htrans
      let y : Fin (n + 5) := ⟨0, by omega⟩
      obtain ⟨r, hrOrbit⟩ := Q.isPGroup'.card_orbit y
      have hr : n + 5 = 3 ^ r := by
        have hcard : Nat.card (MulAction.orbit Q y) = n + 5 := by
          rw [MulAction.orbit_eq_univ]
          simp
        exact hcard.symm.trans hrOrbit
      have hr3 : 3 ≤ r := by
        by_contra hrnot
        have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
        rcases hrCases with rfl | rfl | rfl <;> norm_num at hr <;> omega
      let s := r - 1
      have hs : 0 < s := by omega
      let d := 3 ^ s
      have hd9 : 9 ≤ d := by
        dsimp [d]
        have hs2 : 2 ≤ s := by omega
        calc
          9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ s := pow_le_pow_right₀ (by omega : 1 ≤ 3) hs2
      have hd5 : 5 ≤ d := by omega
      let q := d - 5
      have hq : q + 5 = d := Nat.sub_add_cancel hd5
      have hpow : q + 5 = 3 ^ s := by
        rw [hq]
      have hrsucc : r = s + 1 := by omega
      have hm : n + 5 = 3 * (q + 5) := by
        calc
          n + 5 = 3 ^ r := hr
          _ = 3 ^ (s + 1) := by rw [hrsucc]
          _ = 3 * 3 ^ s := by rw [pow_succ']
          _ = 3 * (q + 5) := by rw [hpow]
      have hdlt : d < n + 5 := by
        rw [hm, hq]
        exact lt_mul_of_one_lt_left (pow_pos (by omega : 0 < 3) s) (by omega)
      have h3Base : ¬ 3 ∣ Nat.card
          (alternatingFreeCentralCovering q).toMonoidHom.ker := by
        apply ih
        · dsimp [q]
          omega
        · rw [hq]
          omega
        · rw [hq]
          omega
      have hbot := kernel_eq_bot_of_alternatingThreeImprimitive_primePower_degree
        q s (n + 5) hs hpow hm fbar hbarSurj hbarCenter hbarP h3Base
      rw [hbot, Subgroup.card_bot] at h3bar
      exact Nat.prime_three.ne_one (Nat.dvd_one.mp h3bar)
    · exact false_of_not_pretransitive_sylow_image_three_of_inductive_not_dvd
        (n + 5) hm12 h3deg fbar hbarSurj hbarCenter hbarP h3bar P htrans hsmall

end GLS3.Chapter5.SchurPresentation
/- END Theory.ThreeMultiplierBound -/

/- BEGIN Theory.SmallFixedPointFactorEven -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_SmallFixedPointFactorEven_u

/-- A symmetric group on at most one fixed point is trivial, hence its
embedded fixed-point factor lies in the sign kernel. -/
public theorem fixedPointPermutationSubgroup_le_signKernel_of_card_le_one
    {Ω : Type __ch5_SmallFixedPointFactorEven_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (hs : Fintype.card (Function.fixedPoints x) ≤ 1) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    fixedPointPermutationSubgroup x ≤ χ.ker := by
  dsimp only
  intro i hi
  rw [MonoidHom.mem_ker]
  let ii : fixedPointPermutationSubgroup x := ⟨i, hi⟩
  let e := theorem_5_2_2_d_4 x
  have : Subsingleton (Function.fixedPoints x) :=
    Fintype.card_le_one_iff_subsingleton.mp hs
  have he : e ii = 1 := Subsingleton.elim _ _
  change Equiv.Perm.sign i.1 = 1
  rw [show Equiv.Perm.sign i.1 = Equiv.Perm.sign (e ii) by
    exact fixedPointPermutation_sign x ii, he]
  simp

end GLS3.Chapter5
/- END Theory.SmallFixedPointFactorEven -/

/- BEGIN Theory.TwoReduction -/
noncomputable section

/- Source: TwoRootReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # First reductions for the two-primary multiplier bound -/

/-- In nonexceptional degree the universal alternating multiplier is a
two-group, since all odd prime divisors have already been excluded. -/
public theorem isTwoGroup_ker_alternatingFreeCentralCovering
    (n : Nat) (hn6 : n + 5 ≠ 6) (hn7 : n + 5 ≠ 7) :
    IsPGroup 2 (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  let K := (alternatingFreeCentralCovering n).toMonoidHom.ker
  apply IsPGroup.iff_card.mpr
  refine ⟨(Nat.card K).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro q hq hqd
  by_cases hq2 : q = 2
  · exact hq2
  by_cases hq3 : q = 3
  · subst q
    exact False.elim
      (not_dvd_natCard_ker_alternatingFreeCentralCovering_three n hn6 hn7 hqd)
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
  exact False.elim
    (not_dvd_natCard_ker_alternatingFreeCentralCovering_of_five_le_prime
      q n hq hq5 hqd)

/-- If a Sylow `p`-subgroup lies in the full preimage of a perfect root
alternating subgroup, the global central `p`-kernel embeds in the kernel of
the derived root covering.  Unlike the earlier splitting endpoint, this does
not require the derived kernel to be trivial. -/
public theorem
    natCard_ker_le_centralRootAmPreimageDerivedProjection_ker_of_sylow_le
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (P : Sylow p H)
    (hPE : (P : Subgroup H) ≤
      centralRootAmPreimage (H := H) n m hmn f) :
    Nat.card f.ker ≤ Nat.card
      (centralRootAmPreimageDerivedProjection n m hmn f).ker := by
  let E := centralRootAmPreimage (H := H) n m hmn f
  let r := centralRootAmPreimageProjection n m hmn f
  let D := centralRootAmPreimageDerived n m hmn f
  let rD := centralRootAmPreimageDerivedProjection n m hmn f
  have hKleP : f.ker ≤ (P : Subgroup H) :=
    hkerp.le_sylow_of_normal P
  let i : P →* E :=
    (P : Subgroup H).subtype.codRestrict E (fun x => hPE x.2)
  let Kp : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  let C : Subgroup P := D.comap i
  have hKpFrattini : Kp ≤ frattini P :=
    ker_comap_le_frattini_sylow P f hker
  have hsup : C ⊔ Kp = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨d, hd⟩ :=
      centralRootAmPreimageDerivedProjection_surjective
        n m hmn f hsurj (r (i x))
    have hd' : r (d : E) = r (i x) := hd
    let k : r.ker := ⟨i x * (d : E)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change r (i x) * (r (d : E))⁻¹ = 1
      rw [hd']
      simp⟩
    have hkGlobal : ((k : E) : H) ∈ f.ker := by
      have hkcomap : (k : E) ∈ f.ker.comap E.subtype := by
        rw [← centralRootAmPreimageProjection_ker_eq_comap]
        exact k.2
      exact hkcomap
    let kp : P := ⟨((k : E) : H), hKleP hkGlobal⟩
    have hkpKp : kp ∈ Kp := hkGlobal
    let dp : P := kp⁻¹ * x
    have hidp : i dp = d := by
      apply Subtype.ext
      change ((k : E) : H)⁻¹ * (x : H) = ((d : E) : H)
      have hkdef : ((k : E) : H) = (x : H) * ((d : E) : H)⁻¹ := rfl
      rw [hkdef]
      group
    have hdpC : dp ∈ C := by
      change i dp ∈ D
      rw [hidp]
      exact d.2
    have hkpSup : kp ∈ C ⊔ Kp := Subgroup.mem_sup_right hkpKp
    have hdpSup : dp ∈ C ⊔ Kp := Subgroup.mem_sup_left hdpC
    have hxSup := Subgroup.mul_mem (C ⊔ Kp) hkpSup hdpSup
    simpa [dp] using hxSup
  have hCfrattini : C ⊔ frattini P = ⊤ := by
    apply top_unique
    calc
      (⊤ : Subgroup P) = C ⊔ Kp := hsup.symm
      _ ≤ C ⊔ frattini P := sup_le_sup le_rfl hKpFrattini
  have hCtop : C = ⊤ :=
    frattini_nongenerating (K := C) hCfrattini
  have hintoD : ∀ z : f.ker, ∃ d : D, (((d : D) : E) : H) = z := by
    intro z
    let zp : P := ⟨z, hKleP z.2⟩
    have hzpC : zp ∈ C := by rw [hCtop]; trivial
    exact ⟨⟨i zp, hzpC⟩, rfl⟩
  let toD : f.ker → D := fun z => Classical.choose (hintoD z)
  have htoDval (z : f.ker) : (((toD z : D) : E) : H) = z :=
    Classical.choose_spec (hintoD z)
  have htoDker (z : f.ker) : toD z ∈ rD.ker := by
    have hzker : (toD z : E) ∈ r.ker := by
      have hzcomap : (toD z : E) ∈ f.ker.comap E.subtype := by
        change (((toD z : D) : E) : H) ∈ f.ker
        rw [htoDval]
        exact z.2
      rw [← centralRootAmPreimageProjection_ker_eq_comap] at hzcomap
      exact hzcomap
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp hzker
  let j : f.ker → rD.ker := fun z => ⟨toD z, htoDker z⟩
  apply Nat.card_le_card_of_injective j
  intro a b hab
  apply Subtype.ext
  calc
    (a : H) = (((toD a : D) : E) : H) := (htoDval a).symm
    _ = (((toD b : D) : E) : H) := by
      exact congrArg (fun z : rD.ker => (((z : D) : E) : H)) hab
    _ = (b : H) := htoDval b

/-- Odd permutation degree reduces the two-primary kernel bound to the point
stabilizer one degree lower. -/
public theorem natCard_ker_le_two_of_odd_degree_of_predecessor_multiplier_le_two
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (n : Nat) (hn : 1 ≤ n) (hodd : Odd (n + 5))
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker2 : IsPGroup 2 f.ker)
    (hpred : Nat.card
      (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker ≤ 2) :
    Nat.card f.ker ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 H := default
  obtain ⟨P', hP'root⟩ :=
    exists_conjugate_sylow_le_rootAm_pred
      n hn f hsurj P hodd.not_two_dvd_nat
  calc
    Nat.card f.ker ≤ Nat.card
        (centralRootAmPreimageDerivedProjection
          n (n + 4) (by omega) f).ker :=
      natCard_ker_le_centralRootAmPreimageDerivedProjection_ker_of_sylow_le
        n (n + 4) (by omega) f hsurj hker hker2 P' hP'root
    _ ≤ Nat.card
        (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker :=
      centralRootAmPreimageDerivedProjection_ker_card_le_multiplier
        n (n + 4) (by omega) (by omega) f hsurj hker
    _ ≤ 2 := hpred

/-- Universal-cover wrapper for the odd-degree two-primary reduction. -/
public theorem
    natCard_ker_alternatingFreeCentralCovering_le_two_of_odd_degree_of_predecessor_le_two
    (n : Nat) (hn : 1 ≤ n) (hn6 : n + 5 ≠ 6) (hn7 : n + 5 ≠ 7)
    (hodd : Odd (n + 5))
    (hpred : Nat.card
      (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker ≤ 2) :
    Nat.card (alternatingFreeCentralCovering n).toMonoidHom.ker ≤ 2 := by
  let f := alternatingFreeCentralCovering n
  exact natCard_ker_le_two_of_odd_degree_of_predecessor_multiplier_le_two
    n hn hodd f.toMonoidHom f.surjective f.ker_le_center
      (isTwoGroup_ker_alternatingFreeCentralCovering n hn6 hn7) hpred

end GLS3.Chapter5.SchurPresentation

/- Source: TwoOrbitReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # Invariant even blocks for Sylow two-subgroups -/

/-- In even degree at least five, a nontransitive Sylow-2 subgroup of the
alternating group preserves a proper subset such that both blocks have
positive even cardinality. -/
public theorem
    exists_invariant_even_proper_subset_of_not_pretransitive_sylow_two
    (m : Nat) (hm5 : 5 ≤ m) (hmeven : Even m)
    (Q : Sylow 2 (alternatingGroup (Fin m)))
    (hnotTrans : ¬ MulAction.IsPretransitive Q (Fin m)) :
    ∃ S : Set (Fin m),
      2 ∣ Nat.card S ∧ 2 ≤ Nat.card S ∧
      2 ∣ Nat.card (Sᶜ : Set (Fin m)) ∧
      2 ≤ Nat.card (Sᶜ : Set (Fin m)) ∧
      ∀ q : Q, Set.MapsTo
        ((q : alternatingGroup (Fin m)) : Fin m → Fin m) S S := by
  have hm4 : 4 ≤ m := by omega
  have hcardFormula :
      2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := by
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h := two_mul_nat_card_alternatingGroup (α := Fin m)
    rw [Nat.card_perm] at h
    simpa [Nat.card_fin] using h
  have h4fact : 4 ∣ m.factorial := by
    exact (show 4 ∣ (4 : Nat).factorial by
      refine ⟨6, ?_⟩
      norm_num [Nat.factorial]).trans
      (Nat.factorial_dvd_factorial hm4)
  have h2card : 2 ∣ Nat.card (alternatingGroup (Fin m)) := by
    obtain ⟨k, hk⟩ := h4fact
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    calc
      2 * Nat.card (alternatingGroup (Fin m)) = m.factorial := hcardFormula
      _ = 4 * k := hk
      _ = 2 * (2 * k) := by omega
  have hQne : (Q : Subgroup (alternatingGroup (Fin m))) ≠ ⊥ :=
    Q.ne_bot_of_dvd_card h2card
  obtain ⟨q, hqQ, hq1⟩ : ∃ q : alternatingGroup (Fin m),
      q ∈ (Q : Subgroup (alternatingGroup (Fin m))) ∧ q ≠ 1 := by
    by_contra h
    push Not at h
    apply hQne
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact h q hq
  let qQ : Q := ⟨q, hqQ⟩
  obtain ⟨y, hqy⟩ : ∃ y : Fin m, qQ • y ≠ y := by
    by_contra h
    push Not at h
    apply hq1
    apply Subtype.ext
    ext y
    have hy := h y
    change (q : Equiv.Perm (Fin m)) y = y at hy
    exact congrArg Fin.val hy
  have hproper : MulAction.orbit Q y ≠ Set.univ := by
    intro htop
    exact hnotTrans
      ((MulAction.isPretransitive_iff_orbit_eq_univ y).mpr htop)
  let S : Set (Fin m) := MulAction.orbit Q y
  let a := Nat.card S
  let b := Nat.card (Sᶜ : Set (Fin m))
  let : Fintype S := Fintype.ofFinite _
  have hsum : m = a + b := by
    have h := Set.ncard_add_ncard_compl S
    simpa [a, b, Nat.card_fin, add_comm] using h.symm
  have hyNotFixed : y ∉ MulAction.fixedPoints Q (Fin m) := by
    intro hy
    exact hqy (MulAction.mem_fixedPoints.mp hy qQ)
  obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
  have hra : a = 2 ^ r := by
    simpa [a, S] using hr
  have ha1 : a ≠ 1 := by
    intro ha
    apply hyNotFixed
    rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
    simpa [a, S, Nat.card_eq_fintype_card] using ha
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    apply ha1
    simpa only [pow_zero] using hra
  have h2a : 2 ∣ a := by
    rw [hra]
    exact dvd_pow_self 2 hr0
  have haPos : 0 < a := by
    exact (show S.Nonempty from ⟨y, MulAction.mem_orbit_self y⟩).ncard_pos
  have ha2 : 2 ≤ a := by
    obtain ⟨k, hk⟩ := h2a
    omega
  have hScNonempty : (Sᶜ : Set (Fin m)).Nonempty := by
    apply Set.ssubset_univ_iff_nonempty_compl.mp
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, hproper⟩
  have hbPos : 0 < b := hScNonempty.ncard_pos
  have h2m : 2 ∣ m := even_iff_two_dvd.mp hmeven
  have h2b : 2 ∣ b := by
    apply (Nat.dvd_add_iff_right h2a).mpr
    rwa [← hsum]
  have hb2 : 2 ≤ b := by
    obtain ⟨k, hk⟩ := h2b
    omega
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · exact h2a
  · exact ha2
  · exact h2b
  · exact hb2
  · intro q
    exact MulAction.mapsTo_smul_orbit q y

end GLS3.Chapter5.SchurPresentation
/- END Theory.TwoReduction -/

/- BEGIN Theory.InvolutionSignKernelDecomposition -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionSignKernelDecomposition_u

/-- The sign kernel in an involution centralizer is generated by the even
rotation factor, the full cycle-permuting factor, the even fixed-point factor,
and at most one additional involution pairing the two odd cosets. -/
public theorem involutionSignKernelDecomposition
    {Ω : Type __ch5_InvolutionSignKernelDecomposition_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    let RZ := (cycleRotationSubgroup x).comap Z.subtype
    let LZ := (cyclePermutationSubgroup x).comap Z.subtype
    let IZ := (fixedPointPermutationSubgroup x).comap Z.subtype
    ∃ t : Z,
      ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers t = ⊤ ∧
        t ^ 2 = 1 ∧
        (Fintype.card (Function.fixedPoints x) ≤ 1 → t = 1) := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let I : Subgroup C := fixedPointPermutationSubgroup x
  have hxprime : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  have hLχ : L ≤ χ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact involutionCyclePermutation_sign x hx ⟨l, hl⟩
  have hLnorm : L ≤ Subgroup.normalizer R :=
    cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x
  have hIcomm : I ≤ Subgroup.centralizer ((R ⊔ L : Subgroup C) : Set C) :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.2
  have hsup : I ⊔ (R ⊔ L) = ⊤ :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.1
  by_cases hs : 2 ≤ Fintype.card (Function.fixedPoints x)
  · obtain ⟨r0, hr0, hr0χ, hr02⟩ :=
      exists_odd_involution_mem_cycleRotationSubgroup x hx
    obtain ⟨i0, hi0, hi0χ, hi02⟩ :=
      exists_odd_involution_mem_fixedPointPermutationSubgroup x hs
    let t : χ.ker := ⟨i0 * r0, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hr0χ]
      norm_num⟩
    have hdecomp := signKernel_decomp_rotation_odd_pair χ R L I hLχ
      hLnorm hIcomm hsup r0 i0 hr0 hi0 hr0χ hi0χ hr02 hi02
    refine ⟨t, hdecomp.1, hdecomp.2, ?_⟩
    intro hsle
    omega
  · have hsle : Fintype.card (Function.fixedPoints x) ≤ 1 := by omega
    have hIχ : I ≤ χ.ker :=
      fixedPointPermutationSubgroup_le_signKernel_of_card_le_one x hsle
    have hdecomp := signKernel_decomp_rotation_only χ R L I hLχ hIχ
      hLnorm hIcomm hsup
    refine ⟨1, ?_, by simp, fun _ => rfl⟩
    rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact hdecomp

end GLS3.Chapter5
/- END Theory.InvolutionSignKernelDecomposition -/

/- BEGIN Theory.EvenBlockCore1 -/
noncomputable section

/- Source: EvenBlockSubgroup.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # The parity-correlated two-block subgroup -/

/-- Pairs of block permutations whose block-diagonal permutation is even. -/
public abbrev evenBlockProductGroup (a b : Nat) :
    Subgroup (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) :=
  (alternatingGroup (Fin (a + b))).comap (permProdBlockHom a b)

/-- Faithful block-diagonal embedding of the parity-correlated product into
the ambient alternating group. -/
@[expose] public def evenBlockProductHom (a b : Nat) :
    evenBlockProductGroup a b →* alternatingGroup (Fin (a + b)) where
  toFun x := ⟨permProdBlockHom a b x, x.2⟩
  map_one' := by
    apply Subtype.ext
    change permProdBlockHom a b
      (1 : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) = 1
    exact map_one (permProdBlockHom a b)
  map_mul' x y := by
    apply Subtype.ext
    change permProdBlockHom a b
        ((x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) *
          (y : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))) =
      permProdBlockHom a b x * permProdBlockHom a b y
    exact map_mul (permProdBlockHom a b)
      (x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
      (y : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))

public theorem evenBlockProductHom_injective (a b : Nat) :
    Function.Injective (evenBlockProductHom a b) := by
  intro x y hxy
  apply Subtype.ext
  apply permProdBlockHom_injective a b
  exact congrArg Subtype.val hxy

@[simp]
public theorem coe_evenBlockProductHom_apply (a b : Nat)
    (x : evenBlockProductGroup a b) :
    ((evenBlockProductHom a b x : alternatingGroup (Fin (a + b))) :
      Equiv.Perm (Fin (a + b))) = permProdBlockHom a b x := by
  rfl

/-- The alternating product as a subgroup of the parity-correlated product. -/
@[expose] public def evenBlockAlternatingHom (a b : Nat) :
    alternatingGroup (Fin a) × alternatingGroup (Fin b) →*
      evenBlockProductGroup a b where
  toFun x := ⟨((x.1 : Equiv.Perm (Fin a)),
      (x.2 : Equiv.Perm (Fin b))), by
    change permProdBlockHom a b
      ((x.1 : Equiv.Perm (Fin a)), (x.2 : Equiv.Perm (Fin b))) ∈
        alternatingGroup (Fin (a + b))
    have hx := (alternatingProdBlockHom a b x).2
    change ((alternatingProdBlockHom a b x :
      alternatingGroup (Fin (a + b))) : Equiv.Perm (Fin (a + b))) ∈
        alternatingGroup (Fin (a + b)) at hx
    rw [coe_alternatingProdBlockHom_apply] at hx
    exact hx⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

public theorem evenBlockAlternatingHom_injective (a b : Nat) :
    Function.Injective (evenBlockAlternatingHom a b) := by
  intro x y hxy
  have hpair := congrArg (fun z : evenBlockProductGroup a b =>
    (z : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))) hxy
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hpair)
  · exact Subtype.ext (congrArg Prod.snd hpair)

public theorem evenBlockProductHom_comp_evenBlockAlternatingHom
    (a b : Nat) :
    (evenBlockProductHom a b).comp (evenBlockAlternatingHom a b) =
      alternatingProdBlockHom a b := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact (coe_alternatingProdBlockHom_apply a b x).symm

/-- Common component parity on the even block product.  Total evenness forces
the second component to have the same sign. -/
@[expose] public def evenBlockParityHom (a b : Nat) :
    evenBlockProductGroup a b →* ℤˣ :=
  Equiv.Perm.sign.comp
    ((MonoidHom.fst (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).comp
      (evenBlockProductGroup a b).subtype)

/-- The kernel of component parity is exactly `A_a × A_b`. -/
public theorem evenBlockParityHom_ker_eq_range (a b : Nat) :
    (evenBlockParityHom a b).ker = (evenBlockAlternatingHom a b).range := by
  ext x
  constructor
  · intro hx
    have hxA : Equiv.Perm.sign (x :
        Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1 = 1 := by
      exact MonoidHom.mem_ker.mp hx
    have htotal : Equiv.Perm.sign
        (permProdBlockHom a b (x :
          Equiv.Perm (Fin a) × Equiv.Perm (Fin b))) = 1 := by
      exact Equiv.Perm.mem_alternatingGroup.mp x.2
    have hprod : Equiv.Perm.sign
          (x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1 *
        Equiv.Perm.sign
          (x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2 = 1 := by
      rw [permProdBlockHom_apply, Equiv.Perm.sign_permCongr,
        Equiv.Perm.sign_sumCongr] at htotal
      exact htotal
    have hxB : Equiv.Perm.sign (x :
        Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2 = 1 := by
      rw [hxA, one_mul] at hprod
      exact hprod
    let xA : alternatingGroup (Fin a) :=
      ⟨(x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1,
        Equiv.Perm.mem_alternatingGroup.mpr hxA⟩
    let xB : alternatingGroup (Fin b) :=
      ⟨(x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2,
        Equiv.Perm.mem_alternatingGroup.mpr hxB⟩
    refine ⟨(xA, xB), ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    exact Equiv.Perm.mem_alternatingGroup.mp y.1.2

/-- If both blocks have at least two points, component parity realizes the
quotient of the even block product by `A_a × A_b` as the two-element sign
group. -/
public theorem evenBlockParityHom_surjective
    (a b : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) :
    Function.Surjective (evenBlockParityHom a b) := by
  let a0 : Fin a := ⟨0, by omega⟩
  let a1 : Fin a := ⟨1, by omega⟩
  let b0 : Fin b := ⟨0, by omega⟩
  let b1 : Fin b := ⟨1, by omega⟩
  have ha01 : a0 ≠ a1 := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  have hb01 : b0 ≠ b1 := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  let x : evenBlockProductGroup a b :=
    ⟨(Equiv.swap a0 a1, Equiv.swap b0 b1), by
      change permProdBlockHom a b
        (Equiv.swap a0 a1, Equiv.swap b0 b1) ∈
          alternatingGroup (Fin (a + b))
      rw [Equiv.Perm.mem_alternatingGroup]
      rw [permProdBlockHom_apply, Equiv.Perm.sign_permCongr,
        Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_swap ha01,
        Equiv.Perm.sign_swap hb01]
      norm_num⟩
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one (evenBlockParityHom a b)⟩
  · refine ⟨x, ?_⟩
    change Equiv.Perm.sign (Equiv.swap a0 a1) = -1
    exact Equiv.Perm.sign_swap ha01

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockSubextension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # Central extensions restricted to parity-correlated two-block groups -/

public abbrev evenBlockPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) : Subgroup H :=
  (evenBlockProductHom a b).range.comap f

@[expose] public noncomputable def evenBlockPreimageProjection
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    evenBlockPreimage a b f →* evenBlockProductGroup a b :=
  let i := evenBlockProductHom a b
  let e := MonoidHom.ofInjective (evenBlockProductHom_injective a b)
  e.symm.toMonoidHom.comp
    ((f.comp (evenBlockPreimage a b f).subtype).codRestrict
      i.range (fun x => x.2))

public theorem evenBlockPreimageProjection_surjective
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f) :
    Function.Surjective (evenBlockPreimageProjection a b f) := by
  intro y
  let i := evenBlockProductHom a b
  let e := MonoidHom.ofInjective (evenBlockProductHom_injective a b)
  obtain ⟨x, hx⟩ := hf (i y)
  have hxE : x ∈ evenBlockPreimage a b f := ⟨y, hx.symm⟩
  let xE : evenBlockPreimage a b f := ⟨x, hxE⟩
  refine ⟨xE, ?_⟩
  change e.symm ⟨f x, hxE⟩ = y
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem evenBlockPreimageProjection_fac
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (x : evenBlockPreimage a b f) :
    evenBlockProductHom a b (evenBlockPreimageProjection a b f x) = f x := by
  let i := evenBlockProductHom a b
  let e := MonoidHom.ofInjective (evenBlockProductHom_injective a b)
  change i (e.symm ⟨f x, x.2⟩) = f x
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨f x, x.2⟩)
  exact h

public theorem evenBlockPreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    (evenBlockPreimageProjection a b f).ker =
      f.ker.comap (evenBlockPreimage a b f).subtype := by
  let i := evenBlockProductHom a b
  let e := MonoidHom.ofInjective (evenBlockProductHom_injective a b)
  let r0 := (f.comp (evenBlockPreimage a b f).subtype).codRestrict
    i.range (fun x => x.2)
  calc
    (evenBlockPreimageProjection a b f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = f.ker.comap (evenBlockPreimage a b f).subtype := by
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

public theorem evenBlockPreimageProjection_ker_le_center
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hker : f.ker ≤ Subgroup.center H) :
    (evenBlockPreimageProjection a b f).ker ≤
      Subgroup.center (evenBlockPreimage a b f) := by
  rw [evenBlockPreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y.1

/-- The parity quotient on the full parity-correlated block preimage. -/
@[expose] public noncomputable def evenBlockPreimageParity
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    evenBlockPreimage a b f →* ℤˣ :=
  (evenBlockParityHom a b).comp (evenBlockPreimageProjection a b f)

public theorem evenBlockPreimageParity_surjective
    {H : Type*} [Group H] (a b : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f) :
    Function.Surjective (evenBlockPreimageParity a b f) :=
  (evenBlockParityHom_surjective a b ha2 hb2).comp
    (evenBlockPreimageProjection_surjective a b f hf)

/-- The kernel of parity in the full even-block preimage is exactly the
existing full preimage of the alternating product. -/
public theorem evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    (evenBlockPreimageParity a b f).ker =
      (alternatingBlockPreimage a b f).comap
        (evenBlockPreimage a b f).subtype := by
  ext x
  constructor
  · intro hx
    have hprojKer : evenBlockPreimageProjection a b f x ∈
        (evenBlockParityHom a b).ker := hx
    rw [evenBlockParityHom_ker_eq_range] at hprojKer
    obtain ⟨y, hy⟩ := hprojKer
    change f (x : H) ∈ (alternatingProdBlockHom a b).range
    refine ⟨y, ?_⟩
    calc
      alternatingProdBlockHom a b y =
          evenBlockProductHom a b (evenBlockAlternatingHom a b y) := by
        exact (DFunLike.congr_fun
          (evenBlockProductHom_comp_evenBlockAlternatingHom a b) y).symm
      _ = evenBlockProductHom a b
          (evenBlockPreimageProjection a b f x) := by rw [hy]
      _ = f x := evenBlockPreimageProjection_fac a b f x
  · intro hx
    change f (x : H) ∈ (alternatingProdBlockHom a b).range at hx
    obtain ⟨y, hy⟩ := hx
    have hproj : evenBlockPreimageProjection a b f x =
        evenBlockAlternatingHom a b y := by
      apply evenBlockProductHom_injective a b
      calc
        evenBlockProductHom a b (evenBlockPreimageProjection a b f x) = f x :=
          evenBlockPreimageProjection_fac a b f x
        _ = alternatingProdBlockHom a b y := hy.symm
        _ = evenBlockProductHom a b (evenBlockAlternatingHom a b y) := by
          exact (DFunLike.congr_fun
            (evenBlockProductHom_comp_evenBlockAlternatingHom a b) y).symm
    rw [MonoidHom.mem_ker]
    change evenBlockParityHom a b
      (evenBlockPreimageProjection a b f x) = 1
    rw [hproj]
    have hyRange : evenBlockAlternatingHom a b y ∈
        (evenBlockAlternatingHom a b).range := ⟨y, rfl⟩
    rw [← evenBlockParityHom_ker_eq_range] at hyRange
    exact MonoidHom.mem_ker.mp hyRange

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockComponentLift.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open RootFourSubgroup

/-- Paired cardinal and root-square information for the left component of an
alternating two-block central extension. -/
public theorem evenBlock_leftComponent_pair_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (hA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)).ker ≤ 2 ∧
      ∃ u : prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f),
        prodLeftPreimageDerivedProjection
            (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) u =
          (⟨rho1 qA, rho1_mem_alternating qA⟩ :
            alternatingGroup (Fin (qA + 5))) ∧
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)).ker =
            Subgroup.zpowers (u ^ 2) := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective _ _ f hf
  have hrker : r.ker ≤ Subgroup.center
      (alternatingBlockPreimage (qA + 5) (qB + 5) f) :=
    alternatingBlockPreimageProjection_ker_le_center _ _ f hker
  exact
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      qA hA (prodLeftPreimageProjection r)
      (prodLeftPreimageProjection_surjective r hr)
      (prodLeftPreimageProjection_ker_le_center r hrker)

/-- Paired cardinal and root-square information for the right component of an
alternating two-block central extension. -/
public theorem evenBlock_rightComponent_pair_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (hB : Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (prodRightPreimageDerivedProjection
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)).ker ≤ 2 ∧
      ∃ u : prodRightPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f),
        prodRightPreimageDerivedProjection
            (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) u =
          (⟨rho1 qB, rho1_mem_alternating qB⟩ :
            alternatingGroup (Fin (qB + 5))) ∧
        (prodRightPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)).ker =
            Subgroup.zpowers (u ^ 2) := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective _ _ f hf
  have hrker : r.ker ≤ Subgroup.center
      (alternatingBlockPreimage (qA + 5) (qB + 5) f) :=
    alternatingBlockPreimageProjection_ker_le_center _ _ f hker
  exact
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      qB hB (prodRightPreimageProjection r)
      (prodRightPreimageProjection_surjective r hr)
      (prodRightPreimageProjection_ker_le_center r hrker)

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockKernelFusion.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- The alternating-product embedding recovers the ambient image of the
restricted block projection. -/
public theorem alternatingBlockPreimageProjection_fac
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (x : alternatingBlockPreimage a b f) :
    alternatingProdBlockHom a b
        (alternatingBlockPreimageProjection a b f x) = f x := by
  let i := alternatingProdBlockHom a b
  let e := MonoidHom.ofInjective (alternatingProdBlockHom_injective a b)
  change i (e.symm ⟨f x, x.2⟩) = f x
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨f x, x.2⟩)
  exact h

/-- Inclusion of the left component-derived preimage back into the original
ambient extension group. -/
@[expose] public def evenBlockLeftDerivedEmbedding
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    prodLeftPreimageDerived (alternatingBlockPreimageProjection a b f) →* H :=
  (alternatingBlockPreimage a b f).subtype.comp
    ((prodLeftPreimage (alternatingBlockPreimageProjection a b f)).subtype.comp
      (prodLeftPreimageDerived
        (alternatingBlockPreimageProjection a b f)).subtype)

/-- Inclusion of the right component-derived preimage back into the original
ambient extension group. -/
@[expose] public def evenBlockRightDerivedEmbedding
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    prodRightPreimageDerived (alternatingBlockPreimageProjection a b f) →* H :=
  (alternatingBlockPreimage a b f).subtype.comp
    ((prodRightPreimage (alternatingBlockPreimageProjection a b f)).subtype.comp
      (prodRightPreimageDerived
        (alternatingBlockPreimageProjection a b f)).subtype)

/-- The left component-derived covering kernel, viewed inside the original
ambient extension group. -/
public abbrev evenBlockLeftDerivedKernel
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) : Subgroup H :=
  (prodLeftPreimageDerivedProjection
    (alternatingBlockPreimageProjection a b f)).ker.map
      (evenBlockLeftDerivedEmbedding a b f)

/-- The right component-derived covering kernel, viewed inside the original
ambient extension group. -/
public abbrev evenBlockRightDerivedKernel
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) : Subgroup H :=
  (prodRightPreimageDerivedProjection
    (alternatingBlockPreimageProjection a b f)).ker.map
      (evenBlockRightDerivedEmbedding a b f)

public theorem evenBlockLeftDerivedKernel_le_ker
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    evenBlockLeftDerivedKernel a b f ≤ f.ker := by
  let r := alternatingBlockPreimageProjection a b f
  rintro z ⟨x, hx, rfl⟩
  have hrx : r (((x : prodLeftPreimageDerived r) : prodLeftPreimage r) :
      alternatingBlockPreimage a b f) = 1 := by
    apply Prod.ext
    · exact MonoidHom.mem_ker.mp hx
    · exact Subgroup.mem_bot.mp x.1.2.2
  have hxker : ((x : prodLeftPreimageDerived r) : prodLeftPreimage r).1 ∈
      r.ker := MonoidHom.mem_ker.mpr hrx
  rw [alternatingBlockPreimageProjection_ker_eq_comap] at hxker
  exact hxker

public theorem evenBlockRightDerivedKernel_le_ker
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    evenBlockRightDerivedKernel a b f ≤ f.ker := by
  let r := alternatingBlockPreimageProjection a b f
  rintro z ⟨x, hx, rfl⟩
  have hrx : r (((x : prodRightPreimageDerived r) : prodRightPreimage r) :
      alternatingBlockPreimage a b f) = 1 := by
    apply Prod.ext
    · exact Subgroup.mem_bot.mp x.1.2.1
    · exact MonoidHom.mem_ker.mp hx
  have hxker : ((x : prodRightPreimageDerived r) : prodRightPreimage r).1 ∈
      r.ker := MonoidHom.mem_ker.mpr hrx
  rw [alternatingBlockPreimageProjection_ker_eq_comap] at hxker
  exact hxker

/-- A1's fusion calculation in an abstract exact-conjugacy form.  If the two
component kernels are generated by squares and the chosen generators are
ambient-conjugate, the two kernels have the same image in the global central
kernel. -/
public theorem evenBlock_componentDerivedKernel_eq_of_conjugate_generators
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hker : f.ker ≤ Subgroup.center H)
    (yL : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection a b f))
    (yR : prodRightPreimageDerived
      (alternatingBlockPreimageProjection a b f))
    (hL : (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection a b f)).ker =
        Subgroup.zpowers (yL ^ 2))
    (hR : (prodRightPreimageDerivedProjection
      (alternatingBlockPreimageProjection a b f)).ker =
        Subgroup.zpowers (yR ^ 2))
    (d : H)
    (hconj : d * evenBlockLeftDerivedEmbedding a b f yL * d⁻¹ =
      evenBlockRightDerivedEmbedding a b f yR) :
    evenBlockLeftDerivedKernel a b f =
      evenBlockRightDerivedKernel a b f := by
  have hyL2ker : yL ^ 2 ∈ (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection a b f)).ker := by
    rw [hL]
    exact Subgroup.mem_zpowers (yL ^ 2)
  have hyL2global : evenBlockLeftDerivedEmbedding a b f (yL ^ 2) ∈ f.ker :=
    evenBlockLeftDerivedKernel_le_ker a b f
      ⟨yL ^ 2, hyL2ker, rfl⟩
  have hyL2center : evenBlockLeftDerivedEmbedding a b f (yL ^ 2) ∈
      Subgroup.center H := hker hyL2global
  have hfixed : d * evenBlockLeftDerivedEmbedding a b f (yL ^ 2) * d⁻¹ =
      evenBlockLeftDerivedEmbedding a b f (yL ^ 2) := by
    have hc := Subgroup.mem_center_iff.mp hyL2center d
    rw [hc]
    simp
  have hsq : evenBlockLeftDerivedEmbedding a b f (yL ^ 2) =
      evenBlockRightDerivedEmbedding a b f (yR ^ 2) := by
    calc
      evenBlockLeftDerivedEmbedding a b f (yL ^ 2) =
          d * evenBlockLeftDerivedEmbedding a b f (yL ^ 2) * d⁻¹ :=
        hfixed.symm
      _ = (d * evenBlockLeftDerivedEmbedding a b f yL * d⁻¹) ^ 2 := by
        rw [map_pow]
        simp [pow_two, mul_assoc]
      _ = (evenBlockRightDerivedEmbedding a b f yR) ^ 2 := by rw [hconj]
      _ = evenBlockRightDerivedEmbedding a b f (yR ^ 2) := by rw [map_pow]
  change (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection a b f)).ker.map
        (evenBlockLeftDerivedEmbedding a b f) =
    (prodRightPreimageDerivedProjection
      (alternatingBlockPreimageProjection a b f)).ker.map
        (evenBlockRightDerivedEmbedding a b f)
  rw [hL, hR, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hsq]

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockEqualSwap.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- An ambient lift of an equal-block swap carries a left component-derived
element to an exactly conjugate right component-derived element. -/
public theorem exists_rightDerived_conjugate_of_equalBlockSwap
    {H : Type*} [Group H] (a : Nat)
    (f : H →* alternatingGroup (Fin (a + a)))
    (s : alternatingGroup (Fin (a + a)))
    (hswap : ∀ x : alternatingGroup (Fin a),
      s * alternatingProdBlockHom a a (x, 1) * s⁻¹ =
        alternatingProdBlockHom a a (1, x))
    (d : H) (hd : f d = s)
    (yL : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection a a f)) :
    ∃ yR : prodRightPreimageDerived
        (alternatingBlockPreimageProjection a a f),
      prodRightPreimageDerivedProjection
          (alternatingBlockPreimageProjection a a f) yR =
        prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection a a f) yL ∧
      d * evenBlockLeftDerivedEmbedding a a f yL * d⁻¹ =
        evenBlockRightDerivedEmbedding a a f yR := by
  let E := alternatingBlockPreimage a a f
  let r := alternatingBlockPreimageProjection a a f
  let EL := prodLeftPreimage r
  let ER := prodRightPreimage r
  let iL : EL →* H := E.subtype.comp EL.subtype
  have hxproj (x : EL) : r (x : E) =
      (prodLeftPreimageProjection r x, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp x.2.2
  have hximage (x : EL) : f (iL x) =
      alternatingProdBlockHom a a (prodLeftPreimageProjection r x, 1) := by
    calc
      f (iL x) = alternatingProdBlockHom a a (r (x : E)) :=
        (alternatingBlockPreimageProjection_fac a a f (x : E)).symm
      _ = alternatingProdBlockHom a a
          (prodLeftPreimageProjection r x, 1) := by rw [hxproj]
  have hzmem (x : EL) : d * iL x * d⁻¹ ∈ E := by
    change f (d * iL x * d⁻¹) ∈ (alternatingProdBlockHom a a).range
    refine ⟨(1, prodLeftPreimageProjection r x), ?_⟩
    rw [map_mul, map_mul, map_inv, hd, hximage]
    exact (hswap (prodLeftPreimageProjection r x)).symm
  let zE (x : EL) : E := ⟨d * iL x * d⁻¹, hzmem x⟩
  have hzproj (x : EL) : r (zE x) =
      (1, prodLeftPreimageProjection r x) := by
    apply alternatingProdBlockHom_injective a a
    calc
      alternatingProdBlockHom a a (r (zE x)) = f (zE x) :=
        alternatingBlockPreimageProjection_fac a a f (zE x)
      _ = s * alternatingProdBlockHom a a
          (prodLeftPreimageProjection r x, 1) * s⁻¹ := by
        change f (d * iL x * d⁻¹) = _
        rw [map_mul, map_mul, map_inv, hd, hximage]
      _ = alternatingProdBlockHom a a
          (1, prodLeftPreimageProjection r x) :=
        hswap (prodLeftPreimageProjection r x)
  have hzER (x : EL) : zE x ∈ ER := by
    change r (zE x) ∈ prodRightFactor
      (alternatingGroup (Fin a)) (alternatingGroup (Fin a))
    rw [hzproj]
    exact ⟨Subgroup.mem_bot.mpr rfl, trivial⟩
  let φ : EL →* ER := {
    toFun := fun x => ⟨zE x, hzER x⟩
    map_one' := by
      apply Subtype.ext
      apply Subtype.ext
      simp [zE, iL]
    map_mul' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      change d * iL (x * y) * d⁻¹ =
        (d * iL x * d⁻¹) * (d * iL y * d⁻¹)
      rw [map_mul]
      group
  }
  have hmap : (commutator EL).map φ ≤ commutator ER := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hyRmem : φ (yL : EL) ∈ commutator ER := by
    apply hmap
    exact ⟨(yL : EL), yL.2, rfl⟩
  let yR : prodRightPreimageDerived r := ⟨φ (yL : EL), hyRmem⟩
  refine ⟨yR, ?_, rfl⟩
  change (r (zE (yL : EL))).2 = (r (yL.1.1 : E)).1
  rw [hzproj]
  rfl

/-- Conditional equal-block fusion endpoint: once an even block-swap
permutation is supplied, the two component-derived kernels have the same image
in the ambient central kernel. -/
public theorem evenBlock_equalComponentDerivedKernel_eq_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (s : alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hswap : ∀ x : alternatingGroup (Fin (q + 5)),
      s * alternatingProdBlockHom (q + 5) (q + 5) (x, 1) * s⁻¹ =
        alternatingProdBlockHom (q + 5) (q + 5) (1, x))
    (d : H) (hd : f d = s) :
    evenBlockLeftDerivedKernel (q + 5) (q + 5) f =
      evenBlockRightDerivedKernel (q + 5) (q + 5) f := by
  obtain ⟨hLcard, yL, hyL, hL⟩ :=
    evenBlock_leftComponent_pair_of_multiplier_le_two q q hM f hf hker
  obtain ⟨hRcard, yR0, hyR0, hR0⟩ :=
    evenBlock_rightComponent_pair_of_multiplier_le_two q q hM f hf hker
  obtain ⟨yR, hyR, hconj⟩ :=
    exists_rightDerived_conjugate_of_equalBlockSwap
      (q + 5) f s hswap d hd yL
  let r := alternatingBlockPreimageProjection (q + 5) (q + 5) f
  let rR := prodRightPreimageDerivedProjection r
  have hrker : r.ker ≤ Subgroup.center
      (alternatingBlockPreimage (q + 5) (q + 5) f) :=
    alternatingBlockPreimageProjection_ker_le_center _ _ f hker
  have hrRcenter : rR.ker ≤ Subgroup.center (prodRightPreimageDerived r) := by
    intro x hx
    have hx' : (x : prodRightPreimage r) ∈
        (prodRightPreimageProjection r).ker := hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (prodRightPreimageProjection_ker_le_center r hrker hx') y
  have hsq : yR ^ 2 = yR0 ^ 2 :=
    sq_eq_sq_of_apply_eq_of_card_ker_le_two rR hrRcenter hRcard
      (hyR.trans (hyL.trans hyR0.symm))
  have hR : rR.ker = Subgroup.zpowers (yR ^ 2) := by
    rw [hR0, hsq]
  exact evenBlock_componentDerivedKernel_eq_of_conjugate_generators
    (q + 5) (q + 5) f hker yL yR hL hR d hconj

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockSwapPerm.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- Coordinates identifying two equal blocks with `Fin 2 × Fin a`. -/
public def finTwoProdEquivSum (a : Nat) :
    Fin 2 × Fin a ≃ Fin a ⊕ Fin a :=
  (finTwoEquiv.prodCongr (Equiv.refl (Fin a))).trans
    (Equiv.boolProdEquivSum (Fin a))

/-- The permutation interchanging two equal consecutive blocks. -/
@[expose] public def equalBlockSwapPerm (a : Nat) : Equiv.Perm (Fin (a + a)) :=
  (finSumFinEquiv (m := a) (n := a)).permCongr
    (Equiv.sumComm (Fin a) (Fin a))

public theorem sign_equalBlockSwapPerm (a : Nat) :
    Equiv.Perm.sign (equalBlockSwapPerm a) = (-1 : ℤˣ) ^ a := by
  have hsum : (Equiv.sumComm (Fin a) (Fin a) :
      Equiv.Perm (Fin a ⊕ Fin a)) =
      (finTwoProdEquivSum a).permCongr
        (blockTopPermHom (Fin 2) (Fin a)
          (Equiv.swap (0 : Fin 2) (1 : Fin 2))) := by
    ext z
    rcases z with z | z <;>
      simp [finTwoProdEquivSum, blockTopPermHom] <;> decide
  rw [equalBlockSwapPerm, Equiv.Perm.sign_permCongr, hsum,
    Equiv.Perm.sign_permCongr]
  change Equiv.Perm.sign
      (Equiv.prodCongrLeft
        (fun _ : Fin a => Equiv.swap (0 : Fin 2) (1 : Fin 2))) = _
  rw [Equiv.Perm.sign_prodCongrLeft]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp [Equiv.Perm.sign_swap h01]

/-- The equal-block swap is even exactly when the block size is even. -/
public def equalBlockSwap (a : Nat) (ha : Even a) :
    alternatingGroup (Fin (a + a)) :=
  ⟨equalBlockSwapPerm a, by
    rw [Equiv.Perm.mem_alternatingGroup, sign_equalBlockSwapPerm]
    exact (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mpr ha⟩

public theorem equalBlockSwap_conj_left
    (a : Nat) (ha : Even a) (x : alternatingGroup (Fin a)) :
    equalBlockSwap a ha * alternatingProdBlockHom a a (x, 1) *
        (equalBlockSwap a ha)⁻¹ =
      alternatingProdBlockHom a a (1, x) := by
  apply Subtype.ext
  change (equalBlockSwap a ha : Equiv.Perm (Fin (a + a))) *
      (alternatingProdBlockHom a a (x, 1) : Equiv.Perm (Fin (a + a))) *
        ((equalBlockSwap a ha)⁻¹ : Equiv.Perm (Fin (a + a))) =
    (alternatingProdBlockHom a a (1, x) : Equiv.Perm (Fin (a + a)))
  rw [coe_alternatingProdBlockHom_apply, coe_alternatingProdBlockHom_apply]
  change equalBlockSwapPerm a *
      permProdBlockHom a a ((x : Equiv.Perm (Fin a)), 1) *
        (equalBlockSwapPerm a)⁻¹ =
    permProdBlockHom a a (1, (x : Equiv.Perm (Fin a)))
  have hsumconj :
      (Equiv.sumComm (Fin a) (Fin a) : Equiv.Perm (Fin a ⊕ Fin a)) *
          Equiv.sumCongr (x : Equiv.Perm (Fin a)) 1 *
          (Equiv.sumComm (Fin a) (Fin a))⁻¹ =
        Equiv.sumCongr 1 (x : Equiv.Perm (Fin a)) := by
    ext z
    rcases z with z | z <;> simp
  rw [equalBlockSwapPerm, permProdBlockHom_apply, permProdBlockHom_apply]
  change (finSumFinEquiv (m := a) (n := a)).permCongrHom
        (Equiv.sumComm (Fin a) (Fin a)) *
      (finSumFinEquiv (m := a) (n := a)).permCongrHom
        (Equiv.sumCongr (x : Equiv.Perm (Fin a)) 1) *
      ((finSumFinEquiv (m := a) (n := a)).permCongrHom
        (Equiv.sumComm (Fin a) (Fin a)))⁻¹ =
      (finSumFinEquiv (m := a) (n := a)).permCongrHom
        (Equiv.sumCongr 1 (x : Equiv.Perm (Fin a)))
  rw [← map_inv, ← map_mul, ← map_mul, hsumconj]

/-- Equal-block fusion with the concrete even block swap. -/
public theorem evenBlock_equalComponentDerivedKernel_eq_of_even_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (ha : Even (q + 5))
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    evenBlockLeftDerivedKernel (q + 5) (q + 5) f =
      evenBlockRightDerivedKernel (q + 5) (q + 5) f := by
  obtain ⟨d, hd⟩ := hf (equalBlockSwap (q + 5) ha)
  exact evenBlock_equalComponentDerivedKernel_eq_of_multiplier_le_two
    q hM f hf hker (equalBlockSwap (q + 5) ha)
      (equalBlockSwap_conj_left (q + 5) ha) d hd

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockUnequalSwap.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

public def sixTailFinEquiv (q : Nat) (hq : 1 ≤ q) :
    Fin 6 ⊕ Fin (q - 1) ≃ Fin (q + 5) :=
  finSumFinEquiv.trans (finCongr (by omega))

public def rootTailUngroupEquiv (α β γ δ : Type*) :
    (α ⊕ γ) ⊕ (β ⊕ δ) ≃ (α ⊕ β) ⊕ (γ ⊕ δ) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr x) => Sum.inr (Sum.inl x)
    | Sum.inr (Sum.inl x) => Sum.inl (Sum.inr x)
    | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr x)
  invFun
    | Sum.inl (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inl (Sum.inr x) => Sum.inr (Sum.inl x)
    | Sum.inr (Sum.inl x) => Sum.inl (Sum.inr x)
    | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr x)
  left_inv x := by rcases x with (x | x) | (x | x) <;> rfl
  right_inv x := by rcases x with (x | x) | (x | x) <;> rfl

public def unequalSixSwapCore (rA rB : Nat) :
    Equiv.Perm ((Fin 6 ⊕ Fin rA) ⊕ (Fin 6 ⊕ Fin rB)) :=
  (rootTailUngroupEquiv (Fin 6) (Fin rA) (Fin 6) (Fin rB)).permCongr
    (Equiv.Perm.sumCongr (Equiv.sumComm (Fin 6) (Fin 6)) 1)

public def unequalSixBlockEquiv (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB) :
    (Fin 6 ⊕ Fin (qA - 1)) ⊕ (Fin 6 ⊕ Fin (qB - 1)) ≃
      Fin ((qA + 5) + (qB + 5)) :=
  (Equiv.sumCongr (sixTailFinEquiv qA hA) (sixTailFinEquiv qB hB)).trans
    finSumFinEquiv

public def unequalSixSwapPerm (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB) :
    Equiv.Perm (Fin ((qA + 5) + (qB + 5))) :=
  (unequalSixBlockEquiv qA qB hA hB).permCongr
    (unequalSixSwapCore (qA - 1) (qB - 1))

public theorem sign_sumComm_fin_six :
    Equiv.Perm.sign (Equiv.sumComm (Fin 6) (Fin 6)) = 1 := by
  have h := sign_equalBlockSwapPerm 6
  rw [equalBlockSwapPerm, Equiv.Perm.sign_permCongr] at h
  exact h

public theorem sign_unequalSixSwapCore (rA rB : Nat) :
    Equiv.Perm.sign (unequalSixSwapCore rA rB) = 1 := by
  rw [unequalSixSwapCore, Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_sumCongr, sign_sumComm_fin_six]
  simp

public theorem sign_unequalSixSwapPerm
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB) :
    Equiv.Perm.sign (unequalSixSwapPerm qA qB hA hB) = 1 := by
  rw [unequalSixSwapPerm, Equiv.Perm.sign_permCongr,
    sign_unequalSixSwapCore]

public def unequalSixSwap
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB) :
    alternatingGroup (Fin ((qA + 5) + (qB + 5))) :=
  ⟨unequalSixSwapPerm qA qB hA hB, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_unequalSixSwapPerm]⟩

public def firstFiveEmbeddingSix : Fin 5 ↪ Fin 6 :=
  ⟨fun i => ⟨i, by omega⟩, by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 6 => x.val) h⟩

public def firstFivePermSix (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 6) :=
  Equiv.Perm.viaEmbeddingHom firstFiveEmbeddingSix σ

public theorem tailPermHom_five_eq_sixTail
    (q : Nat) (hq : 1 ≤ q) (σ : Equiv.Perm (Fin 5)) :
    RootAm.tailPermHom q 5 (by omega) σ =
      (sixTailFinEquiv q hq).permCongr
        (Equiv.Perm.sumCongr (firstFivePermSix σ) 1) := by
  apply Equiv.Perm.ext
  intro x
  obtain ⟨x, rfl⟩ := (sixTailFinEquiv q hq).surjective x
  rcases x with i | t
  · by_cases hi : i.val < 5
    · let j : Fin 5 := ⟨i.val, hi⟩
      have hij : i = firstFiveEmbeddingSix j := by
        apply Fin.ext
        rfl
      rw [hij]
      have hcoord (k : Fin 5) :
          sixTailFinEquiv q hq (Sum.inl (firstFiveEmbeddingSix k)) =
            RootAm.tailEmbedding q 5 (by omega) k := by
        apply Fin.ext
        rfl
      calc
        RootAm.tailPermHom q 5 (by omega) σ
            (sixTailFinEquiv q hq
              (Sum.inl (firstFiveEmbeddingSix j))) =
            RootAm.tailEmbedding q 5 (by omega) (σ j) := by
          rw [hcoord, RootAm.tailPermHom,
            Equiv.Perm.viaEmbeddingHom_apply]
          exact Equiv.Perm.viaEmbedding_apply σ
            (RootAm.tailEmbedding q 5 (by omega)) j
        _ = sixTailFinEquiv q hq
            (Sum.inl (firstFiveEmbeddingSix (σ j))) := (hcoord (σ j)).symm
        _ = (sixTailFinEquiv q hq).permCongr
            (Equiv.Perm.sumCongr (firstFivePermSix σ) 1)
              (sixTailFinEquiv q hq
                (Sum.inl (firstFiveEmbeddingSix j))) := by
          simp [Equiv.permCongr_apply, firstFivePermSix,
            Equiv.Perm.viaEmbeddingHom_apply,
            Equiv.Perm.viaEmbedding_apply]
    · have hi5 : i.val = 5 := by omega
      have hiRange :
          (sixTailFinEquiv q hq (Sum.inl i) : Fin (q + 5)) ∉
            Set.range (RootAm.tailEmbedding q 5 (by omega)) := by
        rintro ⟨j, hj⟩
        have := congrArg Fin.val hj
        simp [sixTailFinEquiv, RootAm.tailEmbedding] at this
        omega
      have hiRange6 : i ∉ Set.range firstFiveEmbeddingSix := by
        rintro ⟨j, hj⟩
        have hval := congrArg Fin.val hj
        change j.val = i.val at hval
        have hjlt : j.val < 5 := j.isLt
        omega
      rw [RootAm.tailPermHom, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem σ
          (RootAm.tailEmbedding q 5 (by omega)) _ hiRange]
      simp [firstFivePermSix, sixTailFinEquiv,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem σ firstFiveEmbeddingSix _ hiRange6]
  · have htRange :
        (sixTailFinEquiv q hq (Sum.inr t) : Fin (q + 5)) ∉
          Set.range (RootAm.tailEmbedding q 5 (by omega)) := by
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp [sixTailFinEquiv, RootAm.tailEmbedding] at this
      omega
    rw [RootAm.tailPermHom, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem σ
        (RootAm.tailEmbedding q 5 (by omega)) _ htRange]
    simp [sixTailFinEquiv]

public theorem unequalSixSwapCore_conj_left
    (rA rB : Nat) (σ : Equiv.Perm (Fin 6)) :
    unequalSixSwapCore rA rB *
        Equiv.Perm.sumCongr (Equiv.Perm.sumCongr σ 1) 1 *
        (unequalSixSwapCore rA rB)⁻¹ =
      Equiv.Perm.sumCongr 1 (Equiv.Perm.sumCongr σ 1) := by
  let e := rootTailUngroupEquiv (Fin 6) (Fin rA) (Fin 6) (Fin rB)
  let c : Equiv.Perm ((Fin 6 ⊕ Fin 6) ⊕ (Fin rA ⊕ Fin rB)) :=
    Equiv.Perm.sumCongr (Equiv.sumComm (Fin 6) (Fin 6)) 1
  let l : Equiv.Perm ((Fin 6 ⊕ Fin 6) ⊕ (Fin rA ⊕ Fin rB)) :=
    Equiv.Perm.sumCongr (Equiv.Perm.sumCongr σ 1) 1
  let r : Equiv.Perm ((Fin 6 ⊕ Fin 6) ⊕ (Fin rA ⊕ Fin rB)) :=
    Equiv.Perm.sumCongr (Equiv.Perm.sumCongr 1 σ) 1
  have hl : e.permCongr l =
      Equiv.Perm.sumCongr (Equiv.Perm.sumCongr σ 1) 1 := by
    ext x
    rcases x with (x | x) | (x | x) <;>
      simp [e, l, rootTailUngroupEquiv]
  have hr : e.permCongr r =
      Equiv.Perm.sumCongr 1 (Equiv.Perm.sumCongr σ 1) := by
    ext x
    rcases x with (x | x) | (x | x) <;>
      simp [e, r, rootTailUngroupEquiv]
  have hcore : c * l * c⁻¹ = r := by
    ext x
    rcases x with (x | x) | (x | x) <;> simp [c, l, r]
  rw [← hl, ← hr]
  change e.permCongrHom c * e.permCongrHom l *
      (e.permCongrHom c)⁻¹ = e.permCongrHom r
  rw [← map_inv, ← map_mul, ← map_mul, hcore]

public theorem permProdBlockHom_tail_five_left_eq_sixCoordinates
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (σ : Equiv.Perm (Fin 5)) :
    permProdBlockHom (qA + 5) (qB + 5)
        (RootAm.tailPermHom qA 5 (by omega) σ, 1) =
      (unequalSixBlockEquiv qA qB hA hB).permCongr
        (Equiv.Perm.sumCongr
          (Equiv.Perm.sumCongr (firstFivePermSix σ) 1) 1) := by
  rw [permProdBlockHom_apply, tailPermHom_five_eq_sixTail qA hA σ]
  apply Equiv.Perm.ext
  intro x
  obtain ⟨x, rfl⟩ := (unequalSixBlockEquiv qA qB hA hB).surjective x
  rcases x with (x | x) | (x | x) <;>
    simp [unequalSixBlockEquiv, Equiv.permCongr_apply]

public theorem permProdBlockHom_tail_five_right_eq_sixCoordinates
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (σ : Equiv.Perm (Fin 5)) :
    permProdBlockHom (qA + 5) (qB + 5)
        (1, RootAm.tailPermHom qB 5 (by omega) σ) =
      (unequalSixBlockEquiv qA qB hA hB).permCongr
        (Equiv.Perm.sumCongr 1
          (Equiv.Perm.sumCongr (firstFivePermSix σ) 1)) := by
  rw [permProdBlockHom_apply, tailPermHom_five_eq_sixTail qB hB σ]
  apply Equiv.Perm.ext
  intro x
  obtain ⟨x, rfl⟩ := (unequalSixBlockEquiv qA qB hA hB).surjective x
  rcases x with (x | x) | (x | x) <;>
    simp [unequalSixBlockEquiv, Equiv.permCongr_apply]

public theorem unequalSixSwapPerm_conj_root
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (σ : Equiv.Perm (Fin 5)) :
    unequalSixSwapPerm qA qB hA hB *
        permProdBlockHom (qA + 5) (qB + 5)
          (RootAm.tailPermHom qA 5 (by omega) σ, 1) *
        (unequalSixSwapPerm qA qB hA hB)⁻¹ =
      permProdBlockHom (qA + 5) (qB + 5)
        (1, RootAm.tailPermHom qB 5 (by omega) σ) := by
  rw [permProdBlockHom_tail_five_left_eq_sixCoordinates qA qB hA hB σ,
    permProdBlockHom_tail_five_right_eq_sixCoordinates qA qB hA hB σ]
  let e := unequalSixBlockEquiv qA qB hA hB
  let c := unequalSixSwapCore (qA - 1) (qB - 1)
  let l : Equiv.Perm
      ((Fin 6 ⊕ Fin (qA - 1)) ⊕ (Fin 6 ⊕ Fin (qB - 1))) :=
    Equiv.Perm.sumCongr
      (Equiv.Perm.sumCongr (firstFivePermSix σ) 1) 1
  let r : Equiv.Perm
      ((Fin 6 ⊕ Fin (qA - 1)) ⊕ (Fin 6 ⊕ Fin (qB - 1))) :=
    Equiv.Perm.sumCongr 1
      (Equiv.Perm.sumCongr (firstFivePermSix σ) 1)
  have hcore : c * l * c⁻¹ = r :=
    unequalSixSwapCore_conj_left (qA - 1) (qB - 1)
      (firstFivePermSix σ)
  change e.permCongrHom c * e.permCongrHom l *
      (e.permCongrHom c)⁻¹ = e.permCongrHom r
  rw [← map_inv, ← map_mul, ← map_mul, hcore]

public theorem unequalSixSwap_conj_root
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (x : alternatingGroup (Fin 5)) :
    unequalSixSwap qA qB hA hB *
        alternatingProdBlockHom (qA + 5) (qB + 5)
          (RootAm.tailAltHom qA 5 (by omega) x, 1) *
        (unequalSixSwap qA qB hA hB)⁻¹ =
      alternatingProdBlockHom (qA + 5) (qB + 5)
        (1, RootAm.tailAltHom qB 5 (by omega) x) := by
  apply Subtype.ext
  change (unequalSixSwap qA qB hA hB :
      Equiv.Perm (Fin ((qA + 5) + (qB + 5)))) *
      (alternatingProdBlockHom (qA + 5) (qB + 5)
        (RootAm.tailAltHom qA 5 (by omega) x, 1) :
        Equiv.Perm (Fin ((qA + 5) + (qB + 5)))) *
      ((unequalSixSwap qA qB hA hB)⁻¹ :
        Equiv.Perm (Fin ((qA + 5) + (qB + 5)))) =
    (alternatingProdBlockHom (qA + 5) (qB + 5)
      (1, RootAm.tailAltHom qB 5 (by omega) x) :
      Equiv.Perm (Fin ((qA + 5) + (qB + 5))))
  rw [coe_alternatingProdBlockHom_apply,
    coe_alternatingProdBlockHom_apply]
  change unequalSixSwapPerm qA qB hA hB *
      permProdBlockHom (qA + 5) (qB + 5)
        (RootAm.tailPermHom qA 5 (by omega) x.1, 1) *
      (unequalSixSwapPerm qA qB hA hB)⁻¹ =
    permProdBlockHom (qA + 5) (qB + 5)
      (1, RootAm.tailPermHom qB 5 (by omega) x.1)
  exact unequalSixSwapPerm_conj_root qA qB hA hB x.1

public theorem tailAltHom_rho1 (q : Nat) :
    RootAm.tailAltHom q 5 (by omega)
        (⟨RootFourSubgroup.rho1 0,
          RootFourSubgroup.rho1_mem_alternating 0⟩ :
          alternatingGroup (Fin 5)) =
      (⟨RootFourSubgroup.rho1 q,
        RootFourSubgroup.rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))) := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  change RootAm.tailPermHom q 5 (by omega) (RootFourSubgroup.rho1 0)
      (⟨x, hx⟩ : Fin (q + 5)) =
    RootFourSubgroup.rho1 q (⟨x, hx⟩ : Fin (q + 5))
  by_cases h5 : 5 ≤ x
  · have hRange : (⟨x, hx⟩ : Fin (q + 5)) ∉
        Set.range (RootAm.tailEmbedding q 5 (by omega)) := by
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp [RootAm.tailEmbedding] at this
      omega
    rw [RootAm.tailPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hRange]
    have h01 : (⟨x, hx⟩ : Fin (q + 5)) ≠ RootFourSubgroup.p0 q := by
      intro h
      have := congrArg Fin.val h
      simp [RootFourSubgroup.p0] at this
      omega
    have h11 : (⟨x, hx⟩ : Fin (q + 5)) ≠ RootFourSubgroup.p1 q := by
      intro h
      have := congrArg Fin.val h
      simp [RootFourSubgroup.p1] at this
      omega
    have h21 : (⟨x, hx⟩ : Fin (q + 5)) ≠ RootFourSubgroup.p2 q := by
      intro h
      have := congrArg Fin.val h
      simp [RootFourSubgroup.p2] at this
      omega
    have h31 : (⟨x, hx⟩ : Fin (q + 5)) ≠ RootFourSubgroup.p3 q := by
      intro h
      have := congrArg Fin.val h
      simp [RootFourSubgroup.p3] at this
      omega
    simp [RootFourSubgroup.rho1,
      Equiv.swap_apply_of_ne_of_ne h21 h31,
      Equiv.swap_apply_of_ne_of_ne h01 h11]
  · have hxlt : x < 5 := by omega
    interval_cases x <;>
      rw [RootAm.tailPermHom, Equiv.Perm.viaEmbeddingHom_apply,
        show (⟨_, hx⟩ : Fin (q + 5)) =
            RootAm.tailEmbedding q 5 (by omega) (⟨_, by omega⟩ : Fin 5) by
          apply Fin.ext
          rfl,
        Equiv.Perm.viaEmbedding_apply] <;>
      apply Fin.ext <;>
      simp [RootAm.tailEmbedding, RootFourSubgroup.rho1,
        RootFourSubgroup.p0, RootFourSubgroup.p1,
        RootFourSubgroup.p2, RootFourSubgroup.p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]

public def evenBlockLeftRootDerivedEmbedding
    {H : Type} [Group H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5)))) :
    centralRootAmPreimageDerived qA 5 (by omega)
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) →* H :=
  (evenBlockLeftDerivedEmbedding (qA + 5) (qB + 5) f).comp
    ((centralRootAmPreimage qA 5 (by omega)
      (prodLeftPreimageDerivedProjection
        (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f))).subtype.comp
      (centralRootAmPreimageDerived qA 5 (by omega)
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection
            (qA + 5) (qB + 5) f))).subtype)

public theorem exists_rightDerived_conjugate_of_unequalSixSwap
    {H : Type} [Group H]
    (qA qB : Nat) (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (d : H) (hd : f d = unequalSixSwap qA qB hA hB)
    (xL : centralRootAmPreimageDerived qA 5 (by omega)
      (prodLeftPreimageDerivedProjection
        (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f))) :
    ∃ yR : prodRightPreimageDerived
        (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f),
      prodRightPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) yR =
        RootAm.tailAltHom qB 5 (by omega)
          (centralRootAmPreimageDerivedProjection qA 5 (by omega)
            (prodLeftPreimageDerivedProjection
              (alternatingBlockPreimageProjection
                (qA + 5) (qB + 5) f)) xL) ∧
      d * evenBlockLeftRootDerivedEmbedding qA qB f xL * d⁻¹ =
        evenBlockRightDerivedEmbedding (qA + 5) (qB + 5) f yR := by
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let EL := prodLeftPreimage r
  let ER := prodRightPreimage r
  let DL := prodLeftPreimageDerived r
  let DR := prodRightPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let R := centralRootAmPreimage qA 5 (by omega) rL
  let RD := centralRootAmPreimageDerived qA 5 (by omega) rL
  let rRoot := centralRootAmPreimageDerivedProjection qA 5 (by omega) rL
  let iL : DL →* H := evenBlockLeftDerivedEmbedding (qA + 5) (qB + 5) f
  let iRoot : R →* H := iL.comp R.subtype
  have hxproj (x : DL) : r (((x : DL) : EL) : E) = (rL x, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp x.1.2.2
  have hximage (x : DL) : f (iL x) =
      alternatingProdBlockHom (qA + 5) (qB + 5) (rL x, 1) := by
    calc
      f (iL x) = alternatingProdBlockHom (qA + 5) (qB + 5)
          (r (((x : DL) : EL) : E)) :=
        (alternatingBlockPreimageProjection_fac
          (qA + 5) (qB + 5) f (((x : DL) : EL) : E)).symm
      _ = alternatingProdBlockHom (qA + 5) (qB + 5) (rL x, 1) := by
        rw [hxproj]
  have hxroot (x : R) :
      RootAm.tailAltHom qA 5 (by omega)
          (centralRootAmPreimageProjection qA 5 (by omega) rL x) =
        rL (x : DL) := by
    let e := centralRootAmEquiv qA 5 (by omega)
    have h := congrArg Subtype.val
      (e.apply_symm_apply (⟨rL (x : DL), x.2⟩ : RootAm.rootAm qA 5 (by omega)))
    exact h
  have hximageRoot (x : R) : f (iRoot x) =
      alternatingProdBlockHom (qA + 5) (qB + 5)
        (RootAm.tailAltHom qA 5 (by omega)
          (centralRootAmPreimageProjection qA 5 (by omega) rL x), 1) := by
    rw [show iRoot x = iL (x : DL) by rfl, hximage, hxroot]
  have hzmem (x : R) : d * iRoot x * d⁻¹ ∈ E := by
    change f (d * iRoot x * d⁻¹) ∈
      (alternatingProdBlockHom (qA + 5) (qB + 5)).range
    refine ⟨(1, RootAm.tailAltHom qB 5 (by omega)
      (centralRootAmPreimageProjection qA 5 (by omega) rL x)), ?_⟩
    rw [map_mul, map_mul, map_inv, hd, hximageRoot]
    exact (unequalSixSwap_conj_root qA qB hA hB
      (centralRootAmPreimageProjection qA 5 (by omega) rL x)).symm
  let zE (x : R) : E := ⟨d * iRoot x * d⁻¹, hzmem x⟩
  have hzproj (x : R) : r (zE x) =
      (1, RootAm.tailAltHom qB 5 (by omega)
        (centralRootAmPreimageProjection qA 5 (by omega) rL x)) := by
    apply alternatingProdBlockHom_injective (qA + 5) (qB + 5)
    calc
      alternatingProdBlockHom (qA + 5) (qB + 5) (r (zE x)) = f (zE x) :=
        alternatingBlockPreimageProjection_fac
          (qA + 5) (qB + 5) f (zE x)
      _ = unequalSixSwap qA qB hA hB *
          alternatingProdBlockHom (qA + 5) (qB + 5)
            (RootAm.tailAltHom qA 5 (by omega)
              (centralRootAmPreimageProjection qA 5 (by omega) rL x), 1) *
          (unequalSixSwap qA qB hA hB)⁻¹ := by
        change f (d * iRoot x * d⁻¹) = _
        rw [map_mul, map_mul, map_inv, hd, hximageRoot]
      _ = alternatingProdBlockHom (qA + 5) (qB + 5)
          (1, RootAm.tailAltHom qB 5 (by omega)
            (centralRootAmPreimageProjection qA 5 (by omega) rL x)) :=
        unequalSixSwap_conj_root qA qB hA hB
          (centralRootAmPreimageProjection qA 5 (by omega) rL x)
  have hzER (x : R) : zE x ∈ ER := by
    change r (zE x) ∈ prodRightFactor
      (alternatingGroup (Fin (qA + 5)))
      (alternatingGroup (Fin (qB + 5)))
    rw [hzproj]
    exact ⟨Subgroup.mem_bot.mpr rfl, trivial⟩
  let φ : R →* ER := {
    toFun := fun x => ⟨zE x, hzER x⟩
    map_one' := by
      apply Subtype.ext
      apply Subtype.ext
      simp [zE, iRoot, iL]
    map_mul' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      change d * iRoot (x * y) * d⁻¹ =
        (d * iRoot x * d⁻¹) * (d * iRoot y * d⁻¹)
      rw [map_mul]
      group
  }
  have hmap : (commutator R).map φ ≤ commutator ER := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hyRmem : φ (xL : R) ∈ commutator ER := by
    apply hmap
    exact ⟨(xL : R), xL.2, rfl⟩
  let yR : DR := ⟨φ (xL : R), hyRmem⟩
  refine ⟨yR, ?_, rfl⟩
  change (r (zE (xL : R))).2 =
    RootAm.tailAltHom qB 5 (by omega) (rRoot xL)
  rw [hzproj]
  rfl

public theorem evenBlock_unequalComponentDerivedKernel_eq_of_six_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (hMA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (hMB : Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker ≤ 2)
    (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    evenBlockLeftDerivedKernel (qA + 5) (qB + 5) f =
      evenBlockRightDerivedKernel (qA + 5) (qB + 5) f := by
  obtain ⟨hLcard, yL0, hyL0, hL0⟩ :=
    evenBlock_leftComponent_pair_of_multiplier_le_two
      qA qB hMA f hf hker
  obtain ⟨hRcard, yR0, hyR0, hR0⟩ :=
    evenBlock_rightComponent_pair_of_multiplier_le_two
      qA qB hMB f hf hker
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let EL := prodLeftPreimage r
  let ER := prodRightPreimage r
  let DL := prodLeftPreimageDerived r
  let DR := prodRightPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let rR := prodRightPreimageDerivedProjection r
  let R := centralRootAmPreimage qA 5 (by omega) rL
  let RD := centralRootAmPreimageDerived qA 5 (by omega) rL
  let rRoot := centralRootAmPreimageDerivedProjection qA 5 (by omega) rL
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective
      (qA + 5) (qB + 5) f hf
  have hrL : Function.Surjective rL :=
    prodLeftPreimageDerivedProjection_surjective r hr
  have hrRoot : Function.Surjective rRoot :=
    centralRootAmPreimageDerivedProjection_surjective
      qA 5 (by omega) rL hrL
  obtain ⟨xL, hxL⟩ := hrRoot
    (⟨RootFourSubgroup.rho1 0,
      RootFourSubgroup.rho1_mem_alternating 0⟩ :
      alternatingGroup (Fin 5))
  let yL : DL := (xL : R)
  have hrootfac : RootAm.tailAltHom qA 5 (by omega) (rRoot xL) =
      rL yL := by
    let e := centralRootAmEquiv qA 5 (by omega)
    have h := congrArg Subtype.val
      (e.apply_symm_apply (⟨rL yL, (xL : R).2⟩ :
        RootAm.rootAm qA 5 (by omega)))
    exact h
  have hyL : rL yL =
      (⟨RootFourSubgroup.rho1 qA,
        RootFourSubgroup.rho1_mem_alternating qA⟩ :
        alternatingGroup (Fin (qA + 5))) := by
    calc
      rL yL = RootAm.tailAltHom qA 5 (by omega) (rRoot xL) :=
        hrootfac.symm
      _ = RootAm.tailAltHom qA 5 (by omega)
          (⟨RootFourSubgroup.rho1 0,
            RootFourSubgroup.rho1_mem_alternating 0⟩ :
            alternatingGroup (Fin 5)) := by rw [hxL]
      _ = _ := tailAltHom_rho1 qA
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center
      (qA + 5) (qB + 5) f hker
  have hrLcenter : rL.ker ≤ Subgroup.center DL := by
    intro x hx
    have hx' : (x : EL) ∈ (prodLeftPreimageProjection r).ker := hx
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (prodLeftPreimageProjection_ker_le_center r hrker hx') z
  have hrRcenter : rR.ker ≤ Subgroup.center DR := by
    intro x hx
    have hx' : (x : ER) ∈ (prodRightPreimageProjection r).ker := hx
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (prodRightPreimageProjection_ker_le_center r hrker hx') z
  have hLsq : yL ^ 2 = yL0 ^ 2 :=
    sq_eq_sq_of_apply_eq_of_card_ker_le_two rL hrLcenter hLcard
      (hyL.trans hyL0.symm)
  have hL : rL.ker = Subgroup.zpowers (yL ^ 2) := by
    rw [hL0, hLsq]
  obtain ⟨d, hd⟩ := hf (unequalSixSwap qA qB hA hB)
  obtain ⟨yR, hyR, hconjRoot⟩ :=
    exists_rightDerived_conjugate_of_unequalSixSwap
      qA qB hA hB f d hd xL
  have hyRstd : rR yR =
      (⟨RootFourSubgroup.rho1 qB,
        RootFourSubgroup.rho1_mem_alternating qB⟩ :
        alternatingGroup (Fin (qB + 5))) := by
    rw [hyR, hxL]
    exact tailAltHom_rho1 qB
  have hRsq : yR ^ 2 = yR0 ^ 2 :=
    sq_eq_sq_of_apply_eq_of_card_ker_le_two rR hrRcenter hRcard
      (hyRstd.trans hyR0.symm)
  have hR : rR.ker = Subgroup.zpowers (yR ^ 2) := by
    rw [hR0, hRsq]
  have hconj : d * evenBlockLeftDerivedEmbedding
        (qA + 5) (qB + 5) f yL * d⁻¹ =
      evenBlockRightDerivedEmbedding (qA + 5) (qB + 5) f yR := by
    simpa [yL, evenBlockLeftRootDerivedEmbedding] using hconjRoot
  exact evenBlock_componentDerivedKernel_eq_of_conjugate_generators
    (qA + 5) (qB + 5) f hker yL yR hL hR d hconj

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockKernelEndpoint.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

public theorem kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H] [Group G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (P : Sylow p H)
    (E : Subgroup H) (hPE : (P : Subgroup H) ≤ E)
    (D C : Subgroup E)
    (hdecomp : ∀ x : E,
      ∃ k : f.ker.comap E.subtype, ∃ d : D,
        (k : E) * (d : E) = x)
    (hinf : (f.ker.comap E.subtype) ⊓ D = C) :
    f.ker.comap E.subtype = C := by
  have hKleP : f.ker ≤ (P : Subgroup H) :=
    hkerp.le_sylow_of_normal P
  let i : P →* E :=
    (P : Subgroup H).subtype.codRestrict E (fun x => hPE x.2)
  let Kp : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  let Dp : Subgroup P := D.comap i
  have hKpFrattini : Kp ≤ frattini P :=
    GLS3.Chapter5.ker_comap_le_frattini_sylow P f hker
  have hsup : Dp ⊔ Kp = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k, d, hkd⟩ := hdecomp (i x)
    have hkGlobal : ((k : E) : H) ∈ f.ker := k.2
    let kp : P := ⟨((k : E) : H), hKleP hkGlobal⟩
    have hkpKp : kp ∈ Kp := hkGlobal
    let dp : P := kp⁻¹ * x
    have hidp : i dp = d := by
      apply Subtype.ext
      change ((k : E) : H)⁻¹ * (x : H) = ((d : E) : H)
      have hkdH := congrArg (fun z : E => (z : H)) hkd
      change ((k : E) : H) * ((d : E) : H) = (x : H) at hkdH
      rw [← hkdH]
      simp
    have hdpDp : dp ∈ Dp := by
      change i dp ∈ D
      rw [hidp]
      exact d.2
    have hkpSup : kp ∈ Dp ⊔ Kp := Subgroup.mem_sup_right hkpKp
    have hdpSup : dp ∈ Dp ⊔ Kp := Subgroup.mem_sup_left hdpDp
    have hxSup := Subgroup.mul_mem (Dp ⊔ Kp) hkpSup hdpSup
    simpa [dp] using hxSup
  have hDfrattini : Dp ⊔ frattini P = ⊤ := by
    apply top_unique
    calc
      (⊤ : Subgroup P) = Dp ⊔ Kp := hsup.symm
      _ ≤ Dp ⊔ frattini P := sup_le_sup le_rfl hKpFrattini
  have hDtop : Dp = ⊤ :=
    frattini_nongenerating (K := Dp) hDfrattini
  have hKED : f.ker.comap E.subtype ≤ D := by
    intro z hz
    let zp : P := ⟨(z : H), hKleP hz⟩
    have hzpDp : zp ∈ Dp := by rw [hDtop]; trivial
    change i zp ∈ D at hzpDp
    simpa [i, zp] using hzpDp
  exact (inf_eq_left.mpr hKED).symm.trans hinf

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockCentralProduct.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

public theorem commutatorElement_eq_one_of_left_perfect_of_mem_center'
    {A H : Type*} [Group A] [Group H] [Group.IsPerfect A]
    (s : A →* H) (y : H)
    (hc : ∀ a : A, ⁅s a, y⁆ ∈ Subgroup.center H)
    (a : A) : ⁅s a, y⁆ = 1 := by
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun x z => Subtype.ext
      (Subgroup.mem_center_iff.mp x.2 z.1).symm }
  let φ : A →* Subgroup.center H := {
    toFun := fun x => ⟨⁅s x, y⁆, hc x⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro a₁ a₂
      apply Subtype.ext
      change ⁅s (a₁ * a₂), y⁆ = ⁅s a₁, y⁆ * ⁅s a₂, y⁆
      rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
      have hc₂ := hc a₂
      have hconj : s a₁ * ⁅s a₂, y⁆ * (s a₁)⁻¹ = ⁅s a₂, y⁆ := by
        have hcomm := Subgroup.mem_center_iff.mp hc₂ (s a₁)
        rw [hcomm]
        simp
      rw [hconj]
      exact (Subgroup.mem_center_iff.mp hc₂ ⁅s a₁, y⁆).symm
  }
  have hφ : φ a = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker φ
      (Group.IsPerfect.mem_commutator (g := a))
  exact congrArg Subtype.val hφ

@[expose] public def evenBlockLeftDerivedEmbeddingToBlock
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    prodLeftPreimageDerived
        (alternatingBlockPreimageProjection a b f) →*
      alternatingBlockPreimage a b f :=
  (prodLeftPreimage
    (alternatingBlockPreimageProjection a b f)).subtype.comp
      (prodLeftPreimageDerived
        (alternatingBlockPreimageProjection a b f)).subtype

@[expose] public def evenBlockRightDerivedEmbeddingToBlock
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    prodRightPreimageDerived
        (alternatingBlockPreimageProjection a b f) →*
      alternatingBlockPreimage a b f :=
  (prodRightPreimage
    (alternatingBlockPreimageProjection a b f)).subtype.comp
      (prodRightPreimageDerived
        (alternatingBlockPreimageProjection a b f)).subtype

public abbrev evenBlockLeftDerivedKernelInBlock
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    Subgroup (alternatingBlockPreimage a b f) :=
  (prodLeftPreimageDerivedProjection
    (alternatingBlockPreimageProjection a b f)).ker.map
      (evenBlockLeftDerivedEmbeddingToBlock a b f)

public abbrev evenBlockRightDerivedKernelInBlock
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    Subgroup (alternatingBlockPreimage a b f) :=
  (prodRightPreimageDerivedProjection
    (alternatingBlockPreimageProjection a b f)).ker.map
      (evenBlockRightDerivedEmbeddingToBlock a b f)

public theorem evenBlock_derivedKernelInBlock_eq_of_global_eq
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hglobal : evenBlockLeftDerivedKernel a b f =
      evenBlockRightDerivedKernel a b f) :
    evenBlockLeftDerivedKernelInBlock a b f =
      evenBlockRightDerivedKernelInBlock a b f := by
  let E := alternatingBlockPreimage a b f
  apply Subgroup.map_injective E.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_map]
  exact hglobal

public theorem evenBlock_derivedEmbeddings_commute
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f))
    (y : prodRightPreimageDerived
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) :
    Commute
      (evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x)
      (evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y) := by
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let EL := prodLeftPreimage r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let iL : DL →* E :=
    evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let iR := evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective
      (qA + 5) (qB + 5) f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center
      (qA + 5) (qB + 5) f hker
  let : Group.IsPerfect DL :=
    commutator_isPerfect_of_surjective_of_ker_le_center
      (prodLeftPreimageProjection r)
      (prodLeftPreimageProjection_surjective r hr)
      (prodLeftPreimageProjection_ker_le_center r hrker)
  have hLproj (z : DL) : r (iL z) = (rL z, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp z.1.2.2
  have hRproj (z : prodRightPreimageDerived r) :
      r (iR z) = (1, prodRightPreimageDerivedProjection r z) := by
    apply Prod.ext
    · exact Subgroup.mem_bot.mp z.1.2.1
    · rfl
  have hc (z : DL) : ⁅iL z, iR y⁆ ∈ Subgroup.center E := by
    apply hrker
    rw [MonoidHom.mem_ker, map_commutatorElement, hLproj, hRproj]
    simp [commutatorElement_def]
  rw [← commutatorElement_eq_one_iff_commute]
  exact commutatorElement_eq_one_of_left_perfect_of_mem_center'
    iL (iR y) hc x

@[expose] public def evenBlockComponentDerivedMulHom
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) ×
        prodRightPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) →*
      alternatingBlockPreimage (qA + 5) (qB + 5) f where
  toFun x :=
    evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.1 *
      evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.2
  map_one' := by simp
  map_mul' x y := by
    change
      (evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
          (x.1 * y.1)) *
          evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
            (x.2 * y.2) =
        (evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.1 *
            evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.2) *
          (evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.1 *
            evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.2)
    rw [map_mul, map_mul]
    have hc := evenBlock_derivedEmbeddings_commute
      qA qB f hf hker y.1 x.2
    calc
      _ = evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.1 *
          (evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.1 *
            evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.2) *
          evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.2 := by
        simp only [mul_assoc]
      _ = evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.1 *
          (evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f x.2 *
            evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.1) *
          evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f y.2 := by
        rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

public abbrev evenBlockComponentDerivedProduct
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Subgroup (alternatingBlockPreimage (qA + 5) (qB + 5) f) :=
  (evenBlockComponentDerivedMulHom qA qB f hf hker).range

public theorem evenBlockComponentDerivedMulHom_projection
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) ×
        prodRightPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) :
    alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
        (evenBlockComponentDerivedMulHom qA qB f hf hker x) =
      (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) x.1,
        prodRightPreimageDerivedProjection
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) x.2) := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let iL := evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let iR := evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let rL := prodLeftPreimageDerivedProjection r
  let rR := prodRightPreimageDerivedProjection r
  have hLproj : r (iL x.1) = (rL x.1, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp x.1.1.2.2
  have hRproj : r (iR x.2) = (1, rR x.2) := by
    apply Prod.ext
    · exact Subgroup.mem_bot.mp x.2.1.2.1
    · rfl
  change r (iL x.1 * iR x.2) = _
  rw [map_mul, hLproj, hRproj]
  apply Prod.ext
  · rfl
  · rfl

public theorem evenBlockComponentDerivedProduct_decomposition
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    ∀ x : alternatingBlockPreimage (qA + 5) (qB + 5) f,
      ∃ k : (alternatingBlockPreimageProjection
          (qA + 5) (qB + 5) f).ker,
        ∃ d : evenBlockComponentDerivedProduct qA qB f hf hker,
          (k : alternatingBlockPreimage (qA + 5) (qB + 5) f) *
            (d : alternatingBlockPreimage (qA + 5) (qB + 5) f) = x := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective
      (qA + 5) (qB + 5) f hf
  have hrL : Function.Surjective (prodLeftPreimageDerivedProjection r) :=
    prodLeftPreimageDerivedProjection_surjective r hr
  have hrR : Function.Surjective (prodRightPreimageDerivedProjection r) :=
    prodRightPreimageDerivedProjection_surjective r hr
  intro x
  obtain ⟨xL, hxL⟩ := hrL (r x).1
  obtain ⟨xR, hxR⟩ := hrR (r x).2
  let d0 := evenBlockComponentDerivedMulHom qA qB f hf hker (xL, xR)
  have hdproj : r d0 = r x := by
    rw [evenBlockComponentDerivedMulHom_projection, hxL, hxR]
  have hk : x * d0⁻¹ ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdproj]
    simp
  let k : r.ker := ⟨x * d0⁻¹, hk⟩
  let d : evenBlockComponentDerivedProduct qA qB f hf hker :=
    ⟨d0, ⟨(xL, xR), rfl⟩⟩
  exact ⟨k, d, by simp [k, d, d0]⟩

public theorem evenBlockComponentDerivedProduct_ker_inf_eq_of_kernel_eq
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock
        (qA + 5) (qB + 5) f =
      evenBlockRightDerivedKernelInBlock (qA + 5) (qB + 5) f) :
    (alternatingBlockPreimageProjection
        (qA + 5) (qB + 5) f).ker ⊓
      evenBlockComponentDerivedProduct qA qB f hf hker =
        evenBlockLeftDerivedKernelInBlock (qA + 5) (qB + 5) f := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let iL := evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let iR := evenBlockRightDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let rL := prodLeftPreimageDerivedProjection r
  let rR := prodRightPreimageDerivedProjection r
  apply le_antisymm
  · rintro z ⟨hzker, hzprod⟩
    obtain ⟨x, rfl⟩ := hzprod
    have hpair : (rL x.1, rR x.2) = 1 := by
      rw [← evenBlockComponentDerivedMulHom_projection qA qB f hf hker x]
      exact MonoidHom.mem_ker.mp hzker
    have hxL : x.1 ∈ rL.ker :=
      MonoidHom.mem_ker.mpr (congrArg Prod.fst hpair)
    have hxR : x.2 ∈ rR.ker :=
      MonoidHom.mem_ker.mpr (congrArg Prod.snd hpair)
    have hiL : iL x.1 ∈ evenBlockLeftDerivedKernelInBlock
        (qA + 5) (qB + 5) f := ⟨x.1, hxL, rfl⟩
    have hiR : iR x.2 ∈ evenBlockRightDerivedKernelInBlock
        (qA + 5) (qB + 5) f := ⟨x.2, hxR, rfl⟩
    rw [← hfusion] at hiR
    exact Subgroup.mul_mem _ hiL hiR
  · intro z hz
    constructor
    · obtain ⟨x, hx, rfl⟩ := hz
      change r (iL x) = 1
      have hproj := evenBlockComponentDerivedMulHom_projection
        qA qB f hf hker (x, 1)
      simpa [iL, evenBlockComponentDerivedMulHom] using hproj.trans
        (Prod.ext (MonoidHom.mem_ker.mp hx) (by simp))
    · obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨(x, 1), by simp [evenBlockComponentDerivedMulHom]⟩

end GLS3.Chapter5.SchurPresentation

/- Source: EvenBlockParityCoset.lean -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
/- END Theory.EvenBlockCore1 -/

/- BEGIN Theory.UnitsInvolutionHom -/
noncomputable section

namespace GLS3.Chapter5

/-- The unique homomorphism from the two-element group `ℤˣ` sending `-1` to
an involution `r`. -/
public def unitsInvolutionHom {G : Type*} [Group G]
    (r : G) (hr : r ^ 2 = 1) : ℤˣ →* G where
  toFun u := if u = 1 then 1 else r
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
    · simp
    · simp
    · simp
    · have hneg : (-1 : ℤˣ) ≠ 1 := by norm_num
      simp only [neg_mul_neg, one_mul, ite_true, if_neg hneg]
      simpa [pow_two] using hr.symm

@[simp]
public theorem unitsInvolutionHom_one {G : Type*} [Group G]
    (r : G) (hr : r ^ 2 = 1) :
    unitsInvolutionHom r hr 1 = 1 := by
  simp [unitsInvolutionHom]

@[simp]
public theorem unitsInvolutionHom_neg_one {G : Type*} [Group G]
    (r : G) (hr : r ^ 2 = 1) :
    unitsInvolutionHom r hr (-1) = r := by
  simp [unitsInvolutionHom]

end GLS3.Chapter5
/- END Theory.UnitsInvolutionHom -/

