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

public import Theory.Alternating.EvenBlockCore
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.EvenBlock -/
noncomputable section
set_option maxHeartbeats 800000

namespace GLS3.Chapter5.SchurPresentation

public def evenBlockFourRootEmbedding (q : Nat) :
    Fin 5 ↪ Fin ((q + 5) + 4) :=
  ⟨fun i => if hi : i = 0 then ⟨4, by omega⟩
      else ⟨q + 4 + i, by omega⟩, by
    intro i j h
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · exact hi.trans hj.symm
      · have h' := congrArg Fin.val h
        simp [hi, hj] at h'
        omega
    · by_cases hj : j = 0
      · have h' := congrArg Fin.val h
        simp [hi, hj] at h'
        omega
      · apply Fin.ext
        have h' := congrArg Fin.val h
        simp [hi, hj] at h'
        omega⟩

public def evenBlockFourRightEmbedding : Fin 4 ↪ Fin 5 :=
  ⟨fun i => ⟨i + 1, by omega⟩, by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    dsimp at h'
    omega⟩

private theorem evenBlockFourRightEmbedding_val (j : Fin 4) :
    (evenBlockFourRightEmbedding j).val = j.val + 1 := rfl

private theorem evenBlockFourRightEmbedding_ne_zero (j : Fin 4) :
    evenBlockFourRightEmbedding j ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  rw [evenBlockFourRightEmbedding_val] at hval
  simp at hval

public noncomputable def evenBlockFourRootPermHom (q : Nat) :
    Equiv.Perm (Fin 5) →* Equiv.Perm (Fin ((q + 5) + 4)) :=
  Equiv.Perm.viaEmbeddingHom (evenBlockFourRootEmbedding q)

public noncomputable def evenBlockFourRightPermHom :
    Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) :=
  Equiv.Perm.viaEmbeddingHom evenBlockFourRightEmbedding

set_option linter.unnecessarySimpa false in
public theorem sign_evenBlockFourRootPermHom (q : Nat)
    (σ : Equiv.Perm (Fin 5)) :
    Equiv.Perm.sign (evenBlockFourRootPermHom q σ) =
      Equiv.Perm.sign σ := by
  unfold evenBlockFourRootPermHom
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  simpa [Equiv.Perm.viaEmbedding] using
    (Equiv.Perm.sign_extendDomain σ
      (Equiv.ofInjective (evenBlockFourRootEmbedding q).1
        (evenBlockFourRootEmbedding q).2))

set_option linter.unnecessarySimpa false in
public theorem sign_evenBlockFourRightPermHom
    (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign (evenBlockFourRightPermHom σ) =
      Equiv.Perm.sign σ := by
  unfold evenBlockFourRightPermHom
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  simpa [Equiv.Perm.viaEmbedding] using
    (Equiv.Perm.sign_extendDomain σ
      (Equiv.ofInjective evenBlockFourRightEmbedding.1
        evenBlockFourRightEmbedding.2))

public noncomputable def evenBlockFourRootAltHom (q : Nat) :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin ((q + 5) + 4)) where
  toFun σ := ⟨evenBlockFourRootPermHom q σ, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockFourRootPermHom]
    exact σ.2⟩
  map_one' := by
    apply Subtype.ext
    simp [evenBlockFourRootPermHom]
  map_mul' a b := by
    apply Subtype.ext
    simp [evenBlockFourRootPermHom]

public noncomputable def evenBlockFourRightAltHom :
    alternatingGroup (Fin 4) →* alternatingGroup (Fin 5) where
  toFun σ := ⟨evenBlockFourRightPermHom σ, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockFourRightPermHom]
    exact σ.2⟩
  map_one' := by
    apply Subtype.ext
    simp [evenBlockFourRightPermHom]
  map_mul' a b := by
    apply Subtype.ext
    simp [evenBlockFourRightPermHom]

public theorem evenBlockFourRootAltHom_right
    (q : Nat) (σ : alternatingGroup (Fin 4)) :
    evenBlockFourRootAltHom q
        (evenBlockFourRightAltHom σ) =
      alternatingProdBlockHom (q + 5) 4 (1, σ) := by
  apply Subtype.ext
  simp only [evenBlockFourRootAltHom,
    evenBlockFourRightAltHom,
    coe_alternatingProdBlockHom_apply]
  change evenBlockFourRootPermHom q
      (evenBlockFourRightPermHom σ.1) =
    permProdBlockHom (q + 5) 4 (1, σ.1)
  rw [permProdBlockHom_apply]
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases hleft : x < q + 5
  · let i : Fin (q + 5) := ⟨x, hleft⟩
    have hcoord : (⟨x, hx⟩ : Fin ((q + 5) + 4)) =
        finSumFinEquiv (Sum.inl i) := by
      apply Fin.ext
      rfl
    by_cases hx4 : x = 4
    · subst x
      let z : Fin 5 := 0
      have hemb0 : evenBlockFourRootEmbedding q z =
          (⟨4, hx⟩ : Fin ((q + 5) + 4)) := by
        apply Fin.ext
        simp [z, evenBlockFourRootEmbedding]
      have hzRange : z ∉ Set.range evenBlockFourRightEmbedding := by
        rintro ⟨j, hj⟩
        have hval := congrArg Fin.val hj
        rw [evenBlockFourRightEmbedding_val] at hval
        simp [z] at hval
      rw [evenBlockFourRootPermHom,
        ← hemb0, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply]
      change evenBlockFourRootEmbedding q
          (evenBlockFourRightPermHom σ.1 z) = _
      rw [evenBlockFourRightPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hzRange]
      rw [hemb0, hcoord]
      simp [Equiv.permCongr_apply]
    · have hrootRange : (⟨x, hx⟩ : Fin ((q + 5) + 4)) ∉
          Set.range (evenBlockFourRootEmbedding q) := by
        rintro ⟨j, hj⟩
        have hval := congrArg Fin.val hj
        by_cases hj0 : j = 0
        · simp [evenBlockFourRootEmbedding, hj0] at hval
          exact hx4 hval.symm
        · simp [evenBlockFourRootEmbedding, hj0] at hval
          omega
      rw [evenBlockFourRootPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hrootRange,
        hcoord]
      simp [Equiv.permCongr_apply]
  · have hq : q + 5 ≤ x := by omega
    let i : Fin 4 := ⟨x - (q + 5), by omega⟩
    have hcoord : (⟨x, hx⟩ : Fin ((q + 5) + 4)) =
        finSumFinEquiv (Sum.inr i) := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hcoord]
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.Perm.sumCongr_apply, Sum.map_inr]
    change evenBlockFourRootPermHom q
        (evenBlockFourRightPermHom σ.1)
          (finSumFinEquiv (Sum.inr i)) =
      finSumFinEquiv (Sum.inr (σ.1 i))
    have hemb (j : Fin 4) :
        evenBlockFourRootEmbedding q
            (evenBlockFourRightEmbedding j) =
        finSumFinEquiv (Sum.inr j) := by
      apply Fin.ext
      change (if h : evenBlockFourRightEmbedding j = 0 then 4 else
        q + 4 + (evenBlockFourRightEmbedding j).val) = q + 5 + j.val
      split_ifs with hzero
      · exact (evenBlockFourRightEmbedding_ne_zero j hzero).elim
      · rw [evenBlockFourRightEmbedding_val]
        omega
    rw [← hemb i, evenBlockFourRootPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply]
    change evenBlockFourRootEmbedding q
        (evenBlockFourRightPermHom σ.1
          (evenBlockFourRightEmbedding i)) = _
    rw [evenBlockFourRightPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply]
    exact hemb (σ.1 i)

public theorem evenBlockFourRootAltHom_injective (q : Nat) :
    Function.Injective (evenBlockFourRootAltHom q) := by
  intro x y hxy
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective
    (ι := evenBlockFourRootEmbedding q)
  exact congrArg Subtype.val hxy

public theorem evenBlockFourRightAltHom_injective :
    Function.Injective evenBlockFourRightAltHom := by
  intro x y hxy
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective
    (ι := evenBlockFourRightEmbedding)
  exact congrArg Subtype.val hxy

public def evenBlockFourRoot (q : Nat) :
    Subgroup (alternatingGroup (Fin ((q + 5) + 4))) :=
  (evenBlockFourRootAltHom q).range

public noncomputable def evenBlockFourRootEquiv (q : Nat) :
    alternatingGroup (Fin 5) ≃* evenBlockFourRoot q :=
  MonoidHom.ofInjective (f := evenBlockFourRootAltHom q)
    (evenBlockFourRootAltHom_injective q)

public abbrev evenBlockFourRootPreimage
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) : Subgroup H :=
  (evenBlockFourRoot q).comap f

public noncomputable def evenBlockFourRootPreimageProjection
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRootPreimage q f →* alternatingGroup (Fin 5) :=
  (evenBlockFourRootEquiv q).symm.toMonoidHom.comp
    ((f.comp (evenBlockFourRootPreimage q f).subtype).codRestrict
      (evenBlockFourRoot q) (fun x => x.2))

public theorem evenBlockFourRootPreimageProjection_surjective
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f) :
    Function.Surjective
      (evenBlockFourRootPreimageProjection q f) := by
  intro y
  let y' : evenBlockFourRoot q :=
    evenBlockFourRootEquiv q y
  obtain ⟨x, hx⟩ := hf y'.1
  have hxRoot : f x ∈ evenBlockFourRoot q := hx.symm ▸ y'.2
  refine ⟨⟨x, hxRoot⟩, ?_⟩
  change (evenBlockFourRootEquiv q).symm ⟨f x, hxRoot⟩ = y
  apply (evenBlockFourRootEquiv q).injective
  rw [(evenBlockFourRootEquiv q).apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem evenBlockFourRootPreimageProjection_ker_le_center
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hker : f.ker ≤ Subgroup.center H) :
    (evenBlockFourRootPreimageProjection q f).ker ≤
      Subgroup.center (evenBlockFourRootPreimage q f) := by
  let R := evenBlockFourRoot q
  let E := evenBlockFourRootPreimage q f
  let r0 : E →* R :=
    (f.comp E.subtype).codRestrict R (fun x => x.2)
  have hkerEq : (evenBlockFourRootPreimageProjection q f).ker =
      r0.ker := by
    exact MonoidHom.ker_comp_of_injective r0
      (evenBlockFourRootEquiv q).symm.toMonoidHom
      (evenBlockFourRootEquiv q).symm.injective
  intro x hx
  have hx0 : x ∈ r0.ker := by rwa [← hkerEq]
  have hxGlobal : (x : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx0)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxGlobal) y.1

public abbrev evenBlockFourRootPreimageDerived
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :=
  commutator (evenBlockFourRootPreimage q f)

public noncomputable def evenBlockFourRootPreimageDerivedProjection
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRootPreimageDerived q f →*
      alternatingGroup (Fin 5) :=
  (evenBlockFourRootPreimageProjection q f).comp
    (evenBlockFourRootPreimageDerived q f).subtype

public theorem evenBlockFourRootPreimageDerivedProjection_surjective
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f) :
    Function.Surjective
      (evenBlockFourRootPreimageDerivedProjection q f) := by
  let E := evenBlockFourRootPreimage q f
  let r := evenBlockFourRootPreimageProjection q f
  have hrange : r.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (evenBlockFourRootPreimageProjection_surjective q f hf)
  have hmap : (commutator E).map r = ⊤ := by
    rw [map_commutator_eq, hrange]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator E).map r := by rw [hmap]; trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

public theorem evenBlockFourRootPreimageDerivedProjection_ker_le_center
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hker : f.ker ≤ Subgroup.center H) :
    (evenBlockFourRootPreimageDerivedProjection q f).ker ≤
      Subgroup.center (evenBlockFourRootPreimageDerived q f) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : (x : evenBlockFourRootPreimage q f) ∈
      (evenBlockFourRootPreimageProjection q f).ker := hx
  exact Subgroup.mem_center_iff.mp
    (evenBlockFourRootPreimageProjection_ker_le_center q f hker hx') y

public def evenBlockFourRhoPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

public def evenBlockFourRho : alternatingGroup (Fin 4) :=
  ⟨evenBlockFourRhoPerm,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide))⟩

public def evenBlockFourShift : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, Equiv.Perm.finRotate_bit1_mem_alternatingGroup (n := 2)⟩

public theorem evenBlockFourRightPermHom_swap (i j : Fin 4) :
    evenBlockFourRightPermHom (Equiv.swap i j) =
      Equiv.swap (evenBlockFourRightEmbedding i)
        (evenBlockFourRightEmbedding j) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range evenBlockFourRightEmbedding
  · obtain ⟨k, rfl⟩ := hx
    rw [evenBlockFourRightPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply]
    exact evenBlockFourRightEmbedding.injective.map_swap i j k
  · have hxi : x ≠ evenBlockFourRightEmbedding i := by
      intro h
      apply hx
      exact ⟨i, h.symm⟩
    have hxj : x ≠ evenBlockFourRightEmbedding j := by
      intro h
      apply hx
      exact ⟨j, h.symm⟩
    rw [evenBlockFourRightPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      Equiv.swap_apply_of_ne_of_ne hxi hxj]

public theorem evenBlockFourRightAltHom_rho :
    (evenBlockFourRightAltHom evenBlockFourRho :
        Equiv.Perm (Fin 5)) =
      Equiv.swap (evenBlockFourRightEmbedding 0)
          (evenBlockFourRightEmbedding 1) *
        Equiv.swap (evenBlockFourRightEmbedding 2)
          (evenBlockFourRightEmbedding 3) := by
  change evenBlockFourRightPermHom evenBlockFourRhoPerm = _
  rw [evenBlockFourRhoPerm, map_mul,
    evenBlockFourRightPermHom_swap,
    evenBlockFourRightPermHom_swap]

public theorem evenBlockFourShift_conj_rho :
    evenBlockFourShift *
        (⟨RootFourSubgroup.rho1 0,
          RootFourSubgroup.rho1_mem_alternating 0⟩ :
          alternatingGroup (Fin 5)) *
        evenBlockFourShift⁻¹ =
      evenBlockFourRightAltHom evenBlockFourRho := by
  apply Subtype.ext
  change finRotate 5 * RootFourSubgroup.rho1 0 * (finRotate 5)⁻¹ =
    evenBlockFourRightPermHom evenBlockFourRhoPerm
  change finRotate 5 *
      (Equiv.swap (RootFourSubgroup.p0 0) (RootFourSubgroup.p1 0) *
        Equiv.swap (RootFourSubgroup.p2 0) (RootFourSubgroup.p3 0)) *
      (finRotate 5)⁻¹ = _
  calc
    _ = (finRotate 5 *
          Equiv.swap (RootFourSubgroup.p0 0) (RootFourSubgroup.p1 0) *
          (finRotate 5)⁻¹) *
        (finRotate 5 *
          Equiv.swap (RootFourSubgroup.p2 0) (RootFourSubgroup.p3 0) *
          (finRotate 5)⁻¹) := by group
    _ = Equiv.swap (finRotate 5 (RootFourSubgroup.p0 0))
          (finRotate 5 (RootFourSubgroup.p1 0)) *
        Equiv.swap (finRotate 5 (RootFourSubgroup.p2 0))
          (finRotate 5 (RootFourSubgroup.p3 0)) := by
      rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    _ = Equiv.swap (evenBlockFourRightEmbedding 0)
          (evenBlockFourRightEmbedding 1) *
        Equiv.swap (evenBlockFourRightEmbedding 2)
          (evenBlockFourRightEmbedding 3) := by decide
    _ = evenBlockFourRightPermHom evenBlockFourRhoPerm := by
      exact evenBlockFourRightAltHom_rho.symm

public theorem evenBlockFourRoot_pair
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (evenBlockFourRootPreimageDerivedProjection q f).ker ≤ 2 ∧
      ∃ y : evenBlockFourRootPreimageDerived q f,
        evenBlockFourRootPreimageDerivedProjection q f y =
          (⟨RootFourSubgroup.rho1 0,
            RootFourSubgroup.rho1_mem_alternating 0⟩ :
            alternatingGroup (Fin 5)) ∧
        (evenBlockFourRootPreimageDerivedProjection q f).ker =
          Subgroup.zpowers (y ^ 2) := by
  have hM : Nat.card
      (alternatingFreeCentralCovering 0).toMonoidHom.ker ≤ 2 := by
    rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two]
  exact
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      0 hM (evenBlockFourRootPreimageProjection q f)
      (evenBlockFourRootPreimageProjection_surjective q f hf)
      (evenBlockFourRootPreimageProjection_ker_le_center q f hker)

public def evenBlockFourRightRoot :
    Subgroup (alternatingGroup (Fin 5)) :=
  evenBlockFourRightAltHom.range

public noncomputable def evenBlockFourRightRootEquiv :
    alternatingGroup (Fin 4) ≃* evenBlockFourRightRoot :=
  MonoidHom.ofInjective
    (f := evenBlockFourRightAltHom)
    evenBlockFourRightAltHom_injective

public abbrev evenBlockFourRightSubextension
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    Subgroup (evenBlockFourRootPreimageDerived q f) :=
  evenBlockFourRightRoot.comap
    (evenBlockFourRootPreimageDerivedProjection q f)

public noncomputable def evenBlockFourRightSubextensionProjection
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRightSubextension q f →*
      alternatingGroup (Fin 4) :=
  evenBlockFourRightRootEquiv.symm.toMonoidHom.comp
    (((evenBlockFourRootPreimageDerivedProjection q f).comp
        (evenBlockFourRightSubextension q f).subtype).codRestrict
      evenBlockFourRightRoot (fun x => x.2))

public theorem evenBlockFourRightSubextensionProjection_surjective
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f) :
    Function.Surjective
      (evenBlockFourRightSubextensionProjection q f) := by
  intro y
  let y' : evenBlockFourRightRoot :=
    evenBlockFourRightRootEquiv y
  obtain ⟨x, hx⟩ :=
    evenBlockFourRootPreimageDerivedProjection_surjective q f hf y'.1
  have hxRight :
      evenBlockFourRootPreimageDerivedProjection q f x ∈
        evenBlockFourRightRoot := hx.symm ▸ y'.2
  refine ⟨⟨x, hxRight⟩, ?_⟩
  change evenBlockFourRightRootEquiv.symm
      ⟨evenBlockFourRootPreimageDerivedProjection q f x,
        hxRight⟩ = y
  apply evenBlockFourRightRootEquiv.injective
  rw [evenBlockFourRightRootEquiv.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem evenBlockFourRightSubextensionProjection_fac
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (x : evenBlockFourRightSubextension q f) :
    evenBlockFourRightAltHom
        (evenBlockFourRightSubextensionProjection q f x) =
      evenBlockFourRootPreimageDerivedProjection q f x := by
  let r := evenBlockFourRootPreimageDerivedProjection q f
  let e := evenBlockFourRightRootEquiv
  change evenBlockFourRightAltHom
      (e.symm ⟨r x, x.2⟩) = r x
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨r x, x.2⟩)
  exact h

public theorem evenBlockFourRightSubextensionProjection_ker_eq_comap
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    (evenBlockFourRightSubextensionProjection q f).ker =
      (evenBlockFourRootPreimageDerivedProjection q f).ker.comap
        (evenBlockFourRightSubextension q f).subtype := by
  let r := evenBlockFourRootPreimageDerivedProjection q f
  let e := evenBlockFourRightRootEquiv
  let r0 := (r.comp
      (evenBlockFourRightSubextension q f).subtype).codRestrict
    evenBlockFourRightRoot (fun x => x.2)
  calc
    (evenBlockFourRightSubextensionProjection q f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = r.ker.comap
        (evenBlockFourRightSubextension q f).subtype := by
      ext x
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

public theorem evenBlockFourRightSubextensionProjection_ker_le_center
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hker : f.ker ≤ Subgroup.center H) :
    (evenBlockFourRightSubextensionProjection q f).ker ≤
      Subgroup.center (evenBlockFourRightSubextension q f) := by
  rw [evenBlockFourRightSubextensionProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (evenBlockFourRootPreimageDerivedProjection_ker_le_center
      q f hker hx) y.1

public theorem evenBlockFourRight_pair
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (evenBlockFourRightSubextensionProjection q f).ker ≤ 2 ∧
      ∃ z : evenBlockFourRightSubextension q f,
        evenBlockFourRightSubextensionProjection q f z =
          evenBlockFourRho ∧
        (evenBlockFourRightSubextensionProjection q f).ker =
          Subgroup.zpowers (z ^ 2) := by
  let R := evenBlockFourRootPreimageDerived q f
  let r := evenBlockFourRootPreimageDerivedProjection q f
  let S := evenBlockFourRightSubextension q f
  let s := evenBlockFourRightSubextensionProjection q f
  obtain ⟨hrootCard, y, hy, hrootKer⟩ :=
    evenBlockFourRoot_pair q f hf hker
  let inc : s.ker → r.ker := fun x =>
    ⟨(((x : s.ker) : S) : R), by
      have hfac :=
        evenBlockFourRightSubextensionProjection_fac q f
          ((x : s.ker) : S)
      rw [MonoidHom.mem_ker.mp x.2, map_one] at hfac
      exact MonoidHom.mem_ker.mpr hfac.symm⟩
  have hinc : Function.Injective inc := by
    intro x z hxz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : r.ker => (w : R)) hxz
  have hcard : Nat.card s.ker ≤ 2 :=
    (Nat.card_le_card_of_injective inc hinc).trans hrootCard
  obtain ⟨t, ht⟩ :=
    evenBlockFourRootPreimageDerivedProjection_surjective q f hf
      evenBlockFourShift
  let z0 : R := t * y * t⁻¹
  have hz0proj : r z0 =
      evenBlockFourRightAltHom evenBlockFourRho := by
    dsimp [z0]
    rw [map_mul, map_mul, map_inv, ht, hy]
    exact evenBlockFourShift_conj_rho
  have hz0mem : z0 ∈ S :=
    ⟨evenBlockFourRho, hz0proj.symm⟩
  let z : S := ⟨z0, hz0mem⟩
  have hzproj : s z = evenBlockFourRho := by
    apply evenBlockFourRightAltHom_injective
    rw [evenBlockFourRightSubextensionProjection_fac q f z,
      hz0proj]
  have hy2ker : y ^ 2 ∈ r.ker := by
    rw [hrootKer]
    exact Subgroup.mem_zpowers (y ^ 2)
  have hy2center : y ^ 2 ∈ Subgroup.center R :=
    evenBlockFourRootPreimageDerivedProjection_ker_le_center
      q f hker hy2ker
  have hfixed : t * y ^ 2 * t⁻¹ = y ^ 2 := by
    have hc := Subgroup.mem_center_iff.mp hy2center t
    rw [hc]
    simp
  have hz0square : z0 ^ 2 = y ^ 2 := by
    dsimp [z0]
    calc
      (t * y * t⁻¹) ^ 2 = t * y ^ 2 * t⁻¹ := by
        simp only [pow_two]
        group
      _ = y ^ 2 := hfixed
  have hsker : s.ker = Subgroup.zpowers (z ^ 2) := by
    ext x
    constructor
    · intro hx
      have hxroot : ((x : S) : R) ∈ r.ker := by
        have hx' : x ∈
            (evenBlockFourRightSubextensionProjection q f).ker := hx
        rw [evenBlockFourRightSubextensionProjection_ker_eq_comap]
          at hx'
        exact hx'
      rw [hrootKer] at hxroot
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxroot
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨n, ?_⟩
      apply Subtype.ext
      change (z0 ^ 2) ^ n = ((x : S) : R)
      rw [hz0square]
      exact hn
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [evenBlockFourRightSubextensionProjection_ker_eq_comap]
      change ((x : S) : R) ∈ r.ker
      rw [hrootKer, Subgroup.mem_zpowers_iff]
      refine ⟨n, ?_⟩
      rw [← hz0square]
      exact congrArg (fun w : S => (w : R)) hn
  exact ⟨hcard, z, hzproj, hsker⟩

public theorem evenBlockFourRootPreimageProjection_fac
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (x : evenBlockFourRootPreimage q f) :
    evenBlockFourRootAltHom q
        (evenBlockFourRootPreimageProjection q f x) = f x := by
  let e := evenBlockFourRootEquiv q
  change evenBlockFourRootAltHom q
      (e.symm ⟨f x, x.2⟩) = f x
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, x.2⟩)

public theorem evenBlockFourRootPreimageDerivedProjection_fac
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (x : evenBlockFourRootPreimageDerived q f) :
    evenBlockFourRootAltHom q
        (evenBlockFourRootPreimageDerivedProjection q f x) =
      f ((((x : evenBlockFourRootPreimageDerived q f) :
        evenBlockFourRootPreimage q f) : H)) := by
  exact evenBlockFourRootPreimageProjection_fac q f
    ((x : evenBlockFourRootPreimageDerived q f) :
      evenBlockFourRootPreimage q f)

public noncomputable def evenBlockFourRightEmbeddingToBlock
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRightSubextension q f →*
      alternatingBlockPreimage (q + 5) 4 f where
  toFun x :=
    ⟨((((x : evenBlockFourRightSubextension q f) :
        evenBlockFourRootPreimageDerived q f) :
      evenBlockFourRootPreimage q f) : H), by
      change f (((((x : evenBlockFourRightSubextension q f) :
          evenBlockFourRootPreimageDerived q f) :
        evenBlockFourRootPreimage q f) : H)) ∈
        (alternatingProdBlockHom (q + 5) 4).range
      refine ⟨(1,
        evenBlockFourRightSubextensionProjection q f x), ?_⟩
      calc
        alternatingProdBlockHom (q + 5) 4
            (1, evenBlockFourRightSubextensionProjection q f x) =
          evenBlockFourRootAltHom q
            (evenBlockFourRightAltHom
              (evenBlockFourRightSubextensionProjection q f x)) :=
                (evenBlockFourRootAltHom_right q _).symm
        _ = evenBlockFourRootAltHom q
            (evenBlockFourRootPreimageDerivedProjection q f
              ((x : evenBlockFourRightSubextension q f) :
                evenBlockFourRootPreimageDerived q f)) := by
              rw [evenBlockFourRightSubextensionProjection_fac]
        _ = f (((((x : evenBlockFourRightSubextension q f) :
              evenBlockFourRootPreimageDerived q f) :
            evenBlockFourRootPreimage q f) : H)) :=
              evenBlockFourRootPreimageDerivedProjection_fac q f _⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

public theorem evenBlockFourRightEmbeddingToBlock_projection
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (x : evenBlockFourRightSubextension q f) :
    alternatingBlockPreimageProjection (q + 5) 4 f
        (evenBlockFourRightEmbeddingToBlock q f x) =
      (1, evenBlockFourRightSubextensionProjection q f x) := by
  apply alternatingProdBlockHom_injective
  calc
    alternatingProdBlockHom (q + 5) 4
        (alternatingBlockPreimageProjection (q + 5) 4 f
          (evenBlockFourRightEmbeddingToBlock q f x)) =
      f (evenBlockFourRightEmbeddingToBlock q f x) :=
        alternatingBlockPreimageProjection_fac (q + 5) 4 f _
    _ = evenBlockFourRootAltHom q
        (evenBlockFourRootPreimageDerivedProjection q f
          ((x : evenBlockFourRightSubextension q f) :
            evenBlockFourRootPreimageDerived q f)) :=
          (evenBlockFourRootPreimageDerivedProjection_fac q f _).symm
    _ = evenBlockFourRootAltHom q
        (evenBlockFourRightAltHom
          (evenBlockFourRightSubextensionProjection q f x)) := by
            rw [evenBlockFourRightSubextensionProjection_fac]
    _ = alternatingProdBlockHom (q + 5) 4
        (1, evenBlockFourRightSubextensionProjection q f x) :=
          evenBlockFourRootAltHom_right q _

public abbrev evenBlockFourRightKernelInBlock
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    Subgroup (alternatingBlockPreimage (q + 5) 4 f) :=
  (evenBlockFourRightSubextensionProjection q f).ker.map
    (evenBlockFourRightEmbeddingToBlock q f)

open scoped commutatorElement

public theorem evenBlockFour_commutatorElement_eq_one_of_left_perfect_of_mem_center
    {A H : Type*} [Group A] [Group H] [Group.IsPerfect A]
    (u : A →* H) (y : H)
    (hc : ∀ a : A, ⁅u a, y⁆ ∈ Subgroup.center H)
    (a : A) : ⁅u a, y⁆ = 1 := by
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun x z => Subtype.ext
      (Subgroup.mem_center_iff.mp x.2 z.1).symm }
  let φ : A →* Subgroup.center H := {
    toFun := fun x => ⟨⁅u x, y⁆, hc x⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro a₁ a₂
      apply Subtype.ext
      change ⁅u (a₁ * a₂), y⁆ = ⁅u a₁, y⁆ * ⁅u a₂, y⁆
      rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
      have hc₂ := hc a₂
      have hconj : u a₁ * ⁅u a₂, y⁆ * (u a₁)⁻¹ = ⁅u a₂, y⁆ := by
        have hcomm := Subgroup.mem_center_iff.mp hc₂ (u a₁)
        rw [hcomm]
        simp
      rw [hconj]
      exact (Subgroup.mem_center_iff.mp hc₂ ⁅u a₁, y⁆).symm }
  have hφ : φ a = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker φ
      (Group.IsPerfect.mem_commutator (g := a))
  exact congrArg Subtype.val hφ

public theorem evenBlockFour_embeddings_commute
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection (q + 5) 4 f))
    (y : evenBlockFourRightSubextension q f) :
    Commute
      (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f x)
      (evenBlockFourRightEmbeddingToBlock q f y) := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let EL := prodLeftPreimage r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let iL : DL →* E :=
    evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f
  let iR := evenBlockFourRightEmbeddingToBlock q f
  let s := evenBlockFourRightSubextensionProjection q f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 4 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 4 f hker
  let : Group.IsPerfect DL :=
    commutator_isPerfect_of_surjective_of_ker_le_center
      (prodLeftPreimageProjection r)
      (prodLeftPreimageProjection_surjective r hr)
      (prodLeftPreimageProjection_ker_le_center r hrker)
  have hLproj (z : DL) : r (iL z) = (rL z, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp z.1.2.2
  have hRproj (z : evenBlockFourRightSubextension q f) :
      r (iR z) = (1, s z) :=
    evenBlockFourRightEmbeddingToBlock_projection q f z
  have hc (z : DL) : ⁅iL z, iR y⁆ ∈ Subgroup.center E := by
    apply hrker
    rw [MonoidHom.mem_ker, map_commutatorElement, hLproj, hRproj]
    simp [commutatorElement_def]
  rw [← commutatorElement_eq_one_iff_commute]
  exact evenBlockFour_commutatorElement_eq_one_of_left_perfect_of_mem_center
    iL (iR y) hc x

public noncomputable def evenBlockFourDerivedMulHom
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (q + 5) 4 f) ×
        evenBlockFourRightSubextension q f →*
      alternatingBlockPreimage (q + 5) 4 f where
  toFun x :=
    evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f x.1 *
      evenBlockFourRightEmbeddingToBlock q f x.2
  map_one' := by simp
  map_mul' x y := by
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul]
    have hc := evenBlockFour_embeddings_commute
      q f hf hker y.1 x.2
    calc
      _ = evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f x.1 *
          (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f y.1 *
            evenBlockFourRightEmbeddingToBlock q f x.2) *
          evenBlockFourRightEmbeddingToBlock q f y.2 := by
            simp only [mul_assoc]
      _ = evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f x.1 *
          (evenBlockFourRightEmbeddingToBlock q f x.2 *
            evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f y.1) *
          evenBlockFourRightEmbeddingToBlock q f y.2 := by
            rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

public abbrev evenBlockFourDerivedProduct
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Subgroup (alternatingBlockPreimage (q + 5) 4 f) :=
  (evenBlockFourDerivedMulHom q f hf hker).range

public theorem evenBlockFourDerivedMulHom_projection
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (q + 5) 4 f) ×
        evenBlockFourRightSubextension q f) :
    alternatingBlockPreimageProjection (q + 5) 4 f
        (evenBlockFourDerivedMulHom q f hf hker x) =
      (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (q + 5) 4 f) x.1,
        evenBlockFourRightSubextensionProjection q f x.2) := by
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let iL := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f
  let iR := evenBlockFourRightEmbeddingToBlock q f
  let rL := prodLeftPreimageDerivedProjection r
  let s := evenBlockFourRightSubextensionProjection q f
  have hLproj : r (iL x.1) = (rL x.1, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp x.1.1.2.2
  have hRproj : r (iR x.2) = (1, s x.2) :=
    evenBlockFourRightEmbeddingToBlock_projection q f x.2
  change r (iL x.1 * iR x.2) = _
  rw [map_mul, hLproj, hRproj]
  rfl

public theorem evenBlockFourDerivedProduct_decomposition
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    ∀ x : alternatingBlockPreimage (q + 5) 4 f,
      ∃ k : (alternatingBlockPreimageProjection (q + 5) 4 f).ker,
        ∃ d : evenBlockFourDerivedProduct q f hf hker,
          (k : alternatingBlockPreimage (q + 5) 4 f) *
              (d : alternatingBlockPreimage (q + 5) 4 f) = x := by
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let rL := prodLeftPreimageDerivedProjection r
  let s := evenBlockFourRightSubextensionProjection q f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 4 f hf
  have hrL : Function.Surjective rL :=
    prodLeftPreimageDerivedProjection_surjective r hr
  have hs : Function.Surjective s :=
    evenBlockFourRightSubextensionProjection_surjective q f hf
  intro x
  obtain ⟨xL, hxL⟩ := hrL (r x).1
  obtain ⟨xR, hxR⟩ := hs (r x).2
  let d0 := evenBlockFourDerivedMulHom q f hf hker (xL, xR)
  have hdproj : r d0 = r x := by
    rw [evenBlockFourDerivedMulHom_projection, hxL, hxR]
  have hk : x * d0⁻¹ ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdproj]
    simp
  let k : r.ker := ⟨x * d0⁻¹, hk⟩
  let d : evenBlockFourDerivedProduct q f hf hker :=
    ⟨d0, ⟨(xL, xR), rfl⟩⟩
  exact ⟨k, d, by simp [k, d, d0]⟩

public theorem evenBlockFourDerivedProduct_ker_inf_eq_of_kernel_eq
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f) :
    (alternatingBlockPreimageProjection (q + 5) 4 f).ker ⊓
        evenBlockFourDerivedProduct q f hf hker =
      evenBlockLeftDerivedKernelInBlock (q + 5) 4 f := by
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let iL := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f
  let iR := evenBlockFourRightEmbeddingToBlock q f
  let rL := prodLeftPreimageDerivedProjection r
  let s := evenBlockFourRightSubextensionProjection q f
  apply le_antisymm
  · rintro z ⟨hzker, hzprod⟩
    obtain ⟨x, rfl⟩ := hzprod
    have hpair : (rL x.1, s x.2) = 1 := by
      rw [← evenBlockFourDerivedMulHom_projection q f hf hker x]
      exact MonoidHom.mem_ker.mp hzker
    have hxL : x.1 ∈ rL.ker :=
      MonoidHom.mem_ker.mpr (congrArg Prod.fst hpair)
    have hxR : x.2 ∈ s.ker :=
      MonoidHom.mem_ker.mpr (congrArg Prod.snd hpair)
    have hiL : iL x.1 ∈ evenBlockLeftDerivedKernelInBlock
        (q + 5) 4 f := ⟨x.1, hxL, rfl⟩
    have hiR : iR x.2 ∈ evenBlockFourRightKernelInBlock
        q f := ⟨x.2, hxR, rfl⟩
    rw [← hfusion] at hiR
    exact Subgroup.mul_mem _ hiL hiR
  · intro z hz
    constructor
    · obtain ⟨x, hx, rfl⟩ := hz
      change r (iL x) = 1
      have hproj := evenBlockFourDerivedMulHom_projection
        q f hf hker (x, 1)
      simpa [iL, evenBlockFourDerivedMulHom] using hproj.trans
        (Prod.ext (MonoidHom.mem_ker.mp hx) (by simp))
    · obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨(x, 1), by simp [evenBlockFourDerivedMulHom]⟩

public def evenBlockFourLeftRootEmbedding (q : Nat) :
    Fin 5 ↪ Fin ((q + 5) + 4) :=
  ⟨fun i => ⟨i, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg
      (fun x : Fin ((q + 5) + 4) => x.val) h)⟩

private theorem evenBlockFourLeftRootEmbedding_val (q : Nat) (j : Fin 5) :
    (evenBlockFourLeftRootEmbedding q j).val = j.val := rfl

public noncomputable def evenBlockFourLeftRootPermHom (q : Nat) :
    Equiv.Perm (Fin 5) →* Equiv.Perm (Fin ((q + 5) + 4)) :=
  Equiv.Perm.viaEmbeddingHom (evenBlockFourLeftRootEmbedding q)

set_option linter.unnecessarySimpa false in
public theorem sign_evenBlockFourLeftRootPermHom (q : Nat)
    (σ : Equiv.Perm (Fin 5)) :
    Equiv.Perm.sign (evenBlockFourLeftRootPermHom q σ) =
      Equiv.Perm.sign σ := by
  unfold evenBlockFourLeftRootPermHom
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  simpa [Equiv.Perm.viaEmbedding] using
    (Equiv.Perm.sign_extendDomain σ
      (Equiv.ofInjective (evenBlockFourLeftRootEmbedding q).1
        (evenBlockFourLeftRootEmbedding q).2))

public noncomputable def evenBlockFourLeftRootAltHom (q : Nat) :
    alternatingGroup (Fin 5) →*
      alternatingGroup (Fin ((q + 5) + 4)) where
  toFun σ := ⟨evenBlockFourLeftRootPermHom q σ, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockFourLeftRootPermHom]
    exact σ.2⟩
  map_one' := by
    apply Subtype.ext
    simp [evenBlockFourLeftRootPermHom]
  map_mul' a b := by
    apply Subtype.ext
    simp [evenBlockFourLeftRootPermHom]

public theorem evenBlockFourLeftRootAltHom_eq_block_tail
    (q : Nat) (σ : alternatingGroup (Fin 5)) :
    evenBlockFourLeftRootAltHom q σ =
      alternatingProdBlockHom (q + 5) 4
        (RootAm.tailAltHom q 5 (by omega) σ, 1) := by
  apply Subtype.ext
  simp only [evenBlockFourLeftRootAltHom,
    coe_alternatingProdBlockHom_apply, RootAm.tailAltHom]
  change evenBlockFourLeftRootPermHom q σ =
    permProdBlockHom (q + 5) 4
      (RootAm.tailPermHom q 5 (by omega) σ, 1)
  rw [permProdBlockHom_apply]
  apply Equiv.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases hleft : x < q + 5
  · let i : Fin (q + 5) := ⟨x, hleft⟩
    have hcoord : (⟨x, hx⟩ : Fin ((q + 5) + 4)) =
        finSumFinEquiv (Sum.inl i) := by
      apply Fin.ext
      rfl
    by_cases hroot : x < 5
    · let j : Fin 5 := ⟨x, hroot⟩
      have hembL : evenBlockFourLeftRootEmbedding q j =
          (⟨x, hx⟩ : Fin ((q + 5) + 4)) := by
        apply Fin.ext
        rfl
      have hembT : RootAm.tailEmbedding q 5 (by omega) j = i := by
        apply Fin.ext
        rfl
      rw [evenBlockFourLeftRootPermHom,
        ← hembL, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply]
      rw [hembL, hcoord]
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
        Equiv.Perm.sumCongr_apply, Sum.map_inl]
      change evenBlockFourLeftRootEmbedding q (σ.1 j) =
        finSumFinEquiv (Sum.inl
          (RootAm.tailPermHom q 5 (by omega) σ.1 i))
      rw [← hembT, RootAm.tailPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply]
      apply Fin.ext
      rfl
    · have hnotL : (⟨x, hx⟩ : Fin ((q + 5) + 4)) ∉
          Set.range (evenBlockFourLeftRootEmbedding q) := by
        rintro ⟨j, hj⟩
        have hval := congrArg Fin.val hj
        rw [evenBlockFourLeftRootEmbedding_val] at hval
        change j.val = x at hval
        omega
      have hnotT : i ∉ Set.range (RootAm.tailEmbedding q 5 (by omega)) := by
        rintro ⟨j, hj⟩
        have hval := congrArg Fin.val hj
        dsimp [RootAm.tailEmbedding, i] at hval
        omega
      rw [evenBlockFourLeftRootPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hnotL,
        hcoord]
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
        Equiv.Perm.sumCongr_apply, Sum.map_inl]
      rw [RootAm.tailPermHom, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hnotT]
  · have hq : q + 5 ≤ x := by omega
    let i : Fin 4 := ⟨x - (q + 5), by omega⟩
    have hcoord : (⟨x, hx⟩ : Fin ((q + 5) + 4)) =
        finSumFinEquiv (Sum.inr i) := by
      apply Fin.ext
      dsimp [i]
      omega
    have hnotL : (⟨x, hx⟩ : Fin ((q + 5) + 4)) ∉
        Set.range (evenBlockFourLeftRootEmbedding q) := by
      rintro ⟨j, hj⟩
      have hval := congrArg Fin.val hj
      rw [evenBlockFourLeftRootEmbedding_val] at hval
      change j.val = x at hval
      omega
    rw [evenBlockFourLeftRootPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hnotL,
      hcoord]
    simp [Equiv.permCongr_apply]

public def evenBlockFourLeftPoint (q : Nat) (i : Fin 4) :
    Fin ((q + 5) + 4) := ⟨i, by omega⟩

public def evenBlockFourRightPoint (q : Nat) (i : Fin 4) :
    Fin ((q + 5) + 4) := ⟨q + 5 + i, by omega⟩

public theorem evenBlockFourLeftPoint_ne_right
    (q : Nat) (i j : Fin 4) :
    evenBlockFourLeftPoint q i ≠
      evenBlockFourRightPoint q j := by
  intro h
  have h' := congrArg Fin.val h
  dsimp [evenBlockFourLeftPoint,
    evenBlockFourRightPoint] at h'
  omega

public def evenBlockFourSwapPerm (q : Nat) :
    Equiv.Perm (Fin ((q + 5) + 4)) :=
  (Equiv.swap (evenBlockFourLeftPoint q 0)
      (evenBlockFourRightPoint q 0) *
    Equiv.swap (evenBlockFourLeftPoint q 1)
      (evenBlockFourRightPoint q 1)) *
  (Equiv.swap (evenBlockFourLeftPoint q 2)
      (evenBlockFourRightPoint q 2) *
    Equiv.swap (evenBlockFourLeftPoint q 3)
      (evenBlockFourRightPoint q 3))

public def evenBlockFourSwap (q : Nat) :
    alternatingGroup (Fin ((q + 5) + 4)) :=
  ⟨evenBlockFourSwapPerm q, by
    apply Subgroup.mul_mem
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr
          (evenBlockFourLeftPoint_ne_right q 0 0))
        (Equiv.Perm.swap_isSwap_iff.mpr
          (evenBlockFourLeftPoint_ne_right q 1 1))
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr
          (evenBlockFourLeftPoint_ne_right q 2 2))
        (Equiv.Perm.swap_isSwap_iff.mpr
          (evenBlockFourLeftPoint_ne_right q 3 3))⟩

public theorem evenBlockFourSwap_map_leftRootEmbedding (q : Nat)
    (i : Fin 5) :
    evenBlockFourSwapPerm q
        (evenBlockFourLeftRootEmbedding q i) =
      evenBlockFourRootEmbedding q (finRotate 5 i) := by
  fin_cases i
  · change evenBlockFourSwapPerm q ⟨0, by omega⟩ = ⟨q + 5, by omega⟩
    apply Fin.ext
    simp [evenBlockFourSwapPerm, evenBlockFourLeftPoint,
      evenBlockFourRightPoint, Equiv.swap_apply_def]
  · change evenBlockFourSwapPerm q ⟨1, by omega⟩ = ⟨q + 5 + 1, by omega⟩
    apply Fin.ext
    simp [evenBlockFourSwapPerm, evenBlockFourLeftPoint,
      evenBlockFourRightPoint, Equiv.swap_apply_def]
  · change evenBlockFourSwapPerm q ⟨2, by omega⟩ = ⟨q + 5 + 2, by omega⟩
    apply Fin.ext
    simp [evenBlockFourSwapPerm, evenBlockFourLeftPoint,
      evenBlockFourRightPoint, Equiv.swap_apply_def]
  · change evenBlockFourSwapPerm q ⟨3, by omega⟩ = ⟨q + 5 + 3, by omega⟩
    apply Fin.ext
    simp [evenBlockFourSwapPerm, evenBlockFourLeftPoint,
      evenBlockFourRightPoint, Equiv.swap_apply_def]
  · change evenBlockFourSwapPerm q ⟨4, by omega⟩ = ⟨4, by omega⟩
    apply Fin.ext
    simp [evenBlockFourSwapPerm, evenBlockFourLeftPoint,
      evenBlockFourRightPoint, Equiv.swap_apply_def]

public theorem evenBlockFour_viaEmbedding_conj
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (e₁ e₂ : ι ↪ α) (c : Equiv.Perm ι) (u : Equiv.Perm α)
    (hmap : ∀ i, u (e₁ i) = e₂ (c i))
    (σ : Equiv.Perm ι) :
    u * Equiv.Perm.viaEmbedding σ e₁ * u⁻¹ =
      Equiv.Perm.viaEmbedding (c * σ * c⁻¹) e₂ := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range e₂
  · obtain ⟨j, rfl⟩ := hx
    have hpre : u⁻¹ (e₂ j) = e₁ (c⁻¹ j) := by
      have hc : c (c⁻¹ j) = j := c.apply_symm_apply j
      calc
        u⁻¹ (e₂ j) = u⁻¹ (e₂ (c (c⁻¹ j))) := by rw [hc]
        _ = u⁻¹ (u (e₁ (c⁻¹ j))) := by rw [hmap]
        _ = e₁ (c⁻¹ j) := u.symm_apply_apply _
    simp only [Equiv.Perm.mul_apply, hpre,
      Equiv.Perm.viaEmbedding_apply]
    rw [hmap]
  · have hpre : u⁻¹ x ∉ Set.range e₁ := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨c i, ?_⟩
      rw [← hmap i, hi]
      exact u.apply_symm_apply x
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hpre,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
    exact u.apply_symm_apply x

public theorem evenBlockFourSwap_conj_leftRoot
    (q : Nat) (x : alternatingGroup (Fin 5)) :
    evenBlockFourSwap q *
        evenBlockFourLeftRootAltHom q x *
        (evenBlockFourSwap q)⁻¹ =
      evenBlockFourRootAltHom q
        (evenBlockFourShift * x * evenBlockFourShift⁻¹) := by
  apply Subtype.ext
  change evenBlockFourSwapPerm q *
      evenBlockFourLeftRootPermHom q x.1 *
      (evenBlockFourSwapPerm q)⁻¹ =
    evenBlockFourRootPermHom q
      (finRotate 5 * x.1 * (finRotate 5)⁻¹)
  exact evenBlockFour_viaEmbedding_conj
    (evenBlockFourLeftRootEmbedding q)
    (evenBlockFourRootEmbedding q)
    (finRotate 5) (evenBlockFourSwapPerm q)
    (evenBlockFourSwap_map_leftRootEmbedding q) x.1

public theorem evenBlockFourSwap_conj_block_tail
    (q : Nat) (x : alternatingGroup (Fin 5)) :
    evenBlockFourSwap q *
        alternatingProdBlockHom (q + 5) 4
          (RootAm.tailAltHom q 5 (by omega) x, 1) *
        (evenBlockFourSwap q)⁻¹ =
      evenBlockFourRootAltHom q
        (evenBlockFourShift * x * evenBlockFourShift⁻¹) := by
  rw [← evenBlockFourLeftRootAltHom_eq_block_tail]
  exact evenBlockFourSwap_conj_leftRoot q x

public def evenBlockFourLeftRootDerivedEmbedding
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    centralRootAmPreimageDerived q 5 (by omega)
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (q + 5) 4 f)) →* H :=
  (evenBlockLeftDerivedEmbedding (q + 5) 4 f).comp
    ((centralRootAmPreimage q 5 (by omega)
      (prodLeftPreimageDerivedProjection
        (alternatingBlockPreimageProjection (q + 5) 4 f))).subtype.comp
      (centralRootAmPreimageDerived q 5 (by omega)
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (q + 5) 4 f))).subtype)

public theorem exists_rightFour_conjugate_of_swap
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (d : H) (hd : f d = evenBlockFourSwap q)
    (xL : centralRootAmPreimageDerived q 5 (by omega)
      (prodLeftPreimageDerivedProjection
        (alternatingBlockPreimageProjection (q + 5) 4 f)))
    (hxL : centralRootAmPreimageDerivedProjection q 5 (by omega)
        (prodLeftPreimageDerivedProjection
          (alternatingBlockPreimageProjection (q + 5) 4 f)) xL =
      (⟨RootFourSubgroup.rho1 0,
        RootFourSubgroup.rho1_mem_alternating 0⟩ :
        alternatingGroup (Fin 5))) :
    ∃ yR : evenBlockFourRightSubextension q f,
      evenBlockFourRightSubextensionProjection q f yR =
        evenBlockFourRho ∧
      d * evenBlockFourLeftRootDerivedEmbedding q f xL * d⁻¹ =
        (((yR : evenBlockFourRightSubextension q f) :
          evenBlockFourRootPreimageDerived q f) :
          evenBlockFourRootPreimage q f) := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let EL := prodLeftPreimage r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let RL := centralRootAmPreimage q 5 (by omega) rL
  let RLD := centralRootAmPreimageDerived q 5 (by omega) rL
  let rRootL := centralRootAmPreimageDerivedProjection q 5 (by omega) rL
  let RG := evenBlockFourRootPreimage q f
  let RDG := evenBlockFourRootPreimageDerived q f
  let rG := evenBlockFourRootPreimageDerivedProjection q f
  let s := evenBlockFourRightSubextensionProjection q f
  let iL : DL →* H := evenBlockLeftDerivedEmbedding (q + 5) 4 f
  let iRoot : RL →* H := iL.comp RL.subtype
  have hxproj (x : DL) : r (((x : DL) : EL) : E) = (rL x, 1) := by
    apply Prod.ext
    · rfl
    · exact Subgroup.mem_bot.mp x.1.2.2
  have hximage (x : DL) : f (iL x) =
      alternatingProdBlockHom (q + 5) 4 (rL x, 1) := by
    calc
      f (iL x) = alternatingProdBlockHom (q + 5) 4
          (r (((x : DL) : EL) : E)) :=
        (alternatingBlockPreimageProjection_fac
          (q + 5) 4 f (((x : DL) : EL) : E)).symm
      _ = alternatingProdBlockHom (q + 5) 4 (rL x, 1) := by
        rw [hxproj]
  have hxroot (x : RL) :
      RootAm.tailAltHom q 5 (by omega)
          (centralRootAmPreimageProjection q 5 (by omega) rL x) =
        rL (x : DL) := by
    let e := centralRootAmEquiv q 5 (by omega)
    exact congrArg Subtype.val
      (e.apply_symm_apply
        (⟨rL (x : DL), x.2⟩ : RootAm.rootAm q 5 (by omega)))
  have hximageRoot (x : RL) : f (iRoot x) =
      alternatingProdBlockHom (q + 5) 4
        (RootAm.tailAltHom q 5 (by omega)
          (centralRootAmPreimageProjection q 5 (by omega) rL x), 1) := by
    rw [show iRoot x = iL (x : DL) by rfl, hximage, hxroot]
  have hzmem (x : RL) : d * iRoot x * d⁻¹ ∈ RG := by
    change f (d * iRoot x * d⁻¹) ∈
      (evenBlockFourRootAltHom q).range
    refine ⟨evenBlockFourShift *
        centralRootAmPreimageProjection q 5 (by omega) rL x *
        evenBlockFourShift⁻¹, ?_⟩
    calc
      evenBlockFourRootAltHom q
          (evenBlockFourShift *
            centralRootAmPreimageProjection q 5 (by omega) rL x *
            evenBlockFourShift⁻¹) =
        evenBlockFourSwap q *
          alternatingProdBlockHom (q + 5) 4
            (RootAm.tailAltHom q 5 (by omega)
              (centralRootAmPreimageProjection q 5 (by omega) rL x), 1) *
          (evenBlockFourSwap q)⁻¹ :=
            (evenBlockFourSwap_conj_block_tail q _).symm
      _ = f d * f (iRoot x) * (f d)⁻¹ := by
        rw [hd, hximageRoot]
      _ = f (d * iRoot x * d⁻¹) := by
        rw [map_mul, map_mul, map_inv]
  let zG (x : RL) : RG := ⟨d * iRoot x * d⁻¹, hzmem x⟩
  have hzproj (x : RL) :
      evenBlockFourRootPreimageProjection q f (zG x) =
        evenBlockFourShift *
          centralRootAmPreimageProjection q 5 (by omega) rL x *
          evenBlockFourShift⁻¹ := by
    apply evenBlockFourRootAltHom_injective q
    calc
      evenBlockFourRootAltHom q
          (evenBlockFourRootPreimageProjection q f (zG x)) =
        f (zG x) :=
          evenBlockFourRootPreimageProjection_fac q f (zG x)
      _ = evenBlockFourSwap q *
          alternatingProdBlockHom (q + 5) 4
            (RootAm.tailAltHom q 5 (by omega)
              (centralRootAmPreimageProjection q 5 (by omega) rL x), 1) *
          (evenBlockFourSwap q)⁻¹ := by
            change f (d * iRoot x * d⁻¹) = _
            rw [map_mul, map_mul, map_inv, hd, hximageRoot]
      _ = evenBlockFourRootAltHom q
          (evenBlockFourShift *
            centralRootAmPreimageProjection q 5 (by omega) rL x *
            evenBlockFourShift⁻¹) :=
              evenBlockFourSwap_conj_block_tail q _
  let φ : RL →* RG := {
    toFun := zG
    map_one' := by
      apply Subtype.ext
      simp [zG, iRoot, iL]
    map_mul' := by
      intro x y
      apply Subtype.ext
      change d * iRoot (x * y) * d⁻¹ =
        (d * iRoot x * d⁻¹) * (d * iRoot y * d⁻¹)
      rw [map_mul]
      group }
  have hmap : (commutator RL).map φ ≤ commutator RG := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hyGmem : φ (xL : RL) ∈ commutator RG := by
    apply hmap
    exact ⟨(xL : RL), xL.2, rfl⟩
  let yG : RDG := ⟨φ (xL : RL), hyGmem⟩
  have hyGproj : rG yG =
      evenBlockFourRightAltHom evenBlockFourRho := by
    change evenBlockFourRootPreimageProjection q f
        (zG (xL : RL)) = _
    rw [hzproj]
    change evenBlockFourShift *
        (centralRootAmPreimageDerivedProjection q 5 (by omega) rL xL) *
        evenBlockFourShift⁻¹ = _
    rw [hxL]
    exact evenBlockFourShift_conj_rho
  have hyGright : yG ∈ evenBlockFourRightSubextension q f :=
    ⟨evenBlockFourRho, hyGproj.symm⟩
  let yR : evenBlockFourRightSubextension q f :=
    ⟨yG, hyGright⟩
  refine ⟨yR, ?_, rfl⟩
  apply evenBlockFourRightAltHom_injective
  rw [evenBlockFourRightSubextensionProjection_fac q f yR,
    hyGproj]

public def evenBlockFourRightEmbeddingToAmbient
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRightSubextension q f →* H :=
  (alternatingBlockPreimage (q + 5) 4 f).subtype.comp
    (evenBlockFourRightEmbeddingToBlock q f)

public abbrev evenBlockFourRightKernel
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    Subgroup H :=
  (evenBlockFourRightSubextensionProjection q f).ker.map
    (evenBlockFourRightEmbeddingToAmbient q f)

public theorem evenBlockFourRightKernel_le_ker
    {H : Type} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    evenBlockFourRightKernel q f ≤ f.ker := by
  rintro z ⟨x, hx, rfl⟩
  rw [MonoidHom.mem_ker]
  have hproj := evenBlockFourRightEmbeddingToBlock_projection q f x
  have hsx : evenBlockFourRightSubextensionProjection q f x = 1 :=
    MonoidHom.mem_ker.mp hx
  have hfac := alternatingBlockPreimageProjection_fac (q + 5) 4 f
    (evenBlockFourRightEmbeddingToBlock q f x)
  rw [hproj, hsx] at hfac
  change f (evenBlockFourRightEmbeddingToBlock q f x) = 1
  calc
    f (evenBlockFourRightEmbeddingToBlock q f x) =
        alternatingProdBlockHom (q + 5) 4 (1, 1) := hfac.symm
    _ = 1 := map_one _

public theorem evenBlockFour_kernel_eq_of_conjugate_generators
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hker : f.ker ≤ Subgroup.center H)
    (yL : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection (q + 5) 4 f))
    (yR : evenBlockFourRightSubextension q f)
    (hL : (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection (q + 5) 4 f)).ker =
        Subgroup.zpowers (yL ^ 2))
    (hR : (evenBlockFourRightSubextensionProjection q f).ker =
        Subgroup.zpowers (yR ^ 2))
    (d : H)
    (hconj : d * evenBlockLeftDerivedEmbedding (q + 5) 4 f yL * d⁻¹ =
      evenBlockFourRightEmbeddingToAmbient q f yR) :
    evenBlockLeftDerivedKernel (q + 5) 4 f =
      evenBlockFourRightKernel q f := by
  have hyL2ker : yL ^ 2 ∈
      (prodLeftPreimageDerivedProjection
        (alternatingBlockPreimageProjection (q + 5) 4 f)).ker := by
    rw [hL]
    exact Subgroup.mem_zpowers (yL ^ 2)
  have hyL2global : evenBlockLeftDerivedEmbedding (q + 5) 4 f
      (yL ^ 2) ∈ f.ker :=
    evenBlockLeftDerivedKernel_le_ker (q + 5) 4 f
      ⟨yL ^ 2, hyL2ker, rfl⟩
  have hyL2center : evenBlockLeftDerivedEmbedding (q + 5) 4 f
      (yL ^ 2) ∈ Subgroup.center H := hker hyL2global
  have hfixed : d * evenBlockLeftDerivedEmbedding (q + 5) 4 f
      (yL ^ 2) * d⁻¹ =
      evenBlockLeftDerivedEmbedding (q + 5) 4 f (yL ^ 2) := by
    have hc := Subgroup.mem_center_iff.mp hyL2center d
    rw [hc]
    simp
  have hsq : evenBlockLeftDerivedEmbedding (q + 5) 4 f (yL ^ 2) =
      evenBlockFourRightEmbeddingToAmbient q f (yR ^ 2) := by
    calc
      evenBlockLeftDerivedEmbedding (q + 5) 4 f (yL ^ 2) =
          d * evenBlockLeftDerivedEmbedding (q + 5) 4 f
            (yL ^ 2) * d⁻¹ := hfixed.symm
      _ = (d * evenBlockLeftDerivedEmbedding (q + 5) 4 f yL * d⁻¹) ^ 2 := by
        rw [map_pow]
        simp [pow_two, mul_assoc]
      _ = (evenBlockFourRightEmbeddingToAmbient q f yR) ^ 2 := by rw [hconj]
      _ = evenBlockFourRightEmbeddingToAmbient q f (yR ^ 2) := by rw [map_pow]
  change (prodLeftPreimageDerivedProjection
      (alternatingBlockPreimageProjection (q + 5) 4 f)).ker.map
        (evenBlockLeftDerivedEmbedding (q + 5) 4 f) =
    (evenBlockFourRightSubextensionProjection q f).ker.map
      (evenBlockFourRightEmbeddingToAmbient q f)
  rw [hL, hR, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hsq]

public theorem evenBlockFour_kernelInBlock_eq_of_global_eq
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hglobal : evenBlockLeftDerivedKernel (q + 5) 4 f =
      evenBlockFourRightKernel q f) :
    evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  apply Subgroup.map_injective E.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_map]
  change evenBlockLeftDerivedKernel (q + 5) 4 f =
    evenBlockFourRightKernel q f
  exact hglobal

public theorem evenBlockFour_kernelInBlock_eq_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let EL := prodLeftPreimage r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let RL := centralRootAmPreimage q 5 (by omega) rL
  let RLD := centralRootAmPreimageDerived q 5 (by omega) rL
  let rRoot := centralRootAmPreimageDerivedProjection q 5 (by omega) rL
  let s := evenBlockFourRightSubextensionProjection q f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 4 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 4 f hker
  obtain ⟨hLcard, yL0, hyL0, hL0⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM (prodLeftPreimageProjection r)
      (prodLeftPreimageProjection_surjective r hr)
      (prodLeftPreimageProjection_ker_le_center r hrker)
  obtain ⟨hRcard, yR0, hyR0, hR0⟩ :=
    evenBlockFourRight_pair q f hf hker
  have hrL : Function.Surjective rL :=
    prodLeftPreimageDerivedProjection_surjective r hr
  have hrRoot : Function.Surjective rRoot :=
    centralRootAmPreimageDerivedProjection_surjective
      q 5 (by omega) rL hrL
  obtain ⟨xL, hxL⟩ := hrRoot
    (⟨RootFourSubgroup.rho1 0,
      RootFourSubgroup.rho1_mem_alternating 0⟩ :
      alternatingGroup (Fin 5))
  let yL : DL := (xL : RL)
  have hrootfac : RootAm.tailAltHom q 5 (by omega) (rRoot xL) =
      rL yL := by
    let e := centralRootAmEquiv q 5 (by omega)
    exact congrArg Subtype.val
      (e.apply_symm_apply
        (⟨rL yL, (xL : RL).2⟩ : RootAm.rootAm q 5 (by omega)))
  have hyL : rL yL =
      (⟨RootFourSubgroup.rho1 q,
        RootFourSubgroup.rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))) := by
    calc
      rL yL = RootAm.tailAltHom q 5 (by omega) (rRoot xL) :=
        hrootfac.symm
      _ = RootAm.tailAltHom q 5 (by omega)
          (⟨RootFourSubgroup.rho1 0,
            RootFourSubgroup.rho1_mem_alternating 0⟩ :
            alternatingGroup (Fin 5)) := by rw [hxL]
      _ = _ := tailAltHom_rho1 q
  have hrLcenter : rL.ker ≤ Subgroup.center DL := by
    intro x hx
    have hx' : (x : EL) ∈ (prodLeftPreimageProjection r).ker := hx
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (prodLeftPreimageProjection_ker_le_center r hrker hx') z
  have hLsq : yL ^ 2 = yL0 ^ 2 :=
    sq_eq_sq_of_apply_eq_of_card_ker_le_two rL hrLcenter hLcard
      (hyL.trans hyL0.symm)
  have hL : rL.ker = Subgroup.zpowers (yL ^ 2) := by
    change rL.ker = Subgroup.zpowers (yL0 ^ 2) at hL0
    rw [hL0, hLsq]
  obtain ⟨d, hd⟩ := hf (evenBlockFourSwap q)
  obtain ⟨yR, hyR, hconjRoot⟩ :=
    exists_rightFour_conjugate_of_swap q f d hd xL hxL
  have hscenter : s.ker ≤
      Subgroup.center (evenBlockFourRightSubextension q f) :=
    evenBlockFourRightSubextensionProjection_ker_le_center
      q f hker
  have hRsq : yR ^ 2 = yR0 ^ 2 :=
    sq_eq_sq_of_apply_eq_of_card_ker_le_two s hscenter hRcard
      (hyR.trans hyR0.symm)
  have hR : s.ker = Subgroup.zpowers (yR ^ 2) := by
    rw [hR0, hRsq]
  have hconj : d * evenBlockLeftDerivedEmbedding (q + 5) 4 f yL * d⁻¹ =
      evenBlockFourRightEmbeddingToAmbient q f yR := by
    simpa [yL, evenBlockFourLeftRootDerivedEmbedding,
      evenBlockFourRightEmbeddingToAmbient,
      evenBlockFourRightEmbeddingToBlock] using hconjRoot
  have hglobal : evenBlockLeftDerivedKernel (q + 5) 4 f =
      evenBlockFourRightKernel q f :=
    evenBlockFour_kernel_eq_of_conjugate_generators
      q f hker yL yR hL hR d hconj
  exact evenBlockFour_kernelInBlock_eq_of_global_eq
    q f hglobal


public noncomputable def evenBlockFourDerivedProductInEvenBlock
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
  (hker : f.ker ≤ Subgroup.center H) :
    Subgroup (evenBlockPreimage (q + 5) 4 f) :=
  ((alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f).comp
    (evenBlockFourDerivedMulHom q f hf hker)).range

public def evenBlockFourCommonKernelInEvenBlock
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4))) :
    Subgroup (evenBlockPreimage (q + 5) 4 f) :=
  (evenBlockLeftDerivedKernelInBlock (q + 5) 4 f).map
    (alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f)

public theorem evenBlockFourKernel_inf_productInEvenBlock_eq_of_fusion
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f) :
    f.ker.comap (evenBlockPreimage (q + 5) 4 f).subtype ⊓
        evenBlockFourDerivedProductInEvenBlock q f hf hker =
      evenBlockFourCommonKernelInEvenBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  let B := evenBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f
  let m := evenBlockFourDerivedMulHom q f hf hker
  let C := evenBlockLeftDerivedKernelInBlock (q + 5) 4 f
  have hinf : r.ker ⊓ evenBlockFourDerivedProduct q f hf hker = C :=
    evenBlockFourDerivedProduct_ker_inf_eq_of_kernel_eq
      q f hf hker hfusion
  ext z
  constructor
  · rintro ⟨hzK, hzL⟩
    obtain ⟨x, rfl⟩ := hzL
    let e : E := m x
    have heK : e ∈ r.ker := by
      rw [alternatingBlockPreimageProjection_ker_eq_comap]
      change f ((e : E) : H) = 1
      change f ((((j e) : B) : H)) = 1 at hzK
      exact hzK
    have heL : e ∈ evenBlockFourDerivedProduct q f hf hker :=
      ⟨x, rfl⟩
    have heC : e ∈ C := by
      rw [← hinf]
      exact ⟨heK, heL⟩
    exact ⟨e, heC, rfl⟩
  · rintro ⟨e, heC, rfl⟩
    have heInf : e ∈ r.ker ⊓
        evenBlockFourDerivedProduct q f hf hker := by
      rw [hinf]
      exact heC
    constructor
    · rw [alternatingBlockPreimageProjection_ker_eq_comap] at heInf
      change f ((((j e) : B) : H)) = 1
      have heK := heInf.1
      change f ((e : E) : H) = 1 at heK
      exact heK
    · obtain ⟨x, hx⟩ := heInf.2
      exact ⟨x, congrArg j hx⟩

public def evenBlockFourBlockLeftPoint (q : Nat) (i : Fin (q + 5)) :
    Fin ((q + 5) + 4) := finSumFinEquiv (Sum.inl i)

public theorem evenBlockFourBlockLeftPoint_injective (q : Nat) :
    Function.Injective (evenBlockFourBlockLeftPoint q) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

public theorem evenBlockFourRightPoint_injective (q : Nat) :
    Function.Injective (evenBlockFourRightPoint q) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg
    (fun x : Fin ((q + 5) + 4) => x.val) h
  dsimp [evenBlockFourRightPoint] at h'
  omega

public theorem evenBlockFourBlockLeftPoint_ne_right
    (q : Nat) (i : Fin (q + 5)) (j : Fin 4) :
    evenBlockFourBlockLeftPoint q i ≠
      evenBlockFourRightPoint q j := by
  intro h
  have h' := congrArg Fin.val h
  dsimp [evenBlockFourBlockLeftPoint,
    evenBlockFourRightPoint] at h'
  omega

public theorem evenBlockFour_root_p0_ne_p1 (q : Nat) :
    RootFourSubgroup.p0 q ≠ RootFourSubgroup.p1 q := by
  intro h
  have h' := congrArg Fin.val h
  simp [RootFourSubgroup.p0, RootFourSubgroup.p1] at h'

public theorem evenBlockFour_permCongr_swap
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (i j : α) :
    e.permCongr (Equiv.swap i j) = Equiv.swap (e i) (e j) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [Equiv.permCongr_apply, e.symm_apply_apply]
  exact e.injective.map_swap i j x

public theorem evenBlockFour_permProdBlockHom_swap_left
    (q : Nat) (i j : Fin (q + 5)) :
    permProdBlockHom (q + 5) 4 (Equiv.swap i j, 1) =
      Equiv.swap (evenBlockFourBlockLeftPoint q i)
        (evenBlockFourBlockLeftPoint q j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_swap_one,
    evenBlockFour_permCongr_swap]
  rfl

public theorem evenBlockFour_permProdBlockHom_swap_right
    (q : Nat) (i j : Fin 4) :
    permProdBlockHom (q + 5) 4 (1, Equiv.swap i j) =
      Equiv.swap (evenBlockFourRightPoint q i)
        (evenBlockFourRightPoint q j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_one_swap,
    evenBlockFour_permCongr_swap]
  rfl

public def evenBlockFourOddPair (q : Nat) :
    evenBlockProductGroup (q + 5) 4 :=
  ⟨(Equiv.swap (RootFourSubgroup.p0 q) (RootFourSubgroup.p1 q),
      Equiv.swap (0 : Fin 4) 1), by
    change permProdBlockHom (q + 5) 4 _ ∈
      alternatingGroup (Fin ((q + 5) + 4))
    rw [Equiv.Perm.mem_alternatingGroup, permProdBlockHom_apply,
      Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
    · norm_num
    · decide
    · exact evenBlockFour_root_p0_ne_p1 q⟩

public theorem evenBlockFourParityHom_oddPair (q : Nat) :
    evenBlockParityHom (q + 5) 4 (evenBlockFourOddPair q) = -1 := by
  change Equiv.Perm.sign
      (Equiv.swap (RootFourSubgroup.p0 q) (RootFourSubgroup.p1 q)) = -1
  exact Equiv.Perm.sign_swap (evenBlockFour_root_p0_ne_p1 q)

public def evenBlockFourParityConjugatorPerm (q : Nat) :
    Equiv.Perm (Fin ((q + 5) + 4)) :=
  Equiv.swap (evenBlockFourLeftPoint q 2)
      (evenBlockFourRightPoint q 0) *
    Equiv.swap (evenBlockFourLeftPoint q 3)
      (evenBlockFourRightPoint q 1)

public theorem sign_evenBlockFourParityConjugatorPerm (q : Nat) :
    Equiv.Perm.sign (evenBlockFourParityConjugatorPerm q) = 1 := by
  rw [evenBlockFourParityConjugatorPerm, map_mul,
    Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
  · norm_num
  · exact evenBlockFourLeftPoint_ne_right q 3 1
  · exact evenBlockFourLeftPoint_ne_right q 2 0

public def evenBlockFourParityConjugator (q : Nat) :
    alternatingGroup (Fin ((q + 5) + 4)) :=
  ⟨evenBlockFourParityConjugatorPerm q, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockFourParityConjugatorPerm]⟩

public theorem evenBlockFourParityConjugator_map_leftPoint
    (q : Nat) (i : Fin 4) :
    evenBlockFourParityConjugatorPerm q
        (evenBlockFourLeftPoint q i) =
      if i = 2 then evenBlockFourRightPoint q 0
      else if i = 3 then evenBlockFourRightPoint q 1
      else evenBlockFourLeftPoint q i := by
  fin_cases i <;>
    apply Fin.ext <;>
    simp [evenBlockFourParityConjugatorPerm,
      evenBlockFourLeftPoint,
      evenBlockFourRightPoint,
      Equiv.swap_apply_def]

public theorem evenBlockFourParityConjugator_conj_left_rho1 (q : Nat) :
    evenBlockFourParityConjugator q *
        alternatingProdBlockHom (q + 5) 4
          ((⟨RootFourSubgroup.rho1 q,
              RootFourSubgroup.rho1_mem_alternating q⟩ :
                alternatingGroup (Fin (q + 5))), 1) *
        (evenBlockFourParityConjugator q)⁻¹ =
      evenBlockProductHom (q + 5) 4
        (evenBlockFourOddPair q) := by
  apply Subtype.ext
  let s := evenBlockFourParityConjugatorPerm q
  let l0 := evenBlockFourLeftPoint q 0
  let l1 := evenBlockFourLeftPoint q 1
  let l2 := evenBlockFourLeftPoint q 2
  let l3 := evenBlockFourLeftPoint q 3
  let r0 := evenBlockFourRightPoint q 0
  let r1 := evenBlockFourRightPoint q 1
  have hleft :
      permProdBlockHom (q + 5) 4 (RootFourSubgroup.rho1 q, 1) =
        Equiv.swap l0 l1 * Equiv.swap l2 l3 := by
    rw [RootFourSubgroup.rho1]
    change permProdBlockHom (q + 5) 4
        ((Equiv.swap _ _, 1) * (Equiv.swap _ _, 1)) = _
    rw [map_mul, evenBlockFour_permProdBlockHom_swap_left,
      evenBlockFour_permProdBlockHom_swap_left]
    rfl
  have htarget :
      permProdBlockHom (q + 5) 4
          (evenBlockFourOddPair q :
            Equiv.Perm (Fin (q + 5)) × Equiv.Perm (Fin 4)) =
        Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
    change permProdBlockHom (q + 5) 4
        ((Equiv.swap _ _, 1) * (1, Equiv.swap _ _)) = _
    rw [map_mul, evenBlockFour_permProdBlockHom_swap_left,
      evenBlockFour_permProdBlockHom_swap_right]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    coe_alternatingProdBlockHom_apply, coe_evenBlockProductHom_apply]
  change s * permProdBlockHom (q + 5) 4
      (RootFourSubgroup.rho1 q, 1) * s⁻¹ =
    permProdBlockHom (q + 5) 4
      (evenBlockFourOddPair q :
        Equiv.Perm (Fin (q + 5)) × Equiv.Perm (Fin 4))
  rw [hleft, htarget]
  calc
    s * (Equiv.swap l0 l1 * Equiv.swap l2 l3) * s⁻¹ =
        (s * Equiv.swap l0 l1 * s⁻¹) *
          (s * Equiv.swap l2 l3 * s⁻¹) := by group
    _ = Equiv.swap (s l0) (s l1) *
        Equiv.swap (s l2) (s l3) := by
      rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    _ = Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
      simp [s, l0, l1, l2, l3, r0, r1,
        evenBlockFourParityConjugator_map_leftPoint]

public def evenBlockFour_permConjAltHom
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) :
    alternatingGroup α →* alternatingGroup α where
  toFun σ := ⟨c * σ * c⁻¹, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv]
    rw [show Equiv.Perm.sign (σ : Equiv.Perm α) = 1 from σ.2]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' σ τ := by
    apply Subtype.ext
    change c * ((σ : Equiv.Perm α) * (τ : Equiv.Perm α)) * c⁻¹ =
      (c * (σ : Equiv.Perm α) * c⁻¹) *
        (c * (τ : Equiv.Perm α) * c⁻¹)
    group

public def evenBlockFourRightOddPerm :
    Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

public noncomputable def evenBlockFourRootOddPerm :
    Equiv.Perm (Fin 5) :=
  evenBlockFourRightPermHom evenBlockFourRightOddPerm

public def evenBlockFourRightOddConj :
    alternatingGroup (Fin 4) →* alternatingGroup (Fin 4) :=
  evenBlockFour_permConjAltHom evenBlockFourRightOddPerm

public noncomputable def evenBlockFourRootOddConj :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) :=
  evenBlockFour_permConjAltHom evenBlockFourRootOddPerm

public theorem evenBlockFourRootOddConj_right
    (σ : alternatingGroup (Fin 4)) :
    evenBlockFourRootOddConj
        (evenBlockFourRightAltHom σ) =
      evenBlockFourRightAltHom
        (evenBlockFourRightOddConj σ) := by
  apply Subtype.ext
  simp only [evenBlockFourRootOddConj,
    evenBlockFourRightOddConj, evenBlockFour_permConjAltHom,
    evenBlockFourRightAltHom]
  change evenBlockFourRootOddPerm *
      evenBlockFourRightPermHom σ *
      evenBlockFourRootOddPerm⁻¹ =
    evenBlockFourRightPermHom
      (evenBlockFourRightOddPerm * σ *
        evenBlockFourRightOddPerm⁻¹)
  exact evenBlockFour_viaEmbedding_conj
    evenBlockFourRightEmbedding
    evenBlockFourRightEmbedding
    evenBlockFourRightOddPerm
    evenBlockFourRootOddPerm
    (fun i => by
      rw [evenBlockFourRootOddPerm,
        evenBlockFourRightPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply]) σ

public noncomputable def evenBlockFourOddPairPerm (q : Nat) :
    Equiv.Perm (Fin ((q + 5) + 4)) :=
  permProdBlockHom (q + 5) 4
    (evenBlockFourOddPair q :
      Equiv.Perm (Fin (q + 5)) × Equiv.Perm (Fin 4))

public theorem evenBlockFourOddPairPerm_map_root (q : Nat) (i : Fin 5) :
    evenBlockFourOddPairPerm q
        (evenBlockFourRootEmbedding q i) =
      evenBlockFourRootEmbedding q
        (evenBlockFourRootOddPerm i) := by
  let left4 : Fin (q + 5) := ⟨4, by omega⟩
  have hemb (j : Fin 4) :
      evenBlockFourRootEmbedding q
          (evenBlockFourRightEmbedding j) =
        finSumFinEquiv (Sum.inr j) := by
    apply Fin.ext
    change (if h : evenBlockFourRightEmbedding j = 0 then 4 else
      q + 4 + (evenBlockFourRightEmbedding j).val) = q + 5 + j.val
    split_ifs with hzero
    · exact (evenBlockFourRightEmbedding_ne_zero j hzero).elim
    · rw [evenBlockFourRightEmbedding_val]
      omega
  have hodd (j : Fin 4) :
      evenBlockFourRootOddPerm
          (evenBlockFourRightEmbedding j) =
        evenBlockFourRightEmbedding
          (evenBlockFourRightOddPerm j) := by
    rw [evenBlockFourRootOddPerm,
      evenBlockFourRightPermHom,
      Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply]
  by_cases hi : i = 0
  · subst i
    have hroot0 : evenBlockFourRootEmbedding q 0 =
        finSumFinEquiv (Sum.inl left4) := by
      apply Fin.ext
      rfl
    have h0not : (0 : Fin 5) ∉
        Set.range evenBlockFourRightEmbedding := by
      rintro ⟨j, hj⟩
      have hval := congrArg Fin.val hj
      rw [evenBlockFourRightEmbedding_val] at hval
      simp at hval
    have hodd0 : evenBlockFourRootOddPerm 0 = 0 := by
      rw [evenBlockFourRootOddPerm,
        evenBlockFourRightPermHom,
        Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ h0not]
    rw [hroot0, hodd0, hroot0]
    simp [evenBlockFourOddPairPerm,
      evenBlockFourOddPair, permProdBlockHom_apply,
      RootFourSubgroup.p0, RootFourSubgroup.p1,
      left4]
    change finSumFinEquiv
        (Sum.map (Equiv.swap 0 1) (Equiv.swap 0 1)
          (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl left4)))) =
      finSumFinEquiv (Sum.inl left4)
    rw [Equiv.symm_apply_apply]
    simp [left4, Equiv.swap_apply_def]
  · let j : Fin 4 := ⟨i - 1, by omega⟩
    have hij : i = evenBlockFourRightEmbedding j := by
      apply Fin.ext
      have hi1 : 1 ≤ i.val := by
        have hi0 : i.val ≠ 0 := by
          intro h
          apply hi
          exact Fin.ext h
        omega
      change i.val = j.val + 1
      dsimp [j]
      omega
    rw [hij, hemb j, hodd j,
      hemb (evenBlockFourRightOddPerm j)]
    simp [evenBlockFourOddPairPerm,
      evenBlockFourOddPair, permProdBlockHom_apply]
    rfl

public theorem evenBlockFourOddPair_conj_root
    (q : Nat) (σ : alternatingGroup (Fin 5)) :
    evenBlockProductHom (q + 5) 4 (evenBlockFourOddPair q) *
        evenBlockFourRootAltHom q σ *
        (evenBlockProductHom (q + 5) 4
          (evenBlockFourOddPair q))⁻¹ =
      evenBlockFourRootAltHom q
        (evenBlockFourRootOddConj σ) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    coe_evenBlockProductHom_apply,
    evenBlockFourRootAltHom,
    evenBlockFourRootOddConj, evenBlockFour_permConjAltHom]
  change evenBlockFourOddPairPerm q *
      evenBlockFourRootPermHom q σ *
      (evenBlockFourOddPairPerm q)⁻¹ =
    evenBlockFourRootPermHom q
      (evenBlockFourRootOddPerm * σ *
        evenBlockFourRootOddPerm⁻¹)
  exact evenBlockFour_viaEmbedding_conj
    (evenBlockFourRootEmbedding q)
    (evenBlockFourRootEmbedding q)
    evenBlockFourRootOddPerm
    (evenBlockFourOddPairPerm q)
    (evenBlockFourOddPairPerm_map_root q) σ

public noncomputable def evenBlockFourConjOnRootPreimage
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q) :
    evenBlockFourRootPreimage q f →*
      evenBlockFourRootPreimage q f where
  toFun x := ⟨(u : H) * (x : H) * (u : H)⁻¹, by
    change f ((u : H) * (x : H) * (u : H)⁻¹) ∈
      evenBlockFourRoot q
    refine ⟨evenBlockFourRootOddConj
      (evenBlockFourRootPreimageProjection q f x), ?_⟩
    have hfu : f u = evenBlockProductHom (q + 5) 4
        (evenBlockFourOddPair q) := by
      calc
        f u = evenBlockProductHom (q + 5) 4
            (evenBlockPreimageProjection (q + 5) 4 f u) :=
          (evenBlockPreimageProjection_fac (q + 5) 4 f u).symm
        _ = _ := by rw [hu]
    calc
      evenBlockFourRootAltHom q
          (evenBlockFourRootOddConj
            (evenBlockFourRootPreimageProjection q f x)) =
        evenBlockProductHom (q + 5) 4
            (evenBlockFourOddPair q) *
          evenBlockFourRootAltHom q
            (evenBlockFourRootPreimageProjection q f x) *
          (evenBlockProductHom (q + 5) 4
            (evenBlockFourOddPair q))⁻¹ :=
          (evenBlockFourOddPair_conj_root q _).symm
      _ = f ((u : H) * (x : H) * (u : H)⁻¹) := by
        rw [map_mul, map_mul, map_inv, hfu,
          evenBlockFourRootPreimageProjection_fac]
  ⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change (u : H) * ((x : H) * (y : H)) * (u : H)⁻¹ =
      ((u : H) * (x : H) * (u : H)⁻¹) *
        ((u : H) * (y : H) * (u : H)⁻¹)
    group

public noncomputable def evenBlockFourConjOnRootDerived
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q) :
    evenBlockFourRootPreimageDerived q f →*
      evenBlockFourRootPreimageDerived q f :=
  let φ := evenBlockFourConjOnRootPreimage q f u hu
  (φ.comp (commutator (evenBlockFourRootPreimage q f)).subtype).codRestrict
    (commutator (evenBlockFourRootPreimage q f)) (fun x => by
      have hmap : (commutator
          (evenBlockFourRootPreimage q f)).map φ ≤
          commutator (evenBlockFourRootPreimage q f) := by
        rw [map_commutator_eq]
        exact Subgroup.commutator_mono le_top le_top
      apply hmap
      exact ⟨x, x.2, rfl⟩)

public theorem evenBlockFourConjOnRootDerived_projection
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q)
    (x : evenBlockFourRootPreimageDerived q f) :
    evenBlockFourRootPreimageDerivedProjection q f
        (evenBlockFourConjOnRootDerived q f u hu x) =
      evenBlockFourRootOddConj
        (evenBlockFourRootPreimageDerivedProjection q f x) := by
  apply evenBlockFourRootAltHom_injective q
  have hfu : f u = evenBlockProductHom (q + 5) 4
      (evenBlockFourOddPair q) := by
    calc
      f u = evenBlockProductHom (q + 5) 4
          (evenBlockPreimageProjection (q + 5) 4 f u) :=
        (evenBlockPreimageProjection_fac (q + 5) 4 f u).symm
      _ = _ := by rw [hu]
  calc
    evenBlockFourRootAltHom q
        (evenBlockFourRootPreimageDerivedProjection q f
          (evenBlockFourConjOnRootDerived q f u hu x)) =
      f ((u : H) * (x : H) * (u : H)⁻¹) :=
        evenBlockFourRootPreimageDerivedProjection_fac q f _
    _ = evenBlockProductHom (q + 5) 4
          (evenBlockFourOddPair q) *
        evenBlockFourRootAltHom q
          (evenBlockFourRootPreimageDerivedProjection q f x) *
        (evenBlockProductHom (q + 5) 4
          (evenBlockFourOddPair q))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hfu,
        evenBlockFourRootPreimageDerivedProjection_fac]
    _ = evenBlockFourRootAltHom q
        (evenBlockFourRootOddConj
          (evenBlockFourRootPreimageDerivedProjection q f x)) :=
      evenBlockFourOddPair_conj_root q _

public noncomputable def evenBlockFourConjOnRightSubextension
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q) :
    evenBlockFourRightSubextension q f →*
      evenBlockFourRightSubextension q f where
  toFun x :=
    ⟨evenBlockFourConjOnRootDerived q f u hu x, by
      change evenBlockFourRootPreimageDerivedProjection q f
          (evenBlockFourConjOnRootDerived q f u hu x) ∈
        evenBlockFourRightRoot
      refine ⟨evenBlockFourRightOddConj
        (evenBlockFourRightSubextensionProjection q f x), ?_⟩
      calc
        evenBlockFourRightAltHom
            (evenBlockFourRightOddConj
              (evenBlockFourRightSubextensionProjection q f x)) =
          evenBlockFourRootOddConj
            (evenBlockFourRightAltHom
              (evenBlockFourRightSubextensionProjection q f x)) :=
            (evenBlockFourRootOddConj_right _).symm
        _ = evenBlockFourRootOddConj
            (evenBlockFourRootPreimageDerivedProjection q f x) := by
          rw [evenBlockFourRightSubextensionProjection_fac]
        _ = evenBlockFourRootPreimageDerivedProjection q f
            (evenBlockFourConjOnRootDerived q f u hu x) :=
          (evenBlockFourConjOnRootDerived_projection q f u hu x).symm⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (evenBlockFourConjOnRootDerived q f u hu)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (evenBlockFourConjOnRootDerived q f u hu)
      (x : evenBlockFourRootPreimageDerived q f)
      (y : evenBlockFourRootPreimageDerived q f)

public theorem evenBlockFourConjOnRightSubextension_embedding
    {H : Type} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q)
    (x : evenBlockFourRightSubextension q f) :
    evenBlockFourRightEmbeddingToAmbient q f
        (evenBlockFourConjOnRightSubextension q f u hu x) =
      (u : H) * evenBlockFourRightEmbeddingToAmbient q f x *
        (u : H)⁻¹ := by
  rfl

public theorem evenBlockFourDerivedProductInEvenBlock_conj_mem
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u z : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q)
    (hz : z ∈ evenBlockFourDerivedProductInEvenBlock q f hf hker) :
    u * z * u⁻¹ ∈
      evenBlockFourDerivedProductInEvenBlock q f hf hker := by
  obtain ⟨x, rfl⟩ := hz
  let cL := evenBlockConjOnLeftDerived (q + 5) 4 f u
  let cR := evenBlockFourConjOnRightSubextension q f u hu
  refine ⟨(cL x.1, cR x.2), ?_⟩
  apply Subtype.ext
  change evenBlockLeftDerivedEmbedding (q + 5) 4 f (cL x.1) *
      evenBlockFourRightEmbeddingToAmbient q f (cR x.2) =
    (u : H) *
        (evenBlockLeftDerivedEmbedding (q + 5) 4 f x.1 *
          evenBlockFourRightEmbeddingToAmbient q f x.2) *
      (u : H)⁻¹
  rw [evenBlockConjOnLeftDerived_embedding_general,
    evenBlockFourConjOnRightSubextension_embedding]
  group

public theorem evenBlockFourOddPair_inv (q : Nat) :
    (evenBlockFourOddPair q)⁻¹ =
      evenBlockFourOddPair q := by
  apply Subtype.ext
  apply Prod.ext
  · simp [evenBlockFourOddPair]
  · simp [evenBlockFourOddPair]

public theorem evenBlockFourDerivedProductInEvenBlock_zpowers_le_normalizer
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u : evenBlockPreimage (q + 5) 4 f)
    (hu : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q) :
    Subgroup.zpowers u ≤ Subgroup.normalizer
      (evenBlockFourDerivedProductInEvenBlock q f hf hker) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
  intro z
  constructor
  · exact evenBlockFourDerivedProductInEvenBlock_conj_mem
      q f hf hker u z hu
  · intro hz
    have huInv : evenBlockPreimageProjection (q + 5) 4 f u⁻¹ =
        evenBlockFourOddPair q := by
      rw [map_inv, hu, evenBlockFourOddPair_inv]
    have h := evenBlockFourDerivedProductInEvenBlock_conj_mem
      q f hf hker u⁻¹ (u * z * u⁻¹) huInv hz
    have heq : u⁻¹ * (u * z * u⁻¹) * u = z := by group
    rw [inv_inv, heq] at h
    exact h


public theorem evenBlockFourKernel_inf_parityCosetProduct_eq_of_square_mem
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f)
    (u : evenBlockPreimage (q + 5) 4 f)
    (huProjection : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q)
    (huParity : evenBlockPreimageParity (q + 5) 4 f u = -1)
    (hu2C : u ^ 2 ∈ evenBlockFourCommonKernelInEvenBlock q f) :
    f.ker.comap (evenBlockPreimage (q + 5) 4 f).subtype ⊓
        (Subgroup.zpowers u ⊔
          evenBlockFourDerivedProductInEvenBlock q f hf hker) =
      evenBlockFourCommonKernelInEvenBlock q f := by
  let B := evenBlockPreimage (q + 5) 4 f
  let parity := evenBlockPreimageParity (q + 5) 4 f
  let K := f.ker.comap B.subtype
  let L := evenBlockFourDerivedProductInEvenBlock q f hf hker
  let C := evenBlockFourCommonKernelInEvenBlock q f
  have hKparity : K ≤ parity.ker := by
    intro x hx
    have hxProjection : x ∈
        (evenBlockPreimageProjection (q + 5) 4 f).ker := by
      rw [evenBlockPreimageProjection_ker_eq_comap]
      exact hx
    rw [MonoidHom.mem_ker]
    change evenBlockParityHom (q + 5) 4
        (evenBlockPreimageProjection (q + 5) 4 f x) = 1
    rw [MonoidHom.mem_ker.mp hxProjection, map_one]
  have hLparity : L ≤ parity.ker := by
    rintro z ⟨x, rfl⟩
    rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
    exact (evenBlockFourDerivedMulHom q f hf hker x).2
  exact kernel_inf_sup_zpowers_eq_of_parity_of_square_mem
    parity K L C u hKparity hLparity huParity
    (evenBlockFourKernel_inf_productInEvenBlock_eq_of_fusion
      q f hf hker hfusion)
    hu2C
    (evenBlockFourDerivedProductInEvenBlock_zpowers_le_normalizer
      q f hf hker u huProjection)

public theorem exists_evenBlockOddLiftFour_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    ∃ u : evenBlockPreimage (q + 5) 4 f,
      evenBlockPreimageProjection (q + 5) 4 f u =
          evenBlockFourOddPair q ∧
        evenBlockPreimageParity (q + 5) 4 f u = -1 ∧
          u ^ 2 ∈ evenBlockFourCommonKernelInEvenBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let EL := prodLeftPreimage r
  let rL0 := prodLeftPreimageProjection r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let iL := evenBlockLeftDerivedEmbedding (q + 5) 4 f
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 4 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 4 f hker
  obtain ⟨_, yL, hyL, hL⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rL0 (prodLeftPreimageProjection_surjective r hr)
        (prodLeftPreimageProjection_ker_le_center r hrker)
  obtain ⟨d, hd⟩ := hf (evenBlockFourParityConjugator q)
  have hryL : r
      ((((yL : DL) : EL) : E)) =
      ((⟨RootFourSubgroup.rho1 q,
          RootFourSubgroup.rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))), 1) := by
    apply Prod.ext
    · exact hyL
    · exact Subgroup.mem_bot.mp yL.1.2.2
  have hfyL : f (iL yL) =
      alternatingProdBlockHom (q + 5) 4
        ((⟨RootFourSubgroup.rho1 q,
            RootFourSubgroup.rho1_mem_alternating q⟩ :
          alternatingGroup (Fin (q + 5))), 1) := by
    change f (((((yL : DL) : EL) : E) : H)) = _
    rw [← alternatingBlockPreimageProjection_fac]
    exact congrArg (alternatingProdBlockHom (q + 5) 4) hryL
  have huImage : f (d * iL yL * d⁻¹) =
      evenBlockProductHom (q + 5) 4
        (evenBlockFourOddPair q) := by
    rw [map_mul, map_mul, map_inv, hd, hfyL]
    exact evenBlockFourParityConjugator_conj_left_rho1 q
  have huMem : d * iL yL * d⁻¹ ∈ evenBlockPreimage (q + 5) 4 f :=
    ⟨evenBlockFourOddPair q, huImage.symm⟩
  let u : evenBlockPreimage (q + 5) 4 f :=
    ⟨d * iL yL * d⁻¹, huMem⟩
  have huProjection : evenBlockPreimageProjection (q + 5) 4 f u =
      evenBlockFourOddPair q := by
    apply evenBlockProductHom_injective
    calc
      evenBlockProductHom (q + 5) 4
          (evenBlockPreimageProjection (q + 5) 4 f u) = f u :=
        evenBlockPreimageProjection_fac (q + 5) 4 f u
      _ = evenBlockProductHom (q + 5) 4
          (evenBlockFourOddPair q) := huImage
  have huParity : evenBlockPreimageParity (q + 5) 4 f u = -1 := by
    change evenBlockParityHom (q + 5) 4
        (evenBlockPreimageProjection (q + 5) 4 f u) = -1
    rw [huProjection]
    exact evenBlockFourParityHom_oddPair q
  have hyL2ker : yL ^ 2 ∈ (rL0.comp DL.subtype).ker := by
    rw [hL]
    exact Subgroup.mem_zpowers (yL ^ 2)
  let e : E := iLB (yL ^ 2)
  have heLeft : e ∈ evenBlockLeftDerivedKernelInBlock (q + 5) 4 f :=
    ⟨yL ^ 2, hyL2ker, rfl⟩
  have heC : j e ∈ evenBlockFourCommonKernelInEvenBlock q f :=
    ⟨e, heLeft, rfl⟩
  have hyL2global : iL (yL ^ 2) ∈ f.ker :=
    evenBlockLeftDerivedKernel_le_ker (q + 5) 4 f
      ⟨yL ^ 2, hyL2ker, rfl⟩
  have hyL2center : iL (yL ^ 2) ∈ Subgroup.center H :=
    hker hyL2global
  have hfixed : d * iL (yL ^ 2) * d⁻¹ = iL (yL ^ 2) := by
    have hc := Subgroup.mem_center_iff.mp hyL2center d
    rw [hc]
    simp
  have huSquare : u ^ 2 = j e := by
    apply Subtype.ext
    change (d * iL yL * d⁻¹) ^ 2 = iL (yL ^ 2)
    calc
      (d * iL yL * d⁻¹) ^ 2 = d * (iL yL) ^ 2 * d⁻¹ := by
        simp only [pow_two]
        group
      _ = d * iL (yL ^ 2) * d⁻¹ := by rw [map_pow]
      _ = iL (yL ^ 2) := hfixed
  refine ⟨u, huProjection, huParity, ?_⟩
  rw [huSquare]
  exact heC

public theorem evenBlockFourParityCosetProduct_decomposition
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u : evenBlockPreimage (q + 5) 4 f)
    (huParity : evenBlockPreimageParity (q + 5) 4 f u = -1) :
    ∀ x : evenBlockPreimage (q + 5) 4 f,
      ∃ k : f.ker.comap
          (evenBlockPreimage (q + 5) 4 f).subtype,
        ∃ d : ↥(Subgroup.zpowers u ⊔
            evenBlockFourDerivedProductInEvenBlock q f hf hker),
          (k : evenBlockPreimage (q + 5) 4 f) *
              (d : evenBlockPreimage (q + 5) 4 f) = x := by
  let B := evenBlockPreimage (q + 5) 4 f
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f
  let parity := evenBlockPreimageParity (q + 5) 4 f
  let L := evenBlockFourDerivedProductInEvenBlock q f hf hker
  let D := Subgroup.zpowers u ⊔ L
  have decomposeEven (x : B) (hx : parity x = 1) :
      ∃ k : f.ker.comap B.subtype, ∃ d : D,
        (k : B) * (d : B) = x := by
    have hxParityKer : x ∈ parity.ker := MonoidHom.mem_ker.mpr hx
    have hxE : (x : H) ∈ E := by
      rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
        at hxParityKer
      exact hxParityKer
    let e : E := ⟨(x : H), hxE⟩
    obtain ⟨k0, d0, hkd⟩ :=
      evenBlockFourDerivedProduct_decomposition q f hf hker e
    have hkGlobal : ((k0 : r.ker) : E) ∈
        f.ker.comap E.subtype := by
      rw [← alternatingBlockPreimageProjection_ker_eq_comap]
      exact k0.2
    have hkB : j (k0 : E) ∈ f.ker.comap B.subtype := hkGlobal
    have hdL : j (d0 : E) ∈ L := by
      obtain ⟨z, hz⟩ := d0.2
      refine ⟨z, ?_⟩
      change j (evenBlockFourDerivedMulHom q f hf hker z) =
        j (d0 : E)
      exact congrArg j hz
    have hdD : j (d0 : E) ∈ D := Subgroup.mem_sup_right hdL
    refine ⟨⟨j (k0 : E), hkB⟩, ⟨j (d0 : E), hdD⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : E => (z : H)) hkd
  intro x
  rcases Int.units_eq_one_or (parity x) with hx | hx
  · exact decomposeEven x hx
  · let y : B := x * u⁻¹
    have huParity' : parity u = -1 := huParity
    have hyParity : parity y = 1 := by
      change parity (x * u⁻¹) = 1
      rw [map_mul, map_inv, hx, huParity']
      norm_num
    obtain ⟨k, d0, hkd⟩ := decomposeEven y hyParity
    have huD : u ∈ D :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    let d : D := ⟨(d0 : B) * u, D.mul_mem d0.2 huD⟩
    refine ⟨k, d, ?_⟩
    change (k : B) * ((d0 : B) * u) = x
    calc
      (k : B) * ((d0 : B) * u) = ((k : B) * (d0 : B)) * u := by
        simp only [mul_assoc]
      _ = y * u := by rw [hkd]
      _ = x := by simp [y]

public theorem evenBlockKernel_comap_eq_leftDerivedKernel_of_four_block
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenBlockPreimage (q + 5) 4 f) :
    f.ker.comap (evenBlockPreimage (q + 5) 4 f).subtype =
      evenBlockFourCommonKernelInEvenBlock q f := by
  let B := evenBlockPreimage (q + 5) 4 f
  let L := evenBlockFourDerivedProductInEvenBlock q f hf hker
  let C := evenBlockFourCommonKernelInEvenBlock q f
  have hfusion : evenBlockLeftDerivedKernelInBlock (q + 5) 4 f =
      evenBlockFourRightKernelInBlock q f :=
    evenBlockFour_kernelInBlock_eq_of_multiplier_le_two
      q hM f hf hker
  obtain ⟨u, huProjection, huParity, hu2C⟩ :=
    exists_evenBlockOddLiftFour_of_multiplier_le_two
      q hM f hf hker
  let D := Subgroup.zpowers u ⊔ L
  exact kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
    (p := 2) f hker hkerTwo P B hP D C
    (evenBlockFourParityCosetProduct_decomposition
      q f hf hker u huParity)
    (evenBlockFourKernel_inf_parityCosetProduct_eq_of_square_mem
      q f hf hker hfusion u huProjection huParity hu2C)

public theorem natCard_ker_le_two_of_sylow_le_evenBlockPreimage_four
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 4)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenBlockPreimage (q + 5) 4 f) :
    Nat.card f.ker ≤ 2 := by
  let B := evenBlockPreimage (q + 5) 4 f
  let E := alternatingBlockPreimage (q + 5) 4 f
  let r := alternatingBlockPreimageProjection (q + 5) 4 f
  let rL0 := prodLeftPreimageProjection r
  let rL := prodLeftPreimageDerivedProjection r
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 4 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 4 f
  let K := f.ker.comap B.subtype
  let C := evenBlockFourCommonKernelInEvenBlock q f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 4 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 4 f hker
  obtain ⟨hlocal, _, _, _⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rL0 (prodLeftPreimageProjection_surjective r hr)
        (prodLeftPreimageProjection_ker_le_center r hrker)
  have hlocal' : Nat.card rL.ker ≤ 2 := hlocal
  let eK : f.ker ≃* K :=
    { toFun := fun z => ⟨⟨z, by
          change f z ∈ (evenBlockProductHom (q + 5) 4).range
          rw [MonoidHom.mem_ker.mp z.2]
          exact Subgroup.one_mem _⟩, z.2⟩
      invFun := fun z => ⟨((z : K) : B), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hKC : K = C :=
    evenBlockKernel_comap_eq_leftDerivedKernel_of_four_block
      q hM f hf hker hkerTwo P hP
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B => (z : H)) hxy
  have hiLB : Function.Injective iLB := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  calc
    Nat.card f.ker = Nat.card K := Nat.card_congr eK.toEquiv
    _ = Nat.card C := by rw [hKC]
    _ = Nat.card (evenBlockLeftDerivedKernelInBlock (q + 5) 4 f) := by
      exact Subgroup.card_map_of_injective hj
    _ = Nat.card rL.ker := by
      exact Subgroup.card_map_of_injective hiLB
    _ ≤ 2 := hlocal'

/-- Transport a left derived-kernel bound back to the global central kernel
once the restricted kernel has been identified with that left kernel. -/
public theorem natCard_ker_le_two_of_kernel_comap_eq_leftDerivedKernel
    {H : Type} [Group H] [Finite H]
    (q b : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + b)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hKC : f.ker.comap (evenBlockPreimage (q + 5) b f).subtype =
      (evenBlockLeftDerivedKernelInBlock (q + 5) b f).map
        (alternatingBlockPreimageToEvenBlockPreimage (q + 5) b f)) :
    Nat.card f.ker ≤ 2 := by
  let B := evenBlockPreimage (q + 5) b f
  let E := alternatingBlockPreimage (q + 5) b f
  let r := alternatingBlockPreimageProjection (q + 5) b f
  let rL0 := prodLeftPreimageProjection r
  let rL := prodLeftPreimageDerivedProjection r
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (q + 5) b f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) b f
  let K := f.ker.comap B.subtype
  let C := (evenBlockLeftDerivedKernelInBlock (q + 5) b f).map j
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) b f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) b f hker
  obtain ⟨hlocal, _, _, _⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rL0 (prodLeftPreimageProjection_surjective r hr)
        (prodLeftPreimageProjection_ker_le_center r hrker)
  have hlocal' : Nat.card rL.ker ≤ 2 := hlocal
  let eK : f.ker ≃* K :=
    { toFun := fun z => ⟨⟨z, by
          change f z ∈ (evenBlockProductHom (q + 5) b).range
          rw [MonoidHom.mem_ker.mp z.2]
          exact Subgroup.one_mem _⟩, z.2⟩
      invFun := fun z => ⟨((z : K) : B), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hKC' : K = C := hKC
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B => (z : H)) hxy
  have hiLB : Function.Injective iLB := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  calc
    Nat.card f.ker = Nat.card K := Nat.card_congr eK.toEquiv
    _ = Nat.card C := by rw [hKC']
    _ = Nat.card (evenBlockLeftDerivedKernelInBlock (q + 5) b f) := by
      exact Subgroup.card_map_of_injective hj
    _ = Nat.card rL.ker := by
      exact Subgroup.card_map_of_injective hiLB
    _ ≤ 2 := hlocal'

/-- Cardinality form of the equal even-block endpoint. -/
public theorem natCard_ker_le_two_of_sylow_le_evenBlockPreimage_equal_blocks
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (ha : Even (q + 5))
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenBlockPreimage (q + 5) (q + 5) f) :
    Nat.card f.ker ≤ 2 := by
  apply natCard_ker_le_two_of_kernel_comap_eq_leftDerivedKernel
    q (q + 5) hM f hf hker
  exact evenBlockKernel_comap_eq_commonDerivedKernel_of_equal_blocks
    q hM ha f hf hker hkerTwo P hP

/-- Cardinality form of the unequal large even-block endpoint. -/
public theorem natCard_ker_le_two_of_sylow_le_evenBlockPreimage_unequal_blocks
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (qA qB : Nat)
    (hMA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (hMB : Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker ≤ 2)
    (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenBlockPreimage (qA + 5) (qB + 5) f) :
    Nat.card f.ker ≤ 2 := by
  apply natCard_ker_le_two_of_kernel_comap_eq_leftDerivedKernel
    qA (qB + 5) hMA f hf hker
  exact evenBlockKernel_comap_eq_commonDerivedKernel_of_unequal_blocks
    qA qB hMA hMB hA hB f hf hker hkerTwo P hP

/-- Relabel a subset and its complement as the two standard consecutive blocks. -/
public noncomputable def relabelingEquivOfSubsetTotal
    (m a b : Nat) (S : Set (Fin m))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = b) :
    Fin (a + b) ≃ Fin m := by
  classical
  let eS : Fin a ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin b ≃ (Sᶜ : Set (Fin m)) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  exact finSumFinEquiv.symm.trans
    ((eS.sumCongr eSc).trans (Equiv.Set.sumCompl S))

/-- The relabelling equivalence sends the standard first block onto the given subset. -/
public theorem relabelingEquivOfSubsetTotal_image_firstBlock
    (m a b : Nat) (S : Set (Fin m))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = b) :
    relabelingEquivOfSubsetTotal m a b S hS hSc ''
        finFirstBlock a b = S := by
  classical
  let eS : Fin a ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin b ≃ (Sᶜ : Set (Fin m)) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    simp [relabelingEquivOfSubsetTotal]
  · intro hx
    obtain ⟨i, hi⟩ := eS.surjective ⟨x, hx⟩
    refine ⟨Fin.castAdd b i, ⟨i, rfl⟩, ?_⟩
    simpa [relabelingEquivOfSubsetTotal, eS, eSc] using
      congrArg Subtype.val hi

/-- After relabelling an invariant subset, a Sylow subgroup lies in the standard
two-block preimage, without changing the kernel of the alternating extension. -/
public theorem exists_relabelled_evenBlock_extension_of_sylow_mapsTo_subset
    {H : Type} [Group H] [Finite H]
    (m a b : Nat)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (P : Sylow 2 H)
    (S : Set (Fin m))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = b)
    (hmaps : ∀ x : P,
      Set.MapsTo (f (x : H) : Fin m → Fin m) S S) :
    ∃ f' : H →* alternatingGroup (Fin (a + b)),
      f'.ker = f.ker ∧ Function.Surjective f' ∧
        (P : Subgroup H) ≤ evenBlockPreimage a b f' := by
  let e := relabelingEquivOfSubsetTotal m a b S hS hSc
  let f' : H →* alternatingGroup (Fin (a + b)) :=
    e.symm.altCongrHom.toMonoidHom.comp f
  have hfker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f e.symm.altCongrHom.toMonoidHom
      e.symm.altCongrHom.injective
  have hf' : Function.Surjective f' :=
    e.symm.altCongrHom.surjective.comp hf
  refine ⟨f', hfker, hf', ?_⟩
  intro x hx
  let xp : P := ⟨x, hx⟩
  have hblock : ((f' x : alternatingGroup (Fin (a + b))) :
      Equiv.Perm (Fin (a + b))) ∈ (permProdBlockHom a b).range := by
    apply perm_mem_permProdBlockHom_range_of_mapsTo_finFirstBlock
    intro y hy
    have hey : e y ∈ S := by
      rw [← relabelingEquivOfSubsetTotal_image_firstBlock
        m a b S hS hSc]
      exact ⟨y, hy, rfl⟩
    have hz := hmaps xp hey
    rw [← relabelingEquivOfSubsetTotal_image_firstBlock
      m a b S hS hSc] at hz
    obtain ⟨z, hz, hzEq⟩ := hz
    change e.symm ((f (x : H) : Equiv.Perm (Fin m)) (e y)) ∈
      finFirstBlock a b
    rw [← hzEq, e.symm_apply_apply]
    exact hz
  obtain ⟨g, hg⟩ := hblock
  let gEven : evenBlockProductGroup a b := ⟨g, by
    change permProdBlockHom a b g ∈ alternatingGroup (Fin (a + b))
    rw [hg]
    exact (f' x).2⟩
  exact ⟨gEven, by
    apply Subtype.ext
    exact hg⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.EvenBlock -/

/- BEGIN Theory.InvolutionFixedPointFullExtension -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionFixedPointFullExtension_u

/-- Adjoining the coupled odd involution to the even fixed-point factor
recovers the full symmetric group on the fixed points. -/
public theorem involutionFixedPointFullExtension
    {Ω : Type __ch5_InvolutionFixedPointFullExtension_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (r0 : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr0 : r0 ∈ cycleRotationSubgroup x)
    (hr0χ : Equiv.Perm.sign r0.1 = -1) (hr02 : r0 ^ 2 = 1)
    (σ0 : Equiv.Perm (Function.fixedPoints x))
    (hσ0χ : Equiv.Perm.sign σ0 = -1) (hσ02 : σ0 ^ 2 = 1) :
    let Z := (Equiv.Perm.sign.comp
      (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker
    let IZ := (fixedPointPermutationSubgroup x).comap Z.subtype
    let f := involutionFixedPointParityLift x r0 hr0 hr0χ hr02
    Nonempty (↥(IZ ⊔ Subgroup.zpowers (f σ0)) ≃*
      Equiv.Perm (Function.fixedPoints x)) := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let IZ := (fixedPointPermutationSubgroup x).comap Z.subtype
  let f := involutionFixedPointParityLift x r0 hr0 hr0χ hr02
  have hf_even (σ : Equiv.Perm (Function.fixedPoints x))
      (hσ : Equiv.Perm.sign σ = 1) : f σ ∈ IZ := by
    change (f σ).1 ∈ fixedPointPermutationSubgroup x
    rw [involutionFixedPointParityLift_coe]
    rw [hσ, unitsInvolutionHom_one, mul_one]
    exact ⟨σ, rfl⟩
  have hrange : f.range = IZ ⊔ Subgroup.zpowers (f σ0) := by
    apply le_antisymm
    · rintro z ⟨σ, rfl⟩
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · exact (le_sup_left : IZ ≤ IZ ⊔ Subgroup.zpowers (f σ0))
          (hf_even σ hσ)
      · let q := σ * σ0
        have hqχ : Equiv.Perm.sign q = 1 := by
          dsimp [q]
          rw [map_mul, hσ, hσ0χ]
          norm_num
        have hqmem := hf_even q hqχ
        have hqσ0 : q * σ0 = σ := by
          dsimp [q]
          rw [mul_assoc, ← pow_two, hσ02, mul_one]
        rw [← hqσ0, map_mul]
        exact (IZ ⊔ Subgroup.zpowers (f σ0)).mul_mem
          ((le_sup_left : IZ ≤ IZ ⊔ Subgroup.zpowers (f σ0)) hqmem)
          ((le_sup_right : Subgroup.zpowers (f σ0) ≤
            IZ ⊔ Subgroup.zpowers (f σ0)) (Subgroup.mem_zpowers (f σ0)))
    · apply sup_le
      · intro z hz
        let i : fixedPointPermutationSubgroup x := ⟨z.1, hz⟩
        let σ := theorem_5_2_2_d_4 x i
        have hσχ : Equiv.Perm.sign σ = 1 := by
          dsimp [σ]
          rw [← fixedPointPermutation_sign x i]
          exact MonoidHom.mem_ker.mp z.2
        refine ⟨σ, ?_⟩
        apply Subtype.ext
        rw [involutionFixedPointParityLift_coe]
        change fixedPointPermToCentralizer x σ *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ) = z
        rw [hσχ, unitsInvolutionHom_one, mul_one]
        apply Subtype.ext
        change (fixedPointPermToCentralizer x σ).1 = z.1
        let e := theorem_5_2_2_d_4 x
        have heq : (fixedPointPermMulEquivSubgroup x) σ = i := by
          exact e.symm_apply_apply i
        calc
          (fixedPointPermToCentralizer x σ).1 =
              ((fixedPointPermMulEquivSubgroup x) σ).1 := by
                have hcoe :
                    ((fixedPointPermMulEquivSubgroup x) σ :
                      Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))) =
                      fixedPointPermToCentralizer x σ :=
                  MonoidHom.ofInjective_apply
                    (fixedPointPermToCentralizer_injective x)
                exact (congrArg Subtype.val hcoe).symm
          _ = i.1 := congrArg (fun q : fixedPointPermutationSubgroup x => q.1.1) heq
          _ = z.1 := rfl
      · rw [Subgroup.zpowers_le]
        exact ⟨σ0, rfl⟩
  let eRange : Equiv.Perm (Function.fixedPoints x) ≃* f.range :=
    MonoidHom.ofInjective (involutionFixedPointParityLift_injective
      x r0 hr0 hr0χ hr02)
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans eRange.symm⟩

end GLS3.Chapter5
/- END Theory.InvolutionFixedPointFullExtension -/

/- BEGIN Theory.SignKernelParityFullExtension -/
noncomputable section

namespace GLS3.Chapter5

/-- The parity-corrected copy of `H` is generated by its even part and one
coupled odd involution. -/
public theorem signKernelParityFullExtension
    {C : Type*} [Group C] (χ : C →* ℤˣ) (H I : Subgroup C)
    (r0 i0 : C) (hr0 : r0 ∈ H) (hi0 : i0 ∈ I)
    (hr0χ : χ r0 = -1) (hi0χ : χ i0 = -1)
    (hr02 : r0 ^ 2 = 1) (hi02 : i0 ^ 2 = 1)
    (hcomm : I ≤ Subgroup.centralizer (H : Set C))
    (hdisj : I ⊓ H = ⊥) :
    let Z := χ.ker
    let HZ := H.comap Z.subtype
    let f := signKernelParityLift χ H I i0 hi0 hi0χ hi02 hcomm
    Nonempty (↥(HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩)) ≃* H) := by
  dsimp only
  let Z := χ.ker
  let HZ := H.comap Z.subtype
  let f := signKernelParityLift χ H I i0 hi0 hi0χ hi02 hcomm
  have hf_even (h : H) (hh : χ h.1 = 1) : f h ∈ HZ := by
    change (f h).1 ∈ H
    rw [signKernelParityLift_coe, hh, unitsInvolutionHom_one, mul_one]
    exact h.2
  have hrange : f.range = HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩) := by
    apply le_antisymm
    · rintro z ⟨h, rfl⟩
      rcases Int.units_eq_one_or (χ h.1) with hh | hh
      · exact (le_sup_left : HZ ≤ HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩))
          (hf_even h hh)
      · let q : H := h * ⟨r0, hr0⟩
        have hqχ : χ q.1 = 1 := by
          dsimp [q]
          rw [map_mul, hh, hr0χ]
          norm_num
        have hqmem := hf_even q hqχ
        have hqr0 : q * ⟨r0, hr0⟩ = h := by
          apply Subtype.ext
          dsimp [q]
          rw [mul_assoc, ← pow_two, hr02, mul_one]
        rw [← hqr0, map_mul]
        exact (HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩)).mul_mem
          ((le_sup_left : HZ ≤ HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩)) hqmem)
          ((le_sup_right : Subgroup.zpowers (f ⟨r0, hr0⟩) ≤
            HZ ⊔ Subgroup.zpowers (f ⟨r0, hr0⟩))
              (Subgroup.mem_zpowers (f ⟨r0, hr0⟩)))
    · apply sup_le
      · intro z hz
        let h : H := ⟨z.1, hz⟩
        have hh : χ h.1 = 1 := MonoidHom.mem_ker.mp z.2
        refine ⟨h, ?_⟩
        apply Subtype.ext
        rw [signKernelParityLift_coe, hh, unitsInvolutionHom_one, mul_one]
      · rw [Subgroup.zpowers_le]
        exact ⟨⟨r0, hr0⟩, rfl⟩
  let eRange : H ≃* f.range := MonoidHom.ofInjective
    (signKernelParityLift_injective χ H I i0 hi0 hi0χ hi02 hcomm hdisj)
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans eRange.symm⟩

end GLS3.Chapter5
/- END Theory.SignKernelParityFullExtension -/

