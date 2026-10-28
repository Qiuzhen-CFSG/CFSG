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

public import Theory.Alternating.proposition_5_2_7_8
set_option linter.style.nameCheck false
-- Retain the legacy instance bindings and public nested namespace names.
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.dupNamespace false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option Elab.async false

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.PRank -/
noncomputable section

/-- Binary coordinates for a finite `ZMod 2`-module of power-of-two cardinality. -/
public theorem exists_linearEquiv_fin_of_card_eq_pow
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (d : Nat) (hcard : Nat.card V = 2 ^ d) :
    Nonempty (V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) := by
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at hc
  have hfin : Module.finrank (ZMod 2) V = d := by
    exact (Nat.pow_right_injective (by omega : 1 < 2)) hc.symm
  let b := Module.Free.chooseBasis (ZMod 2) V
  let e : Fin d ≃ Module.Free.ChooseBasisIndex (ZMod 2) V :=
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, hfin])).symm
  exact ⟨b.equivFun |>.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e)⟩

/-- Coordinates for a finite `ZMod p`-module of cardinality `p^d`. -/
public theorem exists_linearEquiv_fin_of_card_eq_prime_pow
    (p : Nat) (hp : p.Prime)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
    (d : Nat) (hcard : Nat.card V = p ^ d) :
    Nonempty (V ≃ₗ[ZMod p] (Fin d → ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at hc
  have hfin : Module.finrank (ZMod p) V = d := by
    exact (Nat.pow_right_injective hp.one_lt) hc.symm
  let b := Module.Free.chooseBasis (ZMod p) V
  let e : Fin d ≃ Module.Free.ChooseBasisIndex (ZMod p) V :=
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, hfin])).symm
  exact ⟨b.equivFun |>.trans (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) e)⟩

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5.PRank

public theorem exponent_le_three_mul_two_pow_sub_three
    (e : Nat) (he : 3 ≤ e) : e ≤ 3 * 2 ^ (e - 3) := by
  induction e with
  | zero => omega
  | succ e ih =>
      by_cases heq : e = 2
      · subst e
        norm_num
      · have he3 : 3 ≤ e := by omega
        have hi := ih he3
        rw [show e + 1 - 3 = (e - 3) + 1 by omega, pow_succ]
        nlinarith [show 1 ≤ e by omega]

public lemma rank_lt_size_div_p {p r : Nat} (hp : 2 < p) (hr : 2 ≤ r) :
    r < p ^ r / p := by
  have hpow : r < p ^ (r - 1) := by
    induction r with
    | zero => omega
    | succ r ih =>
        cases r with
        | zero => omega
        | succ r =>
            cases r with
            | zero => simpa using hp
            | succ r =>
                have ih' : r + 2 < p ^ (r + 1) := ih (by omega)
                have hpos : 0 < p ^ (r + 1) := pow_pos (by omega) _
                rw [show r + 3 - 1 = r + 2 by omega, pow_succ]
                nlinarith
  have hsize : p ^ r / p = p ^ (r - 1) := by
    have hsplit : p ^ r = p ^ (r - 1) * p := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ r), pow_succ]
      simp [Nat.sub_add_cancel (by omega : 1 ≤ r)]
    rw [hsplit, Nat.mul_div_left _ (by omega : 0 < p)]
  rwa [hsize]

/-- An elementary abelian subgroup: abelian, all elements have order `p` or `1`. -/
@[expose] public def IsElementaryAbelian (G : Type*) [Group G] (p : Nat) : Prop :=
  IsMulCommutative G ∧ ∀ g : G, orderOf g = 1 ∨ orderOf g = p

public lemma isElementaryAbelian_map_of_injective
    {G G' : Type*} [Group G] [Group G']
    (p : Nat) (A : Subgroup G) (hA : IsElementaryAbelian A p)
    (f : G →* G') (hf : Function.Injective f) :
    IsElementaryAbelian (A.map f) p := by
  constructor
  · rw [isMulCommutative_iff]
    intro a b
    obtain ⟨a0, ha0, ha⟩ := a.2
    obtain ⟨b0, hb0, hb⟩ := b.2
    apply Subtype.ext
    change (a : G') * (b : G') = (b : G') * (a : G')
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val
      (isMulCommutative_iff.mp hA.1 ⟨a0, ha0⟩ ⟨b0, hb0⟩))
  · intro a
    obtain ⟨a0, ha0, ha⟩ := a.2
    have horder : orderOf a = orderOf (⟨a0, ha0⟩ : A) := by
      calc
        orderOf a = orderOf (a : G') := (Subgroup.orderOf_coe a).symm
        _ = orderOf (f a0) := by rw [ha]
        _ = orderOf a0 := orderOf_injective f hf a0
        _ = orderOf (⟨a0, ha0⟩ : A) :=
          (Subgroup.orderOf_mk a0 ha0).symm
    rw [horder]
    exact hA.2 ⟨a0, ha0⟩

/-- An elementary abelian `p`-subgroup is a `p`-group. -/
public lemma ea_is_pGroup {p : Nat} {G : Type*} [Group G]
    (hp : p.Prime) (hA : IsElementaryAbelian G p) : IsPGroup p G := by
  intro g
  rcases hA.2 g with h1 | hp_
  · refine ⟨0, ?_⟩
    rw [pow_zero, pow_one]
    exact (orderOf_eq_one_iff.mp h1)
  · refine ⟨1, ?_⟩
    rw [pow_one, ← hp_]
    exact pow_orderOf_eq_one g

/-- In an abelian group acting on a set, the stabilizer of a point fixes its
whole orbit. -/
public lemma stabilizer_fixes_orbit {A α : Type*} [Group A] [MulAction A α]
    (hA : ∀ a b : A, a * b = b * a) {x : α} {a : A}
    (hax : a • x = x) : ∀ y : α, y ∈ MulAction.orbit A x → a • y = y := by
  intro y hy
  rcases hy with ⟨g, rfl⟩
  calc
    a • (g • x) = (a * g) • x := by rw [← mul_smul]
    _ = (g * a) • x := by rw [hA a g]
    _ = g • (a • x) := by rw [mul_smul]
    _ = g • x := by rw [hax]

/-- The rank contribution of an orbit of size `p^r` is `r ≤ size / p`. -/
public lemma rank_le_size_div_p {p : Nat} (hp : 1 < p) {r : Nat} (hr : 1 ≤ r) :
    r ≤ p ^ r / p := by
  have hpow : r ≤ p ^ (r - 1) := by
    induction r with
    | zero => omega
    | succ r ih =>
        cases r with
        | zero => simp
        | succ r =>
            have ih' : r + 1 ≤ p ^ r := ih (by omega)
            calc
              r + 2 ≤ p ^ r + 1 := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  (add_le_add_right ih' 1)
              _ ≤ p ^ (r + 1) := by
                rw [pow_succ]
                have hp1 : 1 ≤ p ^ r := by
                  have hpos : 0 < p ^ r := pow_pos (by omega : 0 < p) r
                  omega
                nlinarith
  have hsize : p ^ r / p = p ^ (r - 1) := by
    have hsplit : p ^ r = p ^ (r - 1) * p := by
      rw [← Nat.sub_add_cancel hr, pow_succ]
      simp [Nat.sub_add_cancel hr]
    rw [hsplit, Nat.mul_div_left _ (by omega : 0 < p)]
  rw [hsize]
  exact hpow

/-- The point set is the disjoint union of the orbits of a finite action. -/
public theorem sum_card_orbitRel_quotient
    {G α : Type*} [Group G] [MulAction G α] [Fintype α]
    [Fintype (MulAction.orbitRel.Quotient G α)] :
    (∑ q : MulAction.orbitRel.Quotient G α, Nat.card q.orbit) =
      Fintype.card α := by
  classical
  let Q := MulAction.orbitRel.Quotient G α
  have : ∀ q : Q, Fintype q.orbit := fun q => Fintype.ofFinite _
  let e : (Σ q : Q, q.orbit) ≃ α :=
    Equiv.ofBijective (fun x : Σ q : Q, q.orbit => x.2.1)
      ⟨by
        intro x y hxy
        rcases x with ⟨q, a⟩
        rcases y with ⟨r, b⟩
        change a.1 = b.1 at hxy
        have hqr : q = r := calc
          q = Quotient.mk'' (s₁ := MulAction.orbitRel G α) a.1 :=
            (MulAction.orbitRel.Quotient.mem_orbit.mp a.2).symm
          _ = Quotient.mk'' (s₁ := MulAction.orbitRel G α) b.1 := by rw [hxy]
          _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp b.2
        apply Sigma.ext
        · exact hqr
        · subst r
          exact heq_of_eq (Subtype.ext hxy),
       by
        intro y
        exact ⟨⟨Quotient.mk'' (s₁ := MulAction.orbitRel G α) y,
          ⟨y, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩, rfl⟩⟩
  calc
    (∑ q : Q, Nat.card q.orbit) = ∑ q : Q, Fintype.card q.orbit := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Nat.card_eq_fintype_card]
    _ = Fintype.card (Σ q : Q, q.orbit) := by rw [Fintype.card_sigma]
    _ = Fintype.card α := Fintype.card_congr e

public theorem fixedOrbit_card_eq_sub
    {A X : Type*} [Group A] [MulAction A X] [Finite A] [Finite X]
    (p d : Nat) (hp : 1 < p)
    (horbit : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = p)
    (hcount : Nat.card {q : MulAction.orbitRel.Quotient A X //
      Nat.card q.orbit = p} = d) :
    Nat.card {q : MulAction.orbitRel.Quotient A X //
      Nat.card q.orbit = 1} = Nat.card X - p * d := by
  classical
  let Q := MulAction.orbitRel.Quotient A X
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype X := Fintype.ofFinite _
  let : ∀ q : Q, Fintype q.orbit := fun q => Fintype.ofFinite _
  have hsum : (∑ q : Q, Nat.card q.orbit) = Nat.card X := by
    have eX : (Σ q : Q, q.orbit) ≃ X :=
      Equiv.ofBijective (fun z : Σ q : Q, q.orbit => z.2.1)
        ⟨by
          intro z w hzw
          rcases z with ⟨q, x⟩
          rcases w with ⟨r, y⟩
          change x.1 = y.1 at hzw
          have hqr : q = r := calc
            q = Quotient.mk'' x.1 :=
              (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm
            _ = Quotient.mk'' y.1 := by rw [hzw]
            _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp y.2
          apply Sigma.ext
          · exact hqr
          · subst r
            exact heq_of_eq (Subtype.ext hzw),
         by
          intro x
          exact ⟨⟨Quotient.mk'' x,
            ⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩, rfl⟩⟩
    calc
      (∑ q : Q, Nat.card q.orbit) = ∑ q : Q, Fintype.card q.orbit := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Nat.card_eq_fintype_card]
      _ = Fintype.card (Σ q : Q, q.orbit) := Fintype.card_sigma.symm
      _ = Fintype.card X := Fintype.card_congr eX
      _ = Nat.card X := Nat.card_eq_fintype_card.symm
  have hshape (q : Q) :
      Nat.card q.orbit = if Nat.card q.orbit = p then p else 1 := by
    rcases horbit q with hq1 | hqp
    · rw [hq1]
      split_ifs with h
      · omega
      · rfl
    · rw [hqp]
      simp
  have hsumShape : Nat.card X =
      p * Nat.card {q : Q // Nat.card q.orbit = p} +
        Nat.card {q : Q // Nat.card q.orbit = 1} := by
    rw [← hsum]
    have hrewrite : (∑ q : Q, Nat.card q.orbit) =
        ∑ q : Q, if Nat.card q.orbit = p then p else 1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hshape q
    rw [hrewrite]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    have hfixed :
        Finset.univ.filter (fun q : Q => ¬ Nat.card q.orbit = p) =
          Finset.univ.filter (fun q : Q => Nat.card q.orbit = 1) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne
        rcases horbit q with hq1 | hqp
        · exact hq1
        · exact False.elim (hne hqp)
      · intro hq1 hqp
        omega
    change (Finset.univ.filter (fun q : Q => Nat.card q.orbit = p)).card * p +
        (Finset.univ.filter (fun q : Q => ¬ Nat.card q.orbit = p)).card =
      p * (Finset.univ.filter (fun q : Q => Nat.card q.orbit = p)).card +
        (Finset.univ.filter (fun q : Q => Nat.card q.orbit = 1)).card
    rw [hfixed, Nat.mul_comm]
  rw [hcount] at hsumShape
  exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsumShape.symm)

public theorem mem_stabilizer_of_orbit_card_eq_one
    {A X : Type*} [Group A] [MulAction A X] [Finite X]
    (q : MulAction.orbitRel.Quotient A X)
    (hq : Nat.card q.orbit = 1) (a : A) :
    a ∈ MulAction.stabilizer A (Quotient.out q) := by
  classical
  letI : Fintype q.orbit := Fintype.ofFinite _
  have hcard : Fintype.card q.orbit = 1 := by simpa using hq
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  have hout : (⟨Quotient.out q,
      MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' q)⟩ : q.orbit) = u := hu _
  have hsmul : (⟨a • Quotient.out q, by
      rw [MulAction.orbitRel.Quotient.mem_orbit]
      calc
        Quotient.mk'' (s₁ := MulAction.orbitRel A X) (a • Quotient.out q) =
            Quotient.mk'' (s₁ := MulAction.orbitRel A X) (Quotient.out q) :=
          Quotient.sound ⟨a, rfl⟩
        _ = q := Quotient.out_eq' q⟩ : q.orbit) = u := hu _
  exact congrArg Subtype.val (hsmul.trans hout.symm)

public theorem two_mul_finrank_le_of_le_orthogonal
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (W : Submodule K V)
    (hiso : W ≤ B.orthogonal W) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have hdim : Module.finrank K W ≤ Module.finrank K (B.orthogonal W) :=
    Submodule.finrank_mono hiso
  rw [B.finrank_orthogonal hB W] at hdim
  omega

public theorem exists_mulAut_map_eq_of_equiv_image
    {G H : Type*} [Group G] [Group H]
    (f : G ≃* H) (A B : Subgroup G)
    (α : MulAut H)
    (hα : Subgroup.map α.toMonoidHom (Subgroup.map f.toMonoidHom A) =
      Subgroup.map f.toMonoidHom B) :
    ∃ β : MulAut G, Subgroup.map β.toMonoidHom A = B := by
  let β : MulAut G := (MulAut.congr f).symm α
  refine ⟨β, ?_⟩
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  calc
    Subgroup.map f.toMonoidHom (Subgroup.map β.toMonoidHom A) =
        Subgroup.map α.toMonoidHom (Subgroup.map f.toMonoidHom A) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [β]
    _ = Subgroup.map f.toMonoidHom B := hα

private theorem __ch5_PRank_selfEquivSigmaOrbitsQuotientStabilizer_smul
    {G X : Type*} [Group G] [MulAction G X]
    (a b : G) (q : MulAction.orbitRel.Quotient G X) :
    let s := MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X
    s (a • s.symm ⟨q, (b : G ⧸ MulAction.stabilizer G (Quotient.out q))⟩) =
      ⟨q, ((a * b : G) : G ⧸ MulAction.stabilizer G (Quotient.out q))⟩ := by
  dsimp only
  apply (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X).symm.injective
  rw [Equiv.symm_apply_apply]
  change a • MulAction.ofQuotientStabilizer G (Quotient.out q) b =
    MulAction.ofQuotientStabilizer G (Quotient.out q) (a * b)
  exact (MulAction.ofQuotientStabilizer_smul G (Quotient.out q) a b).symm

public theorem exists_equivariantEquiv_of_stabilizer_equiv
    {A B X : Type*} [CommGroup A] [CommGroup B]
    [MulAction A X] [MulAction B X]
    (e : A ≃* B)
    (eqOrbit : MulAction.orbitRel.Quotient A X ≃
      MulAction.orbitRel.Quotient B X)
    (hstab : ∀ q : MulAction.orbitRel.Quotient A X, ∀ a : A,
      a ∈ MulAction.stabilizer A (Quotient.out q) ↔
        e a ∈ MulAction.stabilizer B (Quotient.out (eqOrbit q))) :
    ∃ τ : X ≃ X, ∀ a : A, ∀ x : X, τ (a • x) = e a • τ x := by
  classical
  let eqQuot : (q : MulAction.orbitRel.Quotient A X) →
      (A ⧸ MulAction.stabilizer A (Quotient.out q)) ≃
        (B ⧸ MulAction.stabilizer B (Quotient.out (eqOrbit q))) := fun q => by
    let : (MulAction.stabilizer A (Quotient.out q)).Normal :=
      Subgroup.normal_of_isMulCommutative _
    let : (MulAction.stabilizer B (Quotient.out (eqOrbit q))).Normal :=
      Subgroup.normal_of_isMulCommutative _
    let f := QuotientGroup.map
      (MulAction.stabilizer A (Quotient.out q))
      (MulAction.stabilizer B (Quotient.out (eqOrbit q))) e.toMonoidHom
      (fun a ha => (hstab q a).mp ha)
    let g := QuotientGroup.map
      (MulAction.stabilizer B (Quotient.out (eqOrbit q)))
      (MulAction.stabilizer A (Quotient.out q)) e.symm.toMonoidHom
      (fun b hb => (hstab q (e.symm b)).mpr (by simpa using hb))
    exact {
      toFun := f
      invFun := g
      left_inv := by
        intro z
        induction z using QuotientGroup.induction_on with
        | _ a => simp [f, g]
      right_inv := by
        intro z
        induction z using QuotientGroup.induction_on with
        | _ b => simp [f, g] }
  let sA := MulAction.selfEquivSigmaOrbitsQuotientStabilizer A X
  let sB := MulAction.selfEquivSigmaOrbitsQuotientStabilizer B X
  let mid : ((q : MulAction.orbitRel.Quotient A X) ×
      A ⧸ MulAction.stabilizer A (Quotient.out q)) ≃
      ((q : MulAction.orbitRel.Quotient B X) ×
        B ⧸ MulAction.stabilizer B (Quotient.out q)) :=
    Equiv.sigmaCongr eqOrbit eqQuot
  let τ : X ≃ X := sA.trans (mid.trans sB.symm)
  refine ⟨τ, ?_⟩
  intro a x
  change sB.symm (mid (sA (a • x))) = e a • sB.symm (mid (sA x))
  apply sB.injective
  rw [sB.apply_symm_apply]
  generalize hsx : sA x = sx
  rcases sx with ⟨q, z⟩
  have hx : x = sA.symm ⟨q, z⟩ := by
    rw [← hsx, sA.symm_apply_apply]
  rw [hx]
  induction z using QuotientGroup.induction_on with
  | _ b =>
      rw [__ch5_PRank_selfEquivSigmaOrbitsQuotientStabilizer_smul]
      change mid ⟨q, ((a * b : A) : A ⧸ _)⟩ = _
      rw [show mid ⟨q, (b : A ⧸ _)⟩ =
        Sigma.mk (eqOrbit q) ((e b : B) : B ⧸ MulAction.stabilizer B
          (Quotient.out (eqOrbit q))) by
        change @Sigma.mk _ (fun r : MulAction.orbitRel.Quotient B X =>
          B ⧸ MulAction.stabilizer B (Quotient.out r)) (eqOrbit q)
            (eqQuot q (b : A ⧸ _)) = _
        congr 1]
      rw [__ch5_PRank_selfEquivSigmaOrbitsQuotientStabilizer_smul]
      change @Sigma.mk _ (fun r : MulAction.orbitRel.Quotient B X =>
        B ⧸ MulAction.stabilizer B (Quotient.out r)) (eqOrbit q)
          (eqQuot q ((a * b : A) : A ⧸ _)) = _
      congr 1
      simp [eqQuot]

end GLS3.Chapter5.PRank
/- END Theory.PRank -/

/- BEGIN Theory.PRankSmallOrbit -/
noncomputable section
namespace GLS3.Chapter5.PRank
open MulAction
open scoped BigOperators

public abbrev SmallOrbitSpace (t s : Nat) :=
  (Fin t → ZMod 2) × (Fin s × Fin 2 → ZMod 2)

@[expose] public noncomputable def smallOrbitBilin (t s : Nat) :
    LinearMap.BilinForm (ZMod 2) (SmallOrbitSpace t s) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y =>
      (∑ i, x.1 i * y.1 i) +
        ∑ j, (x.2 (j, 0) * y.2 (j, 1) + x.2 (j, 1) * y.2 (j, 0)))
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
      abel)
    (by intros; simp [Finset.mul_sum, mul_add, mul_assoc])
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
        Finset.sum_add_distrib]
      abel)
    (by
      intros c m n
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        ring)

public theorem smallOrbitBilin_nondegenerate_and_finrank (t s : Nat) :
    (smallOrbitBilin t s).Nondegenerate ∧
      Module.finrank (ZMod 2) (SmallOrbitSpace t s) = t + 2 * s := by
  classical
  have hsymm (x y : SmallOrbitSpace t s) :
      smallOrbitBilin t s x y = smallOrbitBilin t s y x := by
    change (∑ i, x.1 i * y.1 i) +
        ∑ j, (x.2 (j, 0) * y.2 (j, 1) + x.2 (j, 1) * y.2 (j, 0)) =
      (∑ i, y.1 i * x.1 i) +
        ∑ j, (y.2 (j, 0) * x.2 (j, 1) + y.2 (j, 1) * x.2 (j, 0))
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  have hleft : ∀ x : SmallOrbitSpace t s,
      (∀ y, smallOrbitBilin t s x y = 0) → x = 0 := by
    intro x hx
    apply Prod.ext
    · funext i
      have h := hx (LinearMap.single (ZMod 2) (fun _ : Fin t => ZMod 2) i 1, 0)
      simpa [smallOrbitBilin, Pi.single_apply] using h
    · funext jk
      rcases jk with ⟨j, k⟩
      fin_cases k
      · have h := hx (0, LinearMap.single (ZMod 2)
          (fun _ : Fin s × Fin 2 => ZMod 2) (j, 1) 1)
        simpa [smallOrbitBilin, Pi.single_apply] using h
      · have h := hx (0, LinearMap.single (ZMod 2)
          (fun _ : Fin s × Fin 2 => ZMod 2) (j, 0) 1)
        simpa [smallOrbitBilin, Pi.single_apply] using h
  have hright : ∀ y : SmallOrbitSpace t s,
      (∀ x, smallOrbitBilin t s x y = 0) → y = 0 := by
    intro y hy
    apply hleft y
    intro x
    rw [hsymm]
    exact hy x
  refine ⟨⟨hleft, hright⟩, ?_⟩
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
  simp
  omega

open MulAction
open scoped BigOperators

public theorem two_mul_smallOrbitDimension_le_card
    {A X : Type*} [Group A] [MulAction A X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient A X)] :
    let Q := MulAction.orbitRel.Quotient A X
    let T := {q : Q // Nat.card q.orbit = 2}
    let S := {q : Q // Nat.card q.orbit = 4}
    2 * (Nat.card T + 2 * Nat.card S) ≤ Fintype.card X := by
  classical
  let Q := MulAction.orbitRel.Quotient A X
  let T := {q : Q // Nat.card q.orbit = 2}
  let S := {q : Q // Nat.card q.orbit = 4}
  haveI : Fintype T := Fintype.ofFinite _
  haveI : Fintype S := Fintype.ofFinite _
  have : ∀ q : T, Fintype q.1.orbit := fun _ => Fintype.ofFinite _
  have : ∀ q : S, Fintype q.1.orbit := fun _ => Fintype.ofFinite _
  let f : (Σ q : T, q.1.orbit) ⊕ (Σ q : S, q.1.orbit) → X
    | Sum.inl z => z.2.1
    | Sum.inr z => z.2.1
  have hquot_eq {q r : Q} {x : q.orbit} {y : r.orbit} (hxy : x.1 = y.1) : q = r := by
    calc
      q = Quotient.mk'' x.1 := (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm
      _ = Quotient.mk'' y.1 := by rw [hxy]
      _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp y.2
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            rcases x with ⟨q, x⟩
            rcases y with ⟨r, y⟩
            have hqr : q = r := by
              apply Subtype.ext
              exact hquot_eq hxy
            subst r
            exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq (Subtype.ext hxy)))
        | inr y =>
            rcases x with ⟨q, x⟩
            rcases y with ⟨r, y⟩
            have hcard := q.2
            rw [congrArg (fun q : Q => q.orbit) (hquot_eq hxy), r.2] at hcard
            omega
    | inr x =>
        cases y with
        | inl y =>
            rcases x with ⟨q, x⟩
            rcases y with ⟨r, y⟩
            have hcard := q.2
            rw [congrArg (fun q : Q => q.orbit) (hquot_eq hxy), r.2] at hcard
            omega
        | inr y =>
            rcases x with ⟨q, x⟩
            rcases y with ⟨r, y⟩
            have hqr : q = r := by
              apply Subtype.ext
              exact hquot_eq hxy
            subst r
            exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext hxy)))
  have hcard := Fintype.card_le_of_injective f hf
  have hT : Fintype.card (Σ q : T, q.1.orbit) = 2 * Nat.card T := by
    rw [Fintype.card_sigma]
    calc
      (∑ q : T, Fintype.card q.1.orbit) = ∑ _q : T, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        simpa [Nat.card_eq_fintype_card] using q.2
      _ = 2 * Nat.card T := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]
  have hS : Fintype.card (Σ q : S, q.1.orbit) = 4 * Nat.card S := by
    rw [Fintype.card_sigma]
    calc
      (∑ q : S, Fintype.card q.1.orbit) = ∑ _q : S, 4 := by
        apply Finset.sum_congr rfl
        intro q hq
        simpa [Nat.card_eq_fintype_card] using q.2
      _ = 4 * Nat.card S := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]
  rw [Fintype.card_sum, hT, hS] at hcard
  have hlocal : 2 * (Nat.card T + 2 * Nat.card S) ≤ Fintype.card X := by omega
  simpa [Q, T, S] using hlocal

/-- An injective binary-linear realization inside the standard small-orbit
space has the expected cardinality bound when its image is totally isotropic. -/
public theorem card_le_pow_half_smallOrbitSpace_of_isotropic
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (t s : Nat)
    (f : V →ₗ[ZMod 2] SmallOrbitSpace t s)
    (hf : Function.Injective f)
    (hiso : ∀ x y : V, smallOrbitBilin t s (f x) (f y) = 0) :
    Nat.card V ≤ 2 ^ ((t + 2 * s) / 2) := by
  let W : Submodule (ZMod 2) (SmallOrbitSpace t s) := LinearMap.range f
  have hWiso : W ≤ (smallOrbitBilin t s).orthogonal W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rcases hx with ⟨x0, rfl⟩
    rcases hy with ⟨y0, rfl⟩
    exact hiso y0 x0
  have hdim := two_mul_finrank_le_of_le_orthogonal (smallOrbitBilin t s)
    (smallOrbitBilin_nondegenerate_and_finrank t s).1 W hWiso
  rw [(smallOrbitBilin_nondegenerate_and_finrank t s).2] at hdim
  have hfinrank : Module.finrank (ZMod 2) V ≤ (t + 2 * s) / 2 := by
    have hrange : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V := by
      exact LinearMap.finrank_range_of_inj hf
    rw [hrange] at hdim
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega
  have hcard : Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := V))
  rw [Nat.card_eq_fintype_card, hcard]
  exact Nat.pow_le_pow_right (by omega) hfinrank

open MulAction
open scoped BigOperators

public theorem support_card_eq_sum_orbit_indicator
    {A X : Type*} [CommGroup A] [MulAction A X] [Fintype X] [DecidableEq X]
    [Fintype (MulAction.orbitRel.Quotient A X)] (a : A) :
    ((MulAction.toPerm a : Equiv.Perm X)).support.card =
      ∑ q : MulAction.orbitRel.Quotient A X,
        if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else Nat.card q.orbit := by
  classical
  let Q := MulAction.orbitRel.Quotient A X
  have : ∀ q : Q, Fintype q.orbit := fun q => Fintype.ofFinite _
  let e : (Σ q : Q, q.orbit) ≃ X :=
    Equiv.ofBijective (fun z : Σ q : Q, q.orbit => z.2.1)
      ⟨by
        intro x y hxy
        rcases x with ⟨q, x⟩
        rcases y with ⟨r, y⟩
        change x.1 = y.1 at hxy
        have hqr : q = r := by
          calc
            q = Quotient.mk'' x.1 := (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm
            _ = Quotient.mk'' y.1 := by rw [hxy]
            _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp y.2
        subst r
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy)),
       by
        intro x
        exact ⟨⟨Quotient.mk'' x,
          ⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩, rfl⟩⟩
  rw [Finset.card_eq_sum_ones]
  change (∑ x ∈ ((MulAction.toPerm a : Equiv.Perm X)).support, 1) = _
  have hs :
      (∑ x ∈ ((MulAction.toPerm a : Equiv.Perm X)).support, 1) =
        ∑ x : X, if (MulAction.toPerm a : Equiv.Perm X) x ≠ x then 1 else 0 := by
    rw [← Finset.sum_filter]
    rfl
  rw [hs]
  rw [← (Equiv.sum_comp e (fun x : X => if (MulAction.toPerm a : Equiv.Perm X) x ≠ x then 1 else 0))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ha : a ∈ MulAction.stabilizer A (Quotient.out q)
  · rw [if_pos ha]
    have hfix : ∀ x : q.orbit, a • x.1 = x.1 := by
      intro x
      have hxorb : x.1 ∈ MulAction.orbit A (Quotient.out q) := by
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
        exact x.2
      rcases hxorb with ⟨b, hb⟩
      rw [← hb, ← mul_smul, mul_comm a b, mul_smul, ha]
    change (∑ x : q.orbit, if a • x.1 ≠ x.1 then 1 else 0) = 0
    simp [hfix]
  · rw [if_neg ha]
    have hmove : ∀ x : q.orbit, a • x.1 ≠ x.1 := by
      intro x hx
      apply ha
      have hxorb : x.1 ∈ MulAction.orbit A (Quotient.out q) := by
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
        exact x.2
      rcases hxorb with ⟨b, hb⟩
      change a • Quotient.out q = Quotient.out q
      have h := congrArg (fun y => b⁻¹ • y) hx
      rw [← hb] at h
      simpa [← mul_smul, mul_comm a b] using h
    change (∑ x : q.orbit, if a • x.1 ≠ x.1 then 1 else 0) = Nat.card q.orbit
    simp [hmove, Nat.card_eq_fintype_card]

open MulAction

public theorem exists_orbitQuotientLinearMap
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A]
    [Module (ZMod 2) (Additive A)]
    (hA : IsElementaryAbelian A 2) (x : X) (d : Nat)
    (hcard : Nat.card (MulAction.orbit A x) = 2 ^ d) :
    ∃ f : Additive A →ₗ[ZMod 2] (Fin d → ZMod 2),
      ∀ a : A, f (Additive.ofMul a) = 0 ↔ a ∈ MulAction.stabilizer A x := by
  let N : Subgroup A := MulAction.stabilizer A x
  let : N.Normal := Subgroup.normal_of_isMulCommutative N
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (by
    intro a
    change a.toMul ^ 2 = 1
    rcases hA.2 a.toMul with h | h
    · have ha : a.toMul = 1 := orderOf_eq_one_iff.mp h
      simp [ha]
    · exact orderOf_dvd_iff_pow_eq_one.mp (by simp [h]))
  letI : Fintype (Additive (A ⧸ N)) := Fintype.ofFinite _
  letI : Module (ZMod 2) (Additive (A ⧸ N)) := AddCommGroup.zmodModule (by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ a =>
        change QuotientGroup.mk' N (a ^ 2) = 1
        rcases hA.2 a with h | h
        · have ha : a = 1 := orderOf_eq_one_iff.mp h
          simp [ha]
        · rw [orderOf_dvd_iff_pow_eq_one.mp (by simp [h])]
          exact map_one _)
  have hquot : Nat.card (A ⧸ N) = 2 ^ d := by
    rw [← Subgroup.index_eq_card]
    change (MulAction.stabilizer A x).index = 2 ^ d
    rw [MulAction.index_stabilizer]
    simpa [Set.ncard_eq_toFinset_card, Nat.card_coe_set_eq] using hcard
  let e := Classical.choice (exists_linearEquiv_fin_of_card_eq_pow (Additive (A ⧸ N)) d hquot)
  let qlin : Additive A →ₗ[ZMod 2] Additive (A ⧸ N) :=
    ((QuotientGroup.mk' N).toAdditive).toZModLinearMap 2
  let f : Additive A →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun a => e (qlin a)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  refine ⟨f, ?_⟩
  intro a
  change e (Additive.ofMul (QuotientGroup.mk' N a)) = 0 ↔ a ∈ N
  rw [e.map_eq_zero_iff]
  change QuotientGroup.mk' N a = 1 ↔ a ∈ N
  exact QuotientGroup.eq_one_iff a

private lemma __ch5_PRankSmallOrbit_fixes_orbit_of_mem_stabilizer
    {A X : Type*} [CommGroup A] [MulAction A X]
    {a : A} {x y : X} (ha : a ∈ MulAction.stabilizer A x)
    (hy : y ∈ MulAction.orbit A x) : a • y = y := by
  rcases hy with ⟨b, rfl⟩
  rw [← mul_smul, mul_comm a b, mul_smul, ha]

public theorem exists_smallOrbitLinearMap
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Finite X]
    [Module (ZMod 2) (Additive A)]
    (hA : IsElementaryAbelian A 2)
    (hsmall : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X))) :
    let Q := MulAction.orbitRel.Quotient A X
    let T := {q : Q // Nat.card q.orbit = 2}
    let S := {q : Q // Nat.card q.orbit = 4}
    ∃ eT : Fin (Nat.card T) ≃ T,
    ∃ eS : Fin (Nat.card S) ≃ S,
    ∃ f : Additive A →ₗ[ZMod 2] SmallOrbitSpace (Nat.card T) (Nat.card S),
      Function.Injective f ∧
      (∀ a : A,
        (∀ i : Fin (Nat.card T),
          (f (Additive.ofMul a)).1 i = 0 ↔
            a ∈ MulAction.stabilizer A (Quotient.out (eT i).1)) ∧
        (∀ j : Fin (Nat.card S),
          (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0 ↔
            a ∈ MulAction.stabilizer A (Quotient.out (eS j).1))) := by
  classical
  let Q := MulAction.orbitRel.Quotient A X
  let T := {q : Q // Nat.card q.orbit = 2}
  let S := {q : Q // Nat.card q.orbit = 4}
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  letI : Fintype S := Fintype.ofFinite _
  let eT : Fin (Nat.card T) ≃ T := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.equivFin T).symm
  let eS : Fin (Nat.card S) ≃ S := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.equivFin S).symm
  have horbit_out (q : Q) :
      Nat.card (MulAction.orbit A (Quotient.out q)) = Nat.card q.orbit := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
  let rawT : (i : Fin (Nat.card T)) → Additive A →ₗ[ZMod 2] (Fin 1 → ZMod 2) := fun i =>
    Classical.choose (exists_orbitQuotientLinearMap hA (Quotient.out (eT i).1) 1 (by
      rw [horbit_out]
      simpa using (eT i).2))
  let fT : (i : Fin (Nat.card T)) → Additive A →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun a => rawT i a 0
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let rawS : (j : Fin (Nat.card S)) → Additive A →ₗ[ZMod 2] (Fin 2 → ZMod 2) := fun j =>
    Classical.choose (exists_orbitQuotientLinearMap hA
      (Quotient.out (eS j).1) 2 (by
        rw [horbit_out]
        simpa using (eS j).2))
  let fS : Additive A →ₗ[ZMod 2] (Fin (Nat.card S) × Fin 2 → ZMod 2) :=
    { toFun := fun a jk => rawS jk.1 a jk.2
      map_add' := by intros; funext jk; simp
      map_smul' := by intros; funext jk; simp }
  let f : Additive A →ₗ[ZMod 2] SmallOrbitSpace (Nat.card T) (Nat.card S) :=
    (LinearMap.pi fT).prod fS
  refine ⟨eT, eS, f, ?_, ?_⟩
  · intro a b hab
    have hz : f (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    apply Additive.toMul.injective
    have hg : (a - b).toMul = 1 := by
      apply hfaith
      funext x
      let q : Q := Quotient.mk'' x
      have hxorb : x ∈ MulAction.orbit A (Quotient.out q) := by
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
        exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
      rcases hsmall q with hq1 | hq2 | hq4
      · have : Fintype q.orbit := Fintype.ofFinite _
        have hc : Fintype.card q.orbit = 1 := by simpa using hq1
        obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hc
        have hout : (⟨Quotient.out q, by
            exact MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' q)⟩ : q.orbit) = u := hu _
        have hx : (⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩ : q.orbit) = u := hu _
        have hxeq : x = Quotient.out q := congrArg Subtype.val (hx.trans hout.symm)
        have hm : (a - b).toMul • x ∈ q.orbit := by
          rw [MulAction.orbitRel.Quotient.mem_orbit]
          exact Quotient.sound ⟨(a - b).toMul, rfl⟩
        have heq : (a - b).toMul • x = x := by
          have hmx : (⟨(a - b).toMul • x, hm⟩ : q.orbit) = u := hu _
          exact congrArg Subtype.val (hmx.trans hx.symm)
        simpa using heq
      · let ti : T := ⟨q, hq2⟩
        let i : Fin (Nat.card T) := eT.symm ti
        have hcoord : fT i (a - b) = 0 := by
          have := congrArg (fun z => z.1 i) hz
          exact this
        have hraw : rawT i (a - b) = 0 := by
          funext k
          fin_cases k
          exact hcoord
        have hspec := Classical.choose_spec (exists_orbitQuotientLinearMap hA
          (Quotient.out q) 1 (by rw [horbit_out]; exact hq2)) ((a - b).toMul)
        have hstab : (a - b).toMul ∈ MulAction.stabilizer A (Quotient.out q) := by
          apply hspec.mp
          have hi_eq : eT i = ti := eT.apply_symm_apply ti
          dsimp [rawT] at hraw
          rw [hi_eq] at hraw
          exact hraw
        simpa using __ch5_PRankSmallOrbit_fixes_orbit_of_mem_stabilizer hstab hxorb
      · let sj : S := ⟨q, hq4⟩
        let j : Fin (Nat.card S) := eS.symm sj
        have hraw : rawS j (a - b) = 0 := by
          funext k
          have hzjk := congrArg (fun z => z.2 (j, k)) hz
          exact hzjk
        have hspec := Classical.choose_spec (exists_orbitQuotientLinearMap hA
          (Quotient.out q) 2 (by rw [horbit_out]; exact hq4)) ((a - b).toMul)
        have hstab : (a - b).toMul ∈ MulAction.stabilizer A (Quotient.out q) := by
          apply hspec.mp
          have hj_eq : eS j = sj := eS.apply_symm_apply sj
          dsimp [rawS] at hraw
          rw [hj_eq] at hraw
          exact hraw
        simpa using __ch5_PRankSmallOrbit_fixes_orbit_of_mem_stabilizer hstab hxorb
    exact div_eq_one.mp (by simpa using hg)
  · intro a
    constructor
    · intro i
      change fT i (Additive.ofMul a) = 0 ↔ _
      have hs := Classical.choose_spec (exists_orbitQuotientLinearMap hA
        (Quotient.out (eT i).1) 1 (by rw [horbit_out]; simpa using (eT i).2)) a
      have hs' : rawT i (Additive.ofMul a) = 0 ↔
          a ∈ MulAction.stabilizer A (Quotient.out (eT i).1) := by
        simpa [rawT] using hs
      rw [← hs']
      constructor
      · intro h
        funext k
        fin_cases k
        exact h
      · intro h
        exact congrFun h 0
    · intro j
      change rawS j (Additive.ofMul a) = 0 ↔ _
      have hs := Classical.choose_spec (exists_orbitQuotientLinearMap hA
        (Quotient.out (eS j).1) 2 (by rw [horbit_out]; simpa using (eS j).2)) a
      dsimp [rawS]
      exact hs

private def __ch5_PRankSmallOrbit_bitNat (a : ZMod 2) : Nat := if a = 0 then 0 else 1
private def __ch5_PRankSmallOrbit_pairNat (a : Fin 2 → ZMod 2) : Nat := if a = 0 then 0 else 1
private def __ch5_PRankSmallOrbit_bitFour (a : ZMod 2) : ZMod 4 := if a = 0 then 0 else 1
private def __ch5_PRankSmallOrbit_pairFour (a : Fin 2 → ZMod 2) : ZMod 4 := if a = 0 then 0 else 2
private def __ch5_PRankSmallOrbit_bilinFour (a : ZMod 2) : ZMod 4 := if a = 0 then 0 else 2

private lemma __ch5_PRankSmallOrbit_bitFour_add (a b : ZMod 2) :
    __ch5_PRankSmallOrbit_bitFour (a + b) = __ch5_PRankSmallOrbit_bitFour a + __ch5_PRankSmallOrbit_bitFour b + __ch5_PRankSmallOrbit_bilinFour (a * b) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma __ch5_PRankSmallOrbit_pairFour_add (a b : Fin 2 → ZMod 2) :
    __ch5_PRankSmallOrbit_pairFour (a + b) = __ch5_PRankSmallOrbit_pairFour a + __ch5_PRankSmallOrbit_pairFour b +
      __ch5_PRankSmallOrbit_bilinFour (a 0 * b 1 + a 1 * b 0) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma __ch5_PRankSmallOrbit_bilinFour_add (a b : ZMod 2) :
    __ch5_PRankSmallOrbit_bilinFour (a + b) = __ch5_PRankSmallOrbit_bilinFour a + __ch5_PRankSmallOrbit_bilinFour b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma __ch5_PRankSmallOrbit_sum_bilinFour_finset {ι : Type*} (u : Finset ι) (f : ι → ZMod 2) :
    ∑ i ∈ u, __ch5_PRankSmallOrbit_bilinFour (f i) = __ch5_PRankSmallOrbit_bilinFour (∑ i ∈ u, f i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [__ch5_PRankSmallOrbit_bilinFour]
  | @insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, __ch5_PRankSmallOrbit_bilinFour_add]

private lemma __ch5_PRankSmallOrbit_sum_bilinFour {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    ∑ i, __ch5_PRankSmallOrbit_bilinFour (f i) = __ch5_PRankSmallOrbit_bilinFour (∑ i, f i) := by
  simpa using __ch5_PRankSmallOrbit_sum_bilinFour_finset (Finset.univ : Finset ι) f

@[expose] public def smallOrbitWeight (t s : Nat) (x : SmallOrbitSpace t s) : Nat :=
  (∑ i, if x.1 i = 0 then 0 else 1) +
    2 * ∑ j, if (fun k => (fun k => x.2 (j, k)) k) = 0 then 0 else 1

private lemma __ch5_PRankSmallOrbit_cast_weight (t s : Nat) (x : SmallOrbitSpace t s) :
    (smallOrbitWeight t s x : ZMod 4) =
      ∑ i, __ch5_PRankSmallOrbit_bitFour (x.1 i) + ∑ j, __ch5_PRankSmallOrbit_pairFour (fun k => (fun k => x.2 (j, k)) k) := by
  rw [smallOrbitWeight, Nat.cast_add, Nat.cast_mul]
  congr 1
  · simp [__ch5_PRankSmallOrbit_bitFour]
  · rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [__ch5_PRankSmallOrbit_pairFour]

private lemma __ch5_PRankSmallOrbit_cast_weight_add (t s : Nat) (x y : SmallOrbitSpace t s) :
    (smallOrbitWeight t s (x + y) : ZMod 4) =
      (smallOrbitWeight t s x : ZMod 4) +
      (smallOrbitWeight t s y : ZMod 4) +
      __ch5_PRankSmallOrbit_bilinFour (smallOrbitBilin t s x y) := by
  rw [__ch5_PRankSmallOrbit_cast_weight, __ch5_PRankSmallOrbit_cast_weight, __ch5_PRankSmallOrbit_cast_weight]
  change
    (∑ i, __ch5_PRankSmallOrbit_bitFour (x.1 i + y.1 i)) +
        ∑ j, __ch5_PRankSmallOrbit_pairFour (fun k => (fun k => x.2 (j, k)) k + (fun k => y.2 (j, k)) k) = _
  simp_rw [__ch5_PRankSmallOrbit_bitFour_add]
  have hpair : ∀ j : Fin s,
      __ch5_PRankSmallOrbit_pairFour (fun k => (fun k => x.2 (j, k)) k + (fun k => y.2 (j, k)) k) =
        __ch5_PRankSmallOrbit_pairFour (fun k => (fun k => x.2 (j, k)) k) + __ch5_PRankSmallOrbit_pairFour (fun k => (fun k => y.2 (j, k)) k) +
          __ch5_PRankSmallOrbit_bilinFour (x.2 (j, 0) * y.2 (j, 1) + x.2 (j, 1) * y.2 (j, 0)) := by
    intro j
    exact __ch5_PRankSmallOrbit_pairFour_add _ _
  simp_rw [hpair]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [__ch5_PRankSmallOrbit_sum_bilinFour, __ch5_PRankSmallOrbit_sum_bilinFour, Finset.sum_add_distrib]
  change _ = _ + _ + __ch5_PRankSmallOrbit_bilinFour
    ((∑ i, x.1 i * y.1 i) +
      ∑ j, (x.2 (j, 0) * y.2 (j, 1) + x.2 (j, 1) * y.2 (j, 0)))
  rw [__ch5_PRankSmallOrbit_bilinFour_add, Finset.sum_add_distrib, __ch5_PRankSmallOrbit_bilinFour_add, __ch5_PRankSmallOrbit_bilinFour_add]
  ac_rfl

private lemma __ch5_PRankSmallOrbit_bilinFour_eq_zero_iff (a : ZMod 2) : __ch5_PRankSmallOrbit_bilinFour a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have hne : (2 : ZMod 4) ≠ 0 := by decide
    exact hne (by simpa [__ch5_PRankSmallOrbit_bilinFour, ha] using h)
  · intro ha
    simp [__ch5_PRankSmallOrbit_bilinFour, ha]

public theorem smallOrbitBilin_eq_zero_of_weight_dvd_four
    (t s : Nat) (V : AddSubgroup (SmallOrbitSpace t s))
    (hweight : ∀ x : V, 4 ∣ smallOrbitWeight t s x) :
    ∀ x y : V, smallOrbitBilin t s x y = 0 := by
  intro x y
  have hx : (smallOrbitWeight t s x : ZMod 4) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 4) 4 _).2 (hweight x)
  have hy : (smallOrbitWeight t s y : ZMod 4) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 4) 4 _).2 (hweight y)
  have hxy : (smallOrbitWeight t s ((x + y : V) : SmallOrbitSpace t s) : ZMod 4) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 4) 4 _).2 (hweight (x + y))
  have hpolar := __ch5_PRankSmallOrbit_cast_weight_add t s (x : SmallOrbitSpace t s) y
  have hxy' : (smallOrbitWeight t s ((x : SmallOrbitSpace t s) + y) : ZMod 4) = 0 := by
    simpa using hxy
  rw [hxy', hx, hy, zero_add, zero_add] at hpolar
  exact (__ch5_PRankSmallOrbit_bilinFour_eq_zero_iff _).mp hpolar.symm

open MulAction
open scoped BigOperators

public theorem support_card_eq_two_mul_smallOrbitWeight
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X] [DecidableEq X]
    [Module (ZMod 2) (Additive A)]
    (hsmall : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4)
    (eT : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
    (eS : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})
    (f : Additive A →ₗ[ZMod 2]
      SmallOrbitSpace
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}))
    (hspec : ∀ a : A,
      (∀ i,
        (f (Additive.ofMul a)).1 i = 0 ↔
          a ∈ MulAction.stabilizer A (Quotient.out (eT i).1)) ∧
      (∀ j,
        (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0 ↔
          a ∈ MulAction.stabilizer A (Quotient.out (eS j).1)))
    (a : A) :
    ((MulAction.toPerm a : Equiv.Perm X)).support.card =
      2 * smallOrbitWeight
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})
        (f (Additive.ofMul a)) := by
  classical
  let Q := MulAction.orbitRel.Quotient A X
  let T := {q : Q // Nat.card q.orbit = 2}
  let S := {q : Q // Nat.card q.orbit = 4}
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  letI : Fintype S := Fintype.ofFinite _
  have hfixed_of_card_one (q : Q) (hq : Nat.card q.orbit = 1) :
      a ∈ MulAction.stabilizer A (Quotient.out q) := by
    haveI : Fintype q.orbit := Fintype.ofFinite _
    have hc : Fintype.card q.orbit = 1 := by simpa using hq
    obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hc
    have hout : (⟨Quotient.out q,
        MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' q)⟩ : q.orbit) = u := hu _
    have hsmul_mem : a • Quotient.out q ∈ q.orbit := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
      exact MulAction.mem_orbit _ _
    have hsmul : (⟨a • Quotient.out q, hsmul_mem⟩ : q.orbit) = u := hu _
    exact congrArg Subtype.val (hsmul.trans hout.symm)
  have horbit :
      ((MulAction.toPerm a : Equiv.Perm X)).support.card =
        ∑ q : Q, if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else Nat.card q.orbit :=
    support_card_eq_sum_orbit_indicator a
  calc
    ((MulAction.toPerm a : Equiv.Perm X)).support.card =
        ∑ q : Q, if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else Nat.card q.orbit := horbit
    _ =
        ∑ q : Q, ((if Nat.card q.orbit = 2 then
            if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else 2
          else 0) +
          (if Nat.card q.orbit = 4 then
            if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else 4
          else 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rcases hsmall q with h1 | h2 | h4
      · rw [h1]
        have hs : a • Quotient.out q = Quotient.out q := hfixed_of_card_one q h1
        simp [hs]
      · rw [h2]
        by_cases hs : a • Quotient.out q = Quotient.out q <;> simp [hs]
      · rw [h4]
        by_cases hs : a • Quotient.out q = Quotient.out q <;> simp [hs]
    _ =
        (∑ q : Q, if Nat.card q.orbit = 2 then
          if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else 2
        else 0) +
        (∑ q : Q, if Nat.card q.orbit = 4 then
          if a ∈ MulAction.stabilizer A (Quotient.out q) then 0 else 4
        else 0) := by rw [Finset.sum_add_distrib]
    _ =
        (∑ q : T, if a ∈ MulAction.stabilizer A (Quotient.out q.1) then 0 else 2) +
        (∑ q : S, if a ∈ MulAction.stabilizer A (Quotient.out q.1) then 0 else 4) := by
      congr 1
      · rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      · rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
    _ =
        (∑ i, if (f (Additive.ofMul a)).1 i = 0 then 0 else 2) +
        (∑ j, if (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0 then 0 else 4) := by
      rw [← Equiv.sum_comp eT, ← Equiv.sum_comp eS]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        by_cases hs : a ∈ MulAction.stabilizer A (Quotient.out (eT i).1)
        · rw [if_pos hs, if_pos ((hspec a).1 i |>.mpr hs)]
        · rw [if_neg hs, if_neg (fun hz => hs ((hspec a).1 i |>.mp hz))]
      · apply Finset.sum_congr rfl
        intro j hj
        by_cases hs : a ∈ MulAction.stabilizer A (Quotient.out (eS j).1)
        · rw [if_pos hs, if_pos ((hspec a).2 j |>.mpr hs)]
        · rw [if_neg hs, if_neg (fun hz => hs ((hspec a).2 j |>.mp hz))]
    _ = 2 * smallOrbitWeight (Nat.card T) (Nat.card S) (f (Additive.ofMul a)) := by
      simp only [smallOrbitWeight, Nat.mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        by_cases hz : (f (Additive.ofMul a)).1 i = 0
        · rw [if_pos hz, if_pos hz]
          norm_num
        · rw [if_neg hz, if_neg hz]
          norm_num
      · apply Finset.sum_congr rfl
        intro j hj
        by_cases hz : (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0
        · rw [if_pos hz, if_pos hz]
          norm_num
        · rw [if_neg hz, if_neg hz]
          norm_num

public theorem smallOrbitWeight_dvd_four_of_support_dvd_eight
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [DecidableEq X] [Module (ZMod 2) (Additive A)]
    (hsmall : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4)
    (eT : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
    (eS : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})
    (f : Additive A →ₗ[ZMod 2]
      SmallOrbitSpace
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}))
    (hspec : ∀ a : A,
      (∀ i, (f (Additive.ofMul a)).1 i = 0 ↔
        a ∈ MulAction.stabilizer A (Quotient.out (eT i).1)) ∧
      (∀ j, (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0 ↔
        a ∈ MulAction.stabilizer A (Quotient.out (eS j).1)))
    (hsupport : ∀ a : A, a ≠ 1 →
      8 ∣ ((MulAction.toPerm a : Equiv.Perm X)).support.card) :
    ∀ x : Additive A,
      4 ∣ smallOrbitWeight
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}) (f x) := by
  intro x
  let a : A := x.toMul
  have hxa : Additive.ofMul a = x := rfl
  by_cases ha : a = 1
  · rw [← hxa, ha]
    change 4 ∣ smallOrbitWeight
      (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
      (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}) (f 0)
    rw [map_zero, smallOrbitWeight]
    have hbit : ∀ i : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2}),
        (0 : SmallOrbitSpace
          (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
          (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})).1 i = 0 := by
      intro i
      rfl
    have hpair : ∀ j : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}),
        (fun k => (fun k => (0 : SmallOrbitSpace
          (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
          (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})).2 (j, k)) k) = 0 := by
      intro j
      rfl
    simp_rw [hbit, hpair]
    simp
  · have hdvd := hsupport a ha
    have heq := support_card_eq_two_mul_smallOrbitWeight hsmall eT eS f hspec a
    rw [hxa] at heq
    rw [heq] at hdvd
    rcases hdvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega

public theorem smallOrbitBilin_eq_zero_of_support_dvd_eight
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [DecidableEq X] [Module (ZMod 2) (Additive A)]
    (hsmall : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4)
    (eT : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
    (eS : Fin (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}) ≃
      {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})
    (f : Additive A →ₗ[ZMod 2]
      SmallOrbitSpace
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}))
    (hspec : ∀ a : A,
      (∀ i, (f (Additive.ofMul a)).1 i = 0 ↔
        a ∈ MulAction.stabilizer A (Quotient.out (eT i).1)) ∧
      (∀ j, (fun k => (f (Additive.ofMul a)).2 (j, k)) = 0 ↔
        a ∈ MulAction.stabilizer A (Quotient.out (eS j).1)))
    (hsupport : ∀ a : A, a ≠ 1 →
      8 ∣ ((MulAction.toPerm a : Equiv.Perm X)).support.card) :
    ∀ x y : Additive A,
      smallOrbitBilin
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2})
        (Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4})
        (f x) (f y) = 0 := by
  let t := Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 2}
  let s := Nat.card {q : MulAction.orbitRel.Quotient A X // Nat.card q.orbit = 4}
  have hweight := smallOrbitWeight_dvd_four_of_support_dvd_eight
    hsmall eT eS f hspec hsupport
  let V : AddSubgroup (SmallOrbitSpace t s) := (LinearMap.range f).toAddSubgroup
  have hweightRange : ∀ z : V, 4 ∣ smallOrbitWeight t s z.1 := by
    intro z
    rcases z.2 with ⟨x, hx⟩
    rw [← hx]
    exact hweight x
  have hisoRange := smallOrbitBilin_eq_zero_of_weight_dvd_four t s V hweightRange
  intro x y
  exact hisoRange ⟨f x, ⟨x, rfl⟩⟩ ⟨f y, ⟨y, rfl⟩⟩

public theorem exists_smallOrbitIsotropicLinearMap
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [DecidableEq X] [Module (ZMod 2) (Additive A)]
    (hA : IsElementaryAbelian A 2)
    (hsmall : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X)))
    (hsupport : ∀ a : A, a ≠ 1 →
      8 ∣ ((MulAction.toPerm a : Equiv.Perm X)).support.card) :
    let Q := MulAction.orbitRel.Quotient A X
    let T := {q : Q // Nat.card q.orbit = 2}
    let S := {q : Q // Nat.card q.orbit = 4}
    ∃ f : Additive A →ₗ[ZMod 2] SmallOrbitSpace (Nat.card T) (Nat.card S),
      Function.Injective f ∧
      ∀ x y : Additive A,
        smallOrbitBilin (Nat.card T) (Nat.card S) (f x) (f y) = 0 := by
  classical
  obtain ⟨eT, eS, f, hf, hspec⟩ := exists_smallOrbitLinearMap hA hsmall hfaith
  refine ⟨f, hf, ?_⟩
  exact smallOrbitBilin_eq_zero_of_support_dvd_eight
    hsmall eT eS f hspec hsupport

open MulAction

public abbrev LargeOrbitIndex (A X : Type*) [Group A] [MulAction A X] :=
  {q : MulAction.orbitRel.Quotient A X // 8 ≤ Nat.card q.orbit}

public abbrev largeOrbitPoints (A X : Type*) [Group A] [MulAction A X] : Set X :=
  {x | ∃ q : LargeOrbitIndex A X, x ∈ q.1.orbit}

public abbrev largeOrbitKernel (A X : Type*) [Group A] [MulAction A X] : Subgroup A :=
  fixingSubgroup A (largeOrbitPoints A X)

public abbrev SmallOrbitComplement (A X : Type*) [Group A] [MulAction A X] :=
  SubMulAction.ofFixingSubgroup A (largeOrbitPoints A X)



public theorem largeOrbitKernel_card_le
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X] :
    Nat.card A ≤ Nat.card (largeOrbitKernel A X) *
      Nat.card ((q : LargeOrbitIndex A X) → q.1.orbit) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _
  haveI : Fintype (LargeOrbitIndex A X) := Fintype.ofFinite _
  have : ∀ q : LargeOrbitIndex A X, Fintype q.1.orbit := fun _ => Fintype.ofFinite _
  let eval : A → ((q : LargeOrbitIndex A X) → q.1.orbit) := fun a q =>
    ⟨a • Quotient.out q.1, by
      rw [MulAction.orbitRel.Quotient.mem_orbit]
      calc
        Quotient.mk'' (s₁ := MulAction.orbitRel A X)
            (a • Quotient.out q.1) =
            Quotient.mk'' (s₁ := MulAction.orbitRel A X) (Quotient.out q.1) := by
          apply Quotient.sound
          exact ⟨a, rfl⟩
        _ = q.1 := Quotient.out_eq' q.1⟩
  have hfiber : ∀ y : (q : LargeOrbitIndex A X) → q.1.orbit,
      Fintype.card {a : A // eval a = y} ≤ Nat.card (largeOrbitKernel A X) := by
    intro y
    by_cases hy : ∃ a : A, eval a = y
    · obtain ⟨a0, ha0⟩ := hy
      let g : {a : A // eval a = y} → largeOrbitKernel A X := fun a =>
        ⟨a0⁻¹ * a.1, by
          rw [mem_fixingSubgroup_iff]
          intro x hx
          rcases hx with ⟨q, hxq⟩
          have hcoord : a0 • Quotient.out q.1 = a.1 • Quotient.out q.1 := by
            exact congrArg Subtype.val (congrFun (ha0.trans a.2.symm) q)
          have hout : (a0⁻¹ * a.1) • Quotient.out q.1 = Quotient.out q.1 := by
            calc
              (a0⁻¹ * a.1) • Quotient.out q.1 =
                  a0⁻¹ • (a.1 • Quotient.out q.1) := by rw [mul_smul]
              _ = a0⁻¹ • (a0 • Quotient.out q.1) := by rw [← hcoord]
              _ = Quotient.out q.1 := by
                rw [← mul_smul, inv_mul_cancel, one_smul]
          rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q.1 Quotient.out_eq'] at hxq
          rcases hxq with ⟨c, rfl⟩
          calc
            (a0⁻¹ * a.1) • (c • Quotient.out q.1) =
                ((a0⁻¹ * a.1) * c) • Quotient.out q.1 := by rw [← mul_smul]
            _ = (c * (a0⁻¹ * a.1)) • Quotient.out q.1 := by rw [mul_comm]
            _ = c • ((a0⁻¹ * a.1) • Quotient.out q.1) := by rw [mul_smul]
            _ = c • Quotient.out q.1 := by rw [hout]⟩
      have hg : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        have hab' : a0⁻¹ * a.1 = a0⁻¹ * b.1 := congrArg Subtype.val hab
        exact mul_left_cancel hab'
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective g hg
    · have : IsEmpty {a : A // eval a = y} :=
        ⟨fun a => hy ⟨a.1, a.2⟩⟩
      simp
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := eval)
    (fun _ _ => Finset.mem_univ _) (Nat.card (largeOrbitKernel A X)) (by
      intro y hy
      rw [← Fintype.card_subtype]
      exact hfiber y)
  simpa [Nat.card_eq_fintype_card] using hcard

public theorem isElementaryAbelian_subgroup
    {G : Type*} [Group G] {p : Nat} (hG : IsElementaryAbelian G p)
    (H : Subgroup G) : IsElementaryAbelian H p := by
  constructor
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact isMulCommutative_iff.mp hG.1 a.1 b.1
  · intro h
    have horder : orderOf h = orderOf h.1 := (Subgroup.orderOf_coe h).symm
    rw [horder]
    exact hG.2 h.1

public theorem largeOrbitKernel_small_action
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    (hA : IsElementaryAbelian A 2)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X))) :
    IsElementaryAbelian (largeOrbitKernel A X) 2 ∧
    Function.Injective
      (fun b : largeOrbitKernel A X =>
        (b • · : SmallOrbitComplement A X → SmallOrbitComplement A X)) ∧
    ∀ q : MulAction.orbitRel.Quotient (largeOrbitKernel A X)
        (SmallOrbitComplement A X),
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4 := by
  classical
  have hB : IsElementaryAbelian (largeOrbitKernel A X) 2 :=
    isElementaryAbelian_subgroup hA (largeOrbitKernel A X)
  refine ⟨hB, ?_, ?_⟩
  · intro b c hbc
    apply Subtype.ext
    apply hfaith
    funext x
    by_cases hx : x ∈ largeOrbitPoints A X
    · have hbfix := ((mem_fixingSubgroup_iff A).mp b.2) x hx
      have hcfix := ((mem_fixingSubgroup_iff A).mp c.2) x hx
      change b.1 • x = c.1 • x
      rw [hbfix, hcfix]
    · let y : SmallOrbitComplement A X := ⟨x, hx⟩
      exact congrArg Subtype.val (congrFun hbc y)
  · intro q
    let y : SmallOrbitComplement A X := Quotient.out q
    let orbitMap : MulAction.orbit (largeOrbitKernel A X) y →
        MulAction.orbit A y.1 := fun z =>
      ⟨z.1.1, by
        rcases z.2 with ⟨b, hb⟩
        exact ⟨b.1, congrArg Subtype.val hb⟩⟩
    have horbitMap : Function.Injective orbitMap := by
      intro z w hzw
      have hx : (orbitMap z).1 = (orbitMap w).1 := congrArg (fun u => u.1) hzw
      have hy : z.1 = w.1 := by
        apply Subtype.ext
        exact hx
      exact Subtype.ext hy
    have hle : Nat.card (MulAction.orbit (largeOrbitKernel A X) y) ≤ Nat.card (MulAction.orbit A y.1) := by
      letI : Fintype (MulAction.orbit (largeOrbitKernel A X) y) := Fintype.ofFinite _
      letI : Fintype (MulAction.orbit A y.1) := Fintype.ofFinite _
      simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective orbitMap horbitMap
    have hlt : Nat.card (MulAction.orbit A y.1) < 8 := by
      by_contra hnot
      have hlarge : 8 ≤ Nat.card (MulAction.orbit A y.1) := by omega
      apply y.2
      let qa : MulAction.orbitRel.Quotient A X := Quotient.mk'' y.1
      refine ⟨⟨qa, ?_⟩, ?_⟩
      · simpa [qa, MulAction.orbitRel.Quotient.orbit_mk] using hlarge
      · exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    have hP : IsPGroup 2 (largeOrbitKernel A X) := ea_is_pGroup Nat.prime_two hB
    obtain ⟨e, he⟩ := hP.card_orbit y
    have hqorbit : Nat.card q.orbit = Nat.card (MulAction.orbit (largeOrbitKernel A X) y) := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    have hpowlt : 2 ^ e < 8 := by
      rw [← he]
      exact hle.trans_lt hlt
    rw [hqorbit, he]
    have he_lt : e < 3 := by
      by_contra hnot
      have he3 : 3 ≤ e := by omega
      have : 8 ≤ 2 ^ e := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) he3
      omega
    interval_cases e <;> simp

public theorem smallOrbitComplement_support_card_eq
    {A X : Type*} [Group A] [MulAction A X] [Fintype X] [DecidableEq X]
    [Fintype (SmallOrbitComplement A X)] (b : largeOrbitKernel A X) :
    ((MulAction.toPerm b : Equiv.Perm (SmallOrbitComplement A X))).support.card =
      ((MulAction.toPerm b.1 : Equiv.Perm X)).support.card := by
  classical
  let pX : Equiv.Perm X := MulAction.toPerm b.1
  let pY : Equiv.Perm (SmallOrbitComplement A X) := MulAction.toPerm b
  let e : pX.support ≃ pY.support :=
    { toFun := fun x =>
        ⟨⟨x.1, by
          intro hx
          have hfix := ((mem_fixingSubgroup_iff A).mp b.2) x.1 hx
          have hmove : pX x.1 ≠ x.1 := Equiv.Perm.mem_support.mp x.2
          exact hmove hfix⟩,
         Equiv.Perm.mem_support.mpr (by
          intro hfix
          have hmove : pX x.1 ≠ x.1 := Equiv.Perm.mem_support.mp x.2
          apply hmove
          exact congrArg Subtype.val hfix)⟩
      invFun := fun y =>
        ⟨y.1.1, Equiv.Perm.mem_support.mpr (by
          intro hfix
          have hmove : pY y.1 ≠ y.1 := Equiv.Perm.mem_support.mp y.2
          apply hmove
          apply Subtype.ext
          exact hfix)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  change pY.support.card = pX.support.card
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact (Fintype.card_congr e).symm

public theorem card_smallOrbitComplement_add_sum_largeOrbit
    {A X : Type*} [Group A] [MulAction A X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient A X)]
    [Fintype (LargeOrbitIndex A X)] :
    Nat.card (SmallOrbitComplement A X) +
      (∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit) = Fintype.card X := by
  classical
  have : ∀ q : LargeOrbitIndex A X, Fintype q.1.orbit := fun _ => Fintype.ofFinite _
  haveI : Fintype (largeOrbitPoints A X) := Fintype.ofFinite _
  haveI : Fintype (SmallOrbitComplement A X) := Fintype.ofFinite _
  let e : (Σ q : LargeOrbitIndex A X, q.1.orbit) ≃ largeOrbitPoints A X :=
    Equiv.ofBijective
      (fun z => ⟨z.2.1, ⟨z.1, z.2.2⟩⟩)
      ⟨by
        intro x y hxy
        rcases x with ⟨q, x⟩
        rcases y with ⟨r, y⟩
        have hval : x.1 = y.1 := congrArg Subtype.val hxy
        have hqr : q = r := by
          apply Subtype.ext
          calc
            q.1 = Quotient.mk'' x.1 :=
              (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm
            _ = Quotient.mk'' y.1 := by rw [hval]
            _ = r.1 := MulAction.orbitRel.Quotient.mem_orbit.mp y.2
        subst r
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext hval)),
       by
        intro x
        rcases x.2 with ⟨q, hxq⟩
        exact ⟨⟨q, ⟨x.1, hxq⟩⟩, rfl⟩⟩
  have hlarge : Fintype.card (largeOrbitPoints A X) =
      ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit := by
    calc
      Fintype.card (largeOrbitPoints A X) =
          Fintype.card (Σ q : LargeOrbitIndex A X, q.1.orbit) :=
        (Fintype.card_congr e).symm
      _ = ∑ q : LargeOrbitIndex A X, Fintype.card q.1.orbit := Fintype.card_sigma
      _ = ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Nat.card_eq_fintype_card]
  let ec : SmallOrbitComplement A X ≃ ↥((largeOrbitPoints A X)ᶜ) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hcomp : Fintype.card (SmallOrbitComplement A X) =
      Fintype.card ↥((largeOrbitPoints A X)ᶜ) := Fintype.card_congr ec
  rw [Nat.card_eq_fintype_card, hcomp, Fintype.card_compl_set, ← hlarge]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

public theorem largeOrbitProduct_card_le
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient A X)]
    [Fintype (LargeOrbitIndex A X)]
    (hA : IsElementaryAbelian A 2) :
    Nat.card ((q : LargeOrbitIndex A X) → q.1.orbit) ≤
      2 ^ (3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8) := by
  classical
  have : ∀ q : LargeOrbitIndex A X, Fintype q.1.orbit := fun _ => Fintype.ofFinite _
  have hP : IsPGroup 2 A := ea_is_pGroup Nat.prime_two hA
  let exponent : LargeOrbitIndex A X → Nat := fun q =>
    Classical.choose (hP.card_orbit (Quotient.out q.1))
  have horbit : ∀ q : LargeOrbitIndex A X,
      Nat.card q.1.orbit = 2 ^ exponent q := by
    intro q
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q.1 Quotient.out_eq']
    exact Classical.choose_spec (hP.card_orbit (Quotient.out q.1))
  have hterm : ∀ q : LargeOrbitIndex A X,
      exponent q ≤ 3 * (Nat.card q.1.orbit / 8) := by
    intro q
    have he3 : 3 ≤ exponent q := by
      by_contra hnot
      have helt : exponent q < 3 := by omega
      have hlarge := q.2
      rw [horbit q] at hlarge
      have hcases : exponent q = 0 ∨ exponent q = 1 ∨ exponent q = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · simp [h0] at hlarge
      · simp [h1] at hlarge
      · simp [h2] at hlarge
    have hpow := exponent_le_three_mul_two_pow_sub_three (exponent q) he3
    have hdiv : 2 ^ exponent q / 8 = 2 ^ (exponent q - 3) := by
      have hsplit : 2 ^ exponent q = 2 ^ (exponent q - 3) * 8 := by
        calc
          2 ^ exponent q = 2 ^ ((exponent q - 3) + 3) := by rw [Nat.sub_add_cancel he3]
          _ = 2 ^ (exponent q - 3) * 2 ^ 3 := by rw [pow_add]
          _ = 2 ^ (exponent q - 3) * 8 := by norm_num
      rw [hsplit, Nat.mul_div_left _ (by omega : 0 < 8)]
    rw [horbit q, hdiv]
    exact hpow
  have hsum : (∑ q : LargeOrbitIndex A X, exponent q) ≤
      3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8 := by
    calc
      (∑ q : LargeOrbitIndex A X, exponent q) ≤
          ∑ q : LargeOrbitIndex A X, 3 * (Nat.card q.1.orbit / 8) :=
        Finset.sum_le_sum fun q _ => hterm q
      _ = 3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8 := by
        rw [Finset.mul_sum]
  calc
    Nat.card ((q : LargeOrbitIndex A X) → q.1.orbit) =
        ∏ q : LargeOrbitIndex A X, Nat.card q.1.orbit := by
      rw [Nat.card_pi]
    _ = ∏ q : LargeOrbitIndex A X, 2 ^ exponent q := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [horbit q]
    _ = 2 ^ (∑ q : LargeOrbitIndex A X, exponent q) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 2 ^ (3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8) :=
      Nat.pow_le_pow_right (by omega) hsum



end GLS3.Chapter5.PRank
/- END Theory.PRankSmallOrbit -/

/- BEGIN Theory.A6OuterCenterThreeInversion -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement

open scoped commutatorElement

/-- Every non-inner automorphism compatible with an `A₆` covering action
inverts a nontrivial central element of order three when the covering kernel
has order three or six. -/
public theorem a6_outer_exists_center_orderThree_inverted
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3 ∨
      Nat.card f.toMonoidHom.ker = 6)
    (x : MulAut K) (hxOrder : orderOf x = 2)
    (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : K, f (x k) = β (f k))
    (hxNoninner : ∀ k : K, x ≠ MulAut.conj k)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin 6))
    (H_action_compat : ∀ h : H, ∀ k : K,
      f (h.1 k) = MulAut.conjNormal (HEquiv h) (f k)) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ x c = c⁻¹ := by
  have hβNoninner : ∀ g : alternatingGroup (Fin 6), β ≠ MulAut.conj g :=
    coveringQuotientAction_noninner_of_noninner f x β hcompat hxNoninner
  have hxPow : x ^ 2 = 1 := by
    rw [← hxOrder]
    exact pow_orderOf_eq_one x
  have hβPow : β ^ 2 = 1 := by
    apply DFunLike.ext _ _
    intro a
    obtain ⟨k, rfl⟩ := f.surjective a
    change β (β (f k)) = f k
    calc
      β (β (f k)) = β (f (x k)) := congrArg β (hcompat k).symm
      _ = f (x (x k)) := (hcompat (x k)).symm
      _ = f k := by
        have hk := congrArg (fun y : MulAut K => y k) hxPow
        simpa [pow_two] using congrArg f hk
  have hβNe : β ≠ 1 := by
    intro hβ
    exact hβNoninner 1 (by simpa using hβ)
  have hβOrder : orderOf β = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hβPow, hβNe⟩
  obtain hnormal | hnormal :=
    a6_noninner_standardNine_normalForm β hβOrder hβNoninner
  · obtain ⟨δ, hX, hY⟩ := hnormal
    obtain ⟨d, hd⟩ := f.surjective δ
    change f d = δ at hd
    let α : MulAut K := MulAut.conj d * x
    let γ : MulAut (alternatingGroup (Fin 6)) := MulAut.conj δ * β
    have hαγ : ∀ k : K, f (α k) = γ (f k) := by
      intro k
      change f (d * x k * d⁻¹) = δ * β (f k) * δ⁻¹
      rw [map_mul, map_inv, map_mul, hd, hcompat]
    have hwitness : ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
        c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ α c = c⁻¹ := by
      rcases hker with hker | hker
      · obtain ⟨u, v, _hu, _hv, hcKer, hcNe, hcCenter, hcPow, _⟩ :=
          exists_a6StandardNine_lifts_commutator f hker
        have hαc := tripleCoverA6_kernel_inverted_of_standardNine_reflection
          f hker α γ hαγ hX hY ⁅u, v⁆ hcKer
        exact ⟨⁅u, v⁆, hcKer, hcNe, hcCenter, hcPow,
          orderOf_eq_prime_iff.mpr ⟨hcPow, hcNe⟩, hαc⟩
      · exact sixCoverA6_exists_center_orderThree_inverted_of_reflection
          f hker α γ hαγ hX hY
    obtain ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder, hαc⟩ := hwitness
    have hxcCenter : x c ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := x.surjective g
      simpa [map_mul] using congrArg x (Subgroup.mem_center_iff.mp hcCenter g)
    have hαcEq : α c = x c := by
      dsimp [α]
      have hcomm : Commute d (x c) :=
        Subgroup.mem_center_iff.mp hxcCenter d
      rw [hcomm.eq, mul_inv_cancel_right]
    exact ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder,
      hαcEq.symm.trans hαc⟩
  · obtain ⟨τ, δ, hX, hY⟩ := hnormal
    let h : H := HEquiv.symm τ
    have hτ : HEquiv h = τ := HEquiv.apply_symm_apply τ
    let α₀ : MulAut K := h.1⁻¹ * x * h.1
    let β₀ : MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.conjNormal τ)⁻¹ * β * MulAut.conjNormal τ
    have hα₀β₀ : ∀ k : K, f (α₀ k) = β₀ (f k) := by
      intro k
      change f (h.1⁻¹ (x (h.1 k))) = β₀ (f k)
      calc
        f (h.1⁻¹ (x (h.1 k))) =
            (MulAut.conjNormal (HEquiv h))⁻¹ (f (x (h.1 k))) := by
          have hhinv := H_action_compat h (h.1⁻¹ (x (h.1 k)))
          calc
            f (h.1⁻¹ (x (h.1 k))) =
                (MulAut.conjNormal (HEquiv h))⁻¹
                  (MulAut.conjNormal (HEquiv h)
                    (f (h.1⁻¹ (x (h.1 k))))) := by simp
            _ = (MulAut.conjNormal (HEquiv h))⁻¹
                  (f (h.1 (h.1⁻¹ (x (h.1 k))))) := by rw [hhinv]
            _ = (MulAut.conjNormal (HEquiv h))⁻¹ (f (x (h.1 k))) := by simp
        _ = (MulAut.conjNormal (HEquiv h))⁻¹ (β (f (h.1 k))) := by
          rw [hcompat]
        _ = β₀ (f k) := by
          rw [H_action_compat, hτ]
          simp only [β₀, MulAut.mul_apply, MulAut.inv_apply]
    obtain ⟨d, hd⟩ := f.surjective δ
    change f d = δ at hd
    let α : MulAut K := MulAut.conj d * α₀
    let γ : MulAut (alternatingGroup (Fin 6)) := MulAut.conj δ * β₀
    have hαγ : ∀ k : K, f (α k) = γ (f k) := by
      intro k
      change f (d * α₀ k * d⁻¹) = δ * β₀ (f k) * δ⁻¹
      rw [map_mul, map_inv, map_mul, hd, hα₀β₀]
    have hwitness : ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
        c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ α c = c⁻¹ := by
      rcases hker with hker | hker
      · obtain ⟨u, v, _hu, _hv, hcKer, hcNe, hcCenter, hcPow, _⟩ :=
          exists_a6StandardNine_lifts_commutator f hker
        have hαc := tripleCoverA6_kernel_inverted_of_standardNine_matrix
          f hker α γ hαγ hX hY ⁅u, v⁆ hcKer
        exact ⟨⁅u, v⁆, hcKer, hcNe, hcCenter, hcPow,
          orderOf_eq_prime_iff.mpr ⟨hcPow, hcNe⟩, hαc⟩
      · exact sixCoverA6_exists_center_orderThree_inverted_of_matrix
          f hker α γ hαγ hX hY
    obtain ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder, hαc⟩ := hwitness
    have hα₀cCenter : α₀ c ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := α₀.surjective g
      simpa [map_mul] using congrArg α₀ (Subgroup.mem_center_iff.mp hcCenter g)
    have hαcEq : α c = α₀ c := by
      dsimp [α]
      have hcomm : Commute d (α₀ c) :=
        Subgroup.mem_center_iff.mp hα₀cCenter d
      rw [hcomm.eq, mul_inv_cancel_right]
    have hα₀c : α₀ c = c⁻¹ := hαcEq.symm.trans hαc
    let c' : K := h.1 c
    have hc'Center : c' ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := h.1.surjective g
      simpa [c', map_mul] using congrArg h.1
        (Subgroup.mem_center_iff.mp hcCenter g)
    have hfker : f.toMonoidHom.ker = Subgroup.center K := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by norm_num)
      exact f.ker_eq_center_of_isSimple
    have hc'Ker : c' ∈ f.toMonoidHom.ker := by
      rw [hfker]
      exact hc'Center
    have hc'Ne : c' ≠ 1 := by
      intro hc'
      apply hcNe
      exact h.1.injective (by simpa [c'] using hc')
    have hc'Pow : c' ^ 3 = 1 := by
      dsimp [c']
      rw [← map_pow, hcPow, map_one]
    have hc'Order : orderOf c' = 3 :=
      orderOf_eq_prime_iff.mpr ⟨hc'Pow, hc'Ne⟩
    have hxc' : x c' = c'⁻¹ := by
      have hback := congrArg h.1 hα₀c
      simpa [α₀, c', map_inv] using hback
    exact ⟨c', hc'Ker, hc'Ne, hc'Center, hc'Pow, hc'Order, hxc'⟩

end GLS3.Chapter5
/- END Theory.A6OuterCenterThreeInversion -/

/- BEGIN Theory.AlternatingCenterCardDvdTwoOfNonexceptional -/
noncomputable section

namespace GLS3.Chapter5

public theorem alternating_center_card_dvd_two_of_nonexceptional
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n) (h6 : n ≠ 6) (h7 : n ≠ 7)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Nat.card (Subgroup.center K) ∣ 2 := by
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let : IsQuasisimple (alternatingGroup (Fin n)) := by
    rw [← hq]
    exact SchurPresentation.alternatingGroup_isQuasisimple q
  obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
  have hq6 : q + 5 ≠ 6 := by simpa [hq] using h6
  have hq7 : q + 5 ≠ 7 := by simpa [hq] using h7
  let ef : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := ef.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective }
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom
        eA.injective]
  have hkernel := Covering.coveringKernel_card_dvd_of_universal
    (SchurPresentation.schurAlternatingCovering q)
    (SchurPresentation.theorem_5_2_3_b_universality q hq6 hq7) c
  rw [SchurPresentation.theorem_5_2_3_a q] at hkernel
  rw [← hfker, ← hf'ker]
  simpa [c] using hkernel

end GLS3.Chapter5
/- END Theory.AlternatingCenterCardDvdTwoOfNonexceptional -/

/- BEGIN Theory.ThreePrimaryExceptionalCenterCard -/
noncomputable section

namespace GLS3.Chapter5

/-- In either exceptional alternating degree, a nontrivial three-primary
center has order exactly three. -/
public theorem three_primary_exceptional_center_card_eq_three
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hnExceptional : n = 6 ∨ n = 7)
    (hcenterP : IsPGroup 3 (Subgroup.center K))
    (hthree : 3 ∣ Nat.card (Subgroup.center K)) :
    Nat.card (Subgroup.center K) = 3 := by
  have hdiv6 := exceptional_alternating_center_card_dvd_six n e hnExceptional
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hcenterP
  have hcoprime : (Nat.card (Subgroup.center K)).Coprime 2 := by
    rw [hr]
    exact Nat.Coprime.pow_left r (by norm_num)
  have hdiv3 : Nat.card (Subgroup.center K) ∣ 3 := by
    apply hcoprime.dvd_of_dvd_mul_left
    simpa using hdiv6
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with hone | hthreeCard
  · rw [hone] at hthree
    norm_num at hthree
  · exact hthreeCard

end GLS3.Chapter5
/- END Theory.ThreePrimaryExceptionalCenterCard -/

/- BEGIN Theory.TwoPrimaryAlternatingCenterCard -/
noncomputable section

namespace GLS3.Chapter5

/-- A nontrivial two-primary center of a quasisimple alternating cover has
order exactly two. -/
public theorem two_primary_alternating_center_card_eq_two
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hcenterP : IsPGroup 2 (Subgroup.center K))
    (htwo : 2 ∣ Nat.card (Subgroup.center K)) :
    Nat.card (Subgroup.center K) = 2 := by
  have hdiv2 : Nat.card (Subgroup.center K) ∣ 2 := by
    by_cases hnExceptional : n = 6 ∨ n = 7
    · have hdiv6 := exceptional_alternating_center_card_dvd_six n e hnExceptional
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hcenterP
      have hcoprime : (Nat.card (Subgroup.center K)).Coprime 3 := by
        rw [hr]
        exact Nat.Coprime.pow_left r (by norm_num)
      apply hcoprime.dvd_of_dvd_mul_right
      norm_num
      exact hdiv6
    · let q := n - 5
      have hq : q + 5 = n := Nat.sub_add_cancel hn
      let : IsQuasisimple (alternatingGroup (Fin n)) := by
        rw [← hq]
        exact SchurPresentation.alternatingGroup_isQuasisimple q
      obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
      have h6 : n ≠ 6 := fun hn6 => hnExceptional (Or.inl hn6)
      have h7 : n ≠ 7 := fun hn7 => hnExceptional (Or.inr hn7)
      have hq6 : q + 5 ≠ 6 := by simpa [hq] using h6
      have hq7 : q + 5 ≠ 7 := by simpa [hq] using h7
      let ef : Fin (q + 5) ≃ Fin n := finCongr hq
      let eA := ef.symm.altCongrHom
      let f' : K →* alternatingGroup (Fin (q + 5)) :=
        eA.toMonoidHom.comp f.toMonoidHom
      have hf'ker : f'.ker = f.toMonoidHom.ker := by
        rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
          MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
      let c : Covering K (alternatingGroup (Fin (q + 5))) := {
        toMonoidHom := f'
        surjective := eA.surjective.comp f.surjective
      }
      have hkernel := Covering.coveringKernel_card_dvd_of_universal
        (SchurPresentation.schurAlternatingCovering q)
        (SchurPresentation.theorem_5_2_3_b_universality q hq6 hq7) c
      rw [SchurPresentation.theorem_5_2_3_a q] at hkernel
      rw [← hfker, ← hf'ker]
      simpa [c] using hkernel
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with hone | htwoCard
  · rw [hone] at htwo
    norm_num at htwo
  · exact htwoCard

end GLS3.Chapter5
/- END Theory.TwoPrimaryAlternatingCenterCard -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_9 -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5

/-!
Infrastructure for Proposition 5.2.9.

The component-classification and center conclusions are not declared as
theorems until their source-specific proofs are available. Earlier versions
put exactly those conclusions in a private record backed by a placeholder;
that did not constitute a proof of Proposition 5.2.9.
-/

/-- A component of `C`: a quasisimple subgroup which is subnormal in `C`. -/
@[expose]
public def IsComponentOf {G : Type*} [Group G]
    (I C : Subgroup G) : Prop :=
  I ≤ C ∧ (I.subgroupOf C).IsSubnormal ∧ IsQuasisimple I

/-- A concrete `p`-component interface: `I` is perfect and subnormal in `C`,
and quotienting by a central `p`-core gives a quasisimple group. -/
@[expose]
public def IsPComponentOf {G : Type*} [Group G]
    (p : Nat) (I C : Subgroup G) : Prop :=
  I ≤ C ∧
    (I.subgroupOf C).IsSubnormal ∧
    _root_.commutator I = ⊤ ∧
    ∃ O : Subgroup I,
      ∃ hO : O.Normal,
        IsPCore p O ∧ O ≤ Subgroup.center I ∧
          @IsQuasisimple (I ⧸ O)
            (@QuotientGroup.Quotient.group I inferInstance O hO)

/-- The layer `E(C)`, defined as the subgroup generated by all components of
`C`. -/
@[expose]
public def componentLayer {G : Type*} [Group G]
    (C : Subgroup G) : Subgroup G :=
  sSup {I : Subgroup G | IsComponentOf I C}

/-- Membership in the alternating quasisimple family used in Section 5.2. -/
@[expose]
public def IsAlternatingQuasisimple {G : Type*} [Group G] [Finite G]
    (I : Subgroup G) : Prop :=
  IsQuasisimple I ∧ IsInAlt I

/-- The largest normal `p`-subgroup contained in `H`. For `H = Z(G)` this is
the subgroup denoted `O_p(Z)` in the printed proposition. -/
@[expose]
public def pCoreSubgroup {G : Type*} [Group G]
    (p : Nat) (H : Subgroup G) : Subgroup G :=
  sSup {P : Subgroup G | P ≤ H ∧ P.Normal ∧ IsPGroup p P}

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.proposition_5_2_9 -/

/- BEGIN Theory.proposition_5_2_7_c -/
set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

noncomputable section

namespace GLS3.Chapter5

private theorem __ch5_proposition_5_2_7_c_center_card_three_or_six
    {K : Type} [Group K] [Finite K]
    (O3 : Subgroup K)
    (hO3center : O3 ≤ Subgroup.center K)
    (hcenterDvd : Nat.card (Subgroup.center K) ∣ 6)
    (hO3card : Nat.card O3 = 3) :
    Nat.card (Subgroup.center K) = 3 ∨ Nat.card (Subgroup.center K) = 6 := by
  have h3dvd : 3 ∣ Nat.card (Subgroup.center K) := by
    rw [← hO3card]
    exact Subgroup.card_dvd_of_le hO3center
  have hpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
  have hle : Nat.card (Subgroup.center K) ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hcenterDvd
  interval_cases hcard : Nat.card (Subgroup.center K)
  · exfalso
    norm_num [hcard] at h3dvd
  · exfalso
    norm_num [hcard] at h3dvd
  · exact Or.inl rfl
  · exfalso
    norm_num [hcard] at h3dvd
  · exfalso
    norm_num [hcard] at h3dvd
  · exact Or.inr rfl

private theorem __ch5_proposition_5_2_7_c_pCore_order_three_inverted
    {K : Type} [Group K] [Finite K]
    (O3 : Subgroup K)
    (hO3card : Nat.card O3 = 3)
    (x : MulAut K) (hmap : O3.map x.toMonoidHom = O3)
    (hc : ∃ c : O3, x c.1 ≠ c.1) :
    ∀ z : O3, x z.1 = z.1⁻¹ := by
  apply inverts_order_three_subgroup_of_not_pointwise_fixed O3 x hmap hO3card
  intro hfixed
  rcases hc with ⟨c, hc⟩
  exact hc (hfixed c)

private theorem __ch5_proposition_5_2_7_c_center_order_three_mem_pCore
    {K : Type} [Group K] [Finite K]
    (O3 : Subgroup K) (hO3 : IsPCore 3 O3)
    (c : K) (hcCenter : c ∈ Subgroup.center K)
    (hcOrder : orderOf c = 3) : c ∈ O3 := by
  let P : Subgroup K := Subgroup.zpowers c
  have hPcenter : P ≤ Subgroup.center K := by
    exact Subgroup.zpowers_le_of_mem hcCenter
  have hPnormal : P.Normal := by
    constructor
    intro g hn n
    have hcomm : Commute n g :=
      Subgroup.mem_center_iff.mp (hPcenter hn) n
    rw [hcomm.eq, mul_inv_cancel_right]
    exact hn
  have hPgroup : IsPGroup 3 P := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [P, Nat.card_zpowers, hcOrder]
  have hPle : P ≤ O3 := hO3.maximal P hPnormal hPgroup
  exact hPle (Subgroup.mem_zpowers c)

private theorem __ch5_proposition_5_2_7_c_exceptional_outer_exists_center_orderThree_inverted
    {K : Type} {n : Nat} [Group K] [Finite K] [IsQuasisimple K]
    [IsQuasisimple (alternatingGroup (Fin n))]
    (hn6 : n = 6 ∨ n = 7)
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 3 ∨
      Nat.card f.toMonoidHom.ker = 6)
    (x : MulAut K) (hxOrder : orderOf x = 2)
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (hcompat : ∀ k : K, f (x k) = quotientAction (f k))
    (hxNoninner : ∀ k : K, x ≠ MulAut.conj k)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin n))
    (H_action_compat : ∀ h : H, ∀ k : K,
      f (h.1 k) = MulAut.conjNormal (HEquiv h) (f k)) :
    ∃ c : K, c ∈ f.toMonoidHom.ker ∧ c ≠ 1 ∧
      c ∈ Subgroup.center K ∧ c ^ 3 = 1 ∧ orderOf c = 3 ∧ x c = c⁻¹ := by
  rcases hn6 with rfl | rfl
  · exact a6_outer_exists_center_orderThree_inverted f hker x hxOrder
      quotientAction hcompat hxNoninner H HEquiv H_action_compat
  · exact a7_outer_exists_center_orderThree_inverted f hker x
      quotientAction hcompat hxNoninner

public theorem proposition_5_2_7_c
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn5 : 5 ≤ n) (hpPrime : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hxOrder : orderOf x = p)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin n))
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hxNoninner : ∀ k : K, x ≠ MulAut.conj k)
    (hn6 : n = 6 ∨ n = 7) (hp2 : p = 2)
    (O3 : Subgroup K) (hO3 : IsPCore 3 O3) :
    ∀ z : O3, x z.1 = z.1⁻¹ := by
  subst p
  have hO3center : O3 ≤ Subgroup.center K := by
    exact pCore_le_center_of_exceptional_alternating_quotient n hn5
      quotientEquiv hn6 O3 hO3
  have hcenterDvd := exceptional_alternating_center_card_dvd_six n
    quotientEquiv hn6
  let : IsQuasisimple (alternatingGroup (Fin n)) := by
    have hn : n - 5 + 5 = n := by omega
    rw [← hn]
    exact SchurPresentation.alternatingGroup_isQuasisimple (n - 5)
  obtain hO3one | hO3three := pCore_card_eq_one_or_three O3 hO3.isPGroup
    hO3center hcenterDvd
  · have hbot : O3 = ⊥ := Subgroup.card_eq_one.mp hO3one
    intro z
    have hz : z.1 = 1 := by simpa [hbot] using z.2
    simp [hz]
  · have hmap : O3.map x.toMonoidHom = O3 :=
      pCore_map_eq 3 O3 hO3 x
    have hcenterThreeOrSix : Nat.card (Subgroup.center K) = 3 ∨
        Nat.card (Subgroup.center K) = 6 :=
      __ch5_proposition_5_2_7_c_center_card_three_or_six O3 hO3center hcenterDvd hO3three
    let f : Covering K (alternatingGroup (Fin n)) := {
      toMonoidHom := alternatingQuotientHom quotientEquiv
      surjective := quotientEquiv.surjective.comp
        (QuotientGroup.mk'_surjective (Subgroup.center K)) }
    have hfker : f.toMonoidHom.ker = Subgroup.center K := by
      ext k
      simp [f, alternatingQuotientHom]
    have hker : Nat.card f.toMonoidHom.ker = 3 ∨
        Nat.card f.toMonoidHom.ker = 6 := by
      rw [hfker]
      exact hcenterThreeOrSix
    have hcompat : ∀ k : K, f (x k) = quotientAction (f k) := by
      intro k
      exact quotientAction_compat k
    obtain ⟨c, hcKer, hcNe, hcCenter, hcPow, hcOrder, hxc⟩ :=
      __ch5_proposition_5_2_7_c_exceptional_outer_exists_center_orderThree_inverted hn6 f hker x hp2
        quotientAction hcompat hxNoninner H HEquiv H_action_compat
    have hcO3 : c ∈ O3 :=
      __ch5_proposition_5_2_7_c_center_order_three_mem_pCore O3 hO3 c hcCenter hcOrder
    have hcInvNe : c⁻¹ ≠ c := by
      intro hcInv
      have hcSq : c ^ 2 = 1 := by
        rw [pow_two]
        calc
          c * c = c⁻¹ * c := by rw [hcInv]
          _ = 1 := inv_mul_cancel c
      have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hcSq
      rw [hcOrder] at hdvd
      norm_num at hdvd
    have hnontrivial : ∃ c : O3, x c.1 ≠ c.1 :=
      ⟨⟨c, hcO3⟩, fun hfixed => hcInvNe (hxc.symm.trans hfixed)⟩
    exact __ch5_proposition_5_2_7_c_pCore_order_three_inverted O3 hO3three x hmap
      hnontrivial

end GLS3.Chapter5
/- END Theory.proposition_5_2_7_c -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_10 -/
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

noncomputable section

namespace GLS3.Chapter5

/-! ## Infrastructure for Proposition 5.2.10

For `K = A_Ω` and odd `p`, this module proves that every elementary abelian
`p`-subgroup has order at most `p^(⌊n/p⌋)`. The proof uses the orbit
decomposition of the action on the point set: each orbit contributes at most
its size divided by `p` to the rank. The matching lower bound and the other
exact-rank clauses of Proposition 5.2.10 are not declared until proved.
-/

namespace PRank
open GLS3.Chapter5.SchurPresentation
open SchurPresentation

public theorem exists_regularEightTranslationSubgroup : ∃ A : Subgroup (alternatingGroup (Fin 3 → ZMod 2)),
    IsElementaryAbelian A 2 ∧ Nat.card A = 8 ∧
      ∀ x : A, x ≠ 1 → ∀ omega, x.1.1 omega ≠ omega := by
  let V := Fin 3 → ZMod 2
  let transHom : Multiplicative V →* Equiv.Perm V := {
    toFun := fun a => AddAction.toPerm a.toAdd
    map_one' := by
      ext x
      simp [AddAction.toPerm_apply]
    map_mul' := by
      intro a b
      ext x
      simp [AddAction.toPerm_apply, add_assoc] }
  have htransInjective : Function.Injective transHom := by
    intro a b h
    change a.toAdd = b.toAdd
    exact AddAction.toPerm_injective h
  have htransSq : ∀ a : Multiplicative V, a ^ 2 = 1 := by
    intro a
    rw [pow_two]
    change a.toAdd + a.toAdd = (0 : V)
    funext i
    have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    calc
      a.toAdd i + a.toAdd i = (2 : ZMod 2) * a.toAdd i := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have htransSign : ∀ a : Multiplicative V, Equiv.Perm.sign (transHom a) = 1 := by
    intro a
    by_cases ha : a = 1
    · simp [ha]
    · have ha0 : a.toAdd ≠ 0 := by simpa using ha
      have hsquare : (transHom a) ^ 2 = 1 := by
        rw [← map_pow, htransSq, map_one]
      rw [Equiv.Perm.sign_of_pow_two_eq_one hsquare]
      have hnotfixed : ∀ x : V, transHom a x ≠ x := by
        intro x hx
        have hax : a.toAdd + x = x := by
          simpa [transHom, AddAction.toPerm_apply] using hx
        exact ha0 (add_right_cancel (show a.toAdd + x = 0 + x by simpa using hax))
      have hfixedcard : Fintype.card (Function.fixedPoints (transHom a)) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun x => (hnotfixed x.1 x.2).elim⟩
      rw [hfixedcard]
      norm_num [V]
  let altTransHom : Multiplicative V →* alternatingGroup V :=
    transHom.codRestrict (alternatingGroup V) (fun a =>
      Equiv.Perm.mem_alternatingGroup.mpr (htransSign a))
  have haltInjective : Function.Injective altTransHom := by
    intro a b h
    apply htransInjective
    exact congrArg Subtype.val h
  let A : Subgroup (alternatingGroup V) := altTransHom.range
  have hdomainEA : IsElementaryAbelian (Multiplicative V) 2 := by
    constructor
    · exact inferInstance
    · intro a
      by_cases ha : a = 1
      · left
        exact orderOf_eq_one_iff.mpr ha
      · right
        exact orderOf_eq_prime (htransSq a) ha
  have htopEA : IsElementaryAbelian (⊤ : Subgroup (Multiplicative V)) 2 := by
    constructor
    · exact inferInstance
    · intro a
      simpa using hdomainEA.2 a.1
  have hAea : IsElementaryAbelian A 2 := by
    change IsElementaryAbelian altTransHom.range 2
    rw [MonoidHom.range_eq_map]
    exact isElementaryAbelian_map_of_injective 2 ⊤ htopEA
      altTransHom haltInjective
  have hAcard : Nat.card A = 8 := by
    change Nat.card altTransHom.range = 8
    rw [← Nat.card_congr (MonoidHom.ofInjective haltInjective).toEquiv]
    change Nat.card V = 8
    rw [Nat.card_pi]
    norm_num
  refine ⟨A, hAea, hAcard, ?_⟩
  intro x hx omega hfix
  rcases x.2 with ⟨a, ha⟩
  have ha1 : a ≠ 1 := by
    intro haone
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    simpa [haone] using (congrArg Subtype.val ha).symm
  have ha0 : a.toAdd ≠ 0 := by simpa using ha1
  have hax : a.toAdd + omega = omega := by
    have hval := congrArg Subtype.val ha
    change altTransHom a = x.1 at ha
    have : transHom a omega = x.1.1 omega := by
      rw [← hval]
      rfl
    rw [← this] at hfix
    simpa [transHom, AddAction.toPerm_apply] using hfix
  exact ha0 (add_right_cancel (show a.toAdd + omega = 0 + omega by simpa using hax))

public theorem exists_regularEightSubgroup_fin : ∃ A : Subgroup (alternatingGroup (Fin 8)),
    IsElementaryAbelian A 2 ∧ Nat.card A = 8 ∧
      ∀ x : A, x ≠ 1 → ∀ omega, x.1.1 omega ≠ omega := by
  obtain ⟨B, hB, hBcard, hBreg⟩ := exists_regularEightTranslationSubgroup
  let V := Fin 3 → ZMod 2
  have hVcard : Fintype.card V = 8 := by
    change Fintype.card ((i : Fin 3) → ZMod 2) = 8
    rw [Fintype.card_pi]
    norm_num
  let e : V ≃ Fin 8 := (Fintype.equivFin V).trans (finCongr hVcard)
  let f : alternatingGroup V →* alternatingGroup (Fin 8) := e.altCongrHom.toMonoidHom
  let A : Subgroup (alternatingGroup (Fin 8)) := B.map f
  have hf : Function.Injective f := e.altCongrHom.injective
  refine ⟨A, isElementaryAbelian_map_of_injective 2 B hB f hf, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := B) (f := f) hf]
    exact hBcard
  · intro x hx omega hfix
    rcases x.2 with ⟨b, hb, hbx⟩
    have hb1 : b ≠ 1 := by
      intro hbOne
      apply hx
      apply Subtype.ext
      have hval := congrArg Subtype.val hbx
      simpa [hbOne] using hval.symm
    have hmove := hBreg ⟨b, hb⟩ (by
      intro hbone
      apply hb1
      exact congrArg Subtype.val hbone) (e.symm omega)
    apply hmove
    have hval := congrArg Subtype.val hbx
    have happ := DFunLike.congr_fun hval omega
    change e (b.1 (e.symm omega)) = x.1.1 omega at happ
    apply e.injective
    rw [happ, hfix]
    exact (e.apply_symm_apply omega).symm

public theorem exists_regularEightFirstBlockSubgroup (b : Nat) : ∃ A : Subgroup (alternatingGroup (Fin (8 + b))),
    IsElementaryAbelian A 2 ∧ Nat.card A = 8 ∧
      ∀ x : A, x ≠ 1 → ∀ omega,
        (∃ y : A, y.1.1 omega ≠ omega) → x.1.1 omega ≠ omega := by
  obtain ⟨B, hB, hBcard, hBreg⟩ := exists_regularEightSubgroup_fin
  let f : alternatingGroup (Fin 8) →* alternatingGroup (Fin (8 + b)) :=
    (alternatingProdBlockHom 8 b).comp
      (MonoidHom.inl (alternatingGroup (Fin 8)) (alternatingGroup (Fin b)))
  have hf : Function.Injective f := by
    intro x y hxy
    have hpair := alternatingProdBlockHom_injective 8 b hxy
    exact congrArg Prod.fst hpair
  let A : Subgroup (alternatingGroup (Fin (8 + b))) := B.map f
  refine ⟨A, isElementaryAbelian_map_of_injective 2 B hB f hf, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := B) (f := f) hf]
    exact hBcard
  · intro x hx omega hmoved hfix
    rcases x.2 with ⟨a, haB, hax⟩
    have ha1 : a ≠ 1 := by
      intro haone
      apply hx
      apply Subtype.ext
      have hval := congrArg Subtype.val hax
      simpa [haone] using hval.symm
    let u := finSumFinEquiv.symm omega
    cases hu : u with
    | inl i =>
        have hamove := hBreg ⟨a, haB⟩ (by
          intro h
          apply ha1
          exact congrArg Subtype.val h) i
        apply hamove
        have hval := congrArg Subtype.val hax
        have happ := DFunLike.congr_fun hval omega
        have happ' : finSumFinEquiv (Sum.inl (a.1 i)) = x.1.1 omega := by
          simpa [f, coe_alternatingProdBlockHom_apply, permProdBlockHom_apply,
            Equiv.permCongr_apply,
            show finSumFinEquiv.symm omega = Sum.inl i by simpa [u] using hu]
            using happ
        apply Sum.inl_injective
        apply finSumFinEquiv.injective
        rw [happ', hfix]
        exact (finSumFinEquiv.apply_symm_apply omega).symm.trans
          (congrArg finSumFinEquiv
            (show finSumFinEquiv.symm omega = Sum.inl i by simpa [u] using hu))
    | inr j =>
        rcases hmoved with ⟨y, hymove⟩
        rcases y.2 with ⟨c, hcB, hcy⟩
        apply hymove
        have hval := congrArg Subtype.val hcy
        have happ := DFunLike.congr_fun hval omega
        have hright : finSumFinEquiv (Sum.inr j) = y.1.1 omega := by
          simpa [f, coe_alternatingProdBlockHom_apply, permProdBlockHom_apply,
            Equiv.permCongr_apply,
            show finSumFinEquiv.symm omega = Sum.inr j by simpa [u] using hu]
            using happ
        rw [← hright]
        exact ((finSumFinEquiv.apply_symm_apply omega).symm.trans
          (congrArg finSumFinEquiv
            (show finSumFinEquiv.symm omega = Sum.inr j by simpa [u] using hu))).symm

public theorem exists_regularEightBlockProductSubgroup (r : Nat) :
    ∃ A : Subgroup (alternatingGroup (Fin (r * 8))),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (3 * r) ∧
      ∀ x : A, x ≠ 1 → 8 ∣ x.1.1.support.card := by
  let V := Fin 3 → ZMod 2
  let W := Fin r → V
  let transPerm : Multiplicative W → Equiv.Perm (Fin r × V) := fun a => {
    toFun := fun q => (q.1, a.toAdd q.1 + q.2)
    invFun := fun q => (q.1, -a.toAdd q.1 + q.2)
    left_inv := by
      rintro ⟨i, x⟩
      apply Prod.ext
      · rfl
      · funext j
        change -a.toAdd i j + (a.toAdd i j + x j) = x j
        rw [← add_assoc, neg_add_cancel, zero_add]
    right_inv := by
      rintro ⟨i, x⟩
      apply Prod.ext
      · rfl
      · funext j
        change a.toAdd i j + (-a.toAdd i j + x j) = x j
        rw [← add_assoc, add_neg_cancel, zero_add] }
  have htransMul : ∀ a b : Multiplicative W,
      transPerm (a * b) = transPerm a * transPerm b := by
    intro a b
    apply Equiv.ext
    intro q
    apply Prod.ext
    · rfl
    · funext j
      change (a.toAdd q.1 j + b.toAdd q.1 j) + q.2 j =
        a.toAdd q.1 j + (b.toAdd q.1 j + q.2 j)
      rw [add_assoc]
  let transHom : Multiplicative W →* Equiv.Perm (Fin r × V) := {
    toFun := transPerm
    map_one' := by
      apply Equiv.ext
      intro q
      apply Prod.ext
      · rfl
      · funext j
        change (0 : ZMod 2) + q.2 j = q.2 j
        rw [zero_add]
    map_mul' := htransMul }
  have htransInjective : Function.Injective transHom := by
    intro a b h
    change a.toAdd = b.toAdd
    funext i
    have hi := congrArg (fun σ : Equiv.Perm (Fin r × V) => σ (i, 0)) h
    simpa [transHom, transPerm] using congrArg Prod.snd hi
  have hsq : ∀ a : Multiplicative W, a ^ 2 = 1 := by
    intro a
    rw [pow_two]
    change a.toAdd + a.toAdd = (0 : W)
    funext i j
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      a.toAdd i j + a.toAdd i j = (2 : ZMod 2) * a.toAdd i j := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hsupport : ∀ a : Multiplicative W,
      8 ∣ (transHom a).support.card := by
    intro a
    let I := {i : Fin r // a.toAdd i ≠ 0}
    let e : ↥(transHom a).support ≃ I × V := {
      toFun := fun q =>
        (⟨q.1.1, by
          intro hai
          have hfix : transHom a q.1 = q.1 := by
            apply Prod.ext
            · rfl
            · simp [transHom, transPerm, hai]
          exact (Equiv.Perm.mem_support.mp q.2) hfix⟩, q.1.2)
      invFun := fun q =>
        ⟨(q.1.1, q.2), Equiv.Perm.mem_support.mpr (by
          intro hfix
          have hsnd := congrArg Prod.snd hfix
          simp [transHom, transPerm] at hsnd
          exact q.1.2 (add_right_cancel (show a.toAdd q.1.1 + q.2 = 0 + q.2 by simpa using hsnd)))⟩
      left_inv := by intro q; apply Subtype.ext; rfl
      right_inv := by intro q; rfl }
    have hc : (transHom a).support.card = Nat.card I * 8 := by
      rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_prod]
      rw [Nat.card_eq_fintype_card]
      simp [V]
    rw [hc]
    exact ⟨Nat.card I, by omega⟩
  have hsign : ∀ a : Multiplicative W, Equiv.Perm.sign (transHom a) = 1 := by
    intro a
    have hsquare : (transHom a) ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
    rw [Equiv.Perm.sign_of_pow_two_eq_one hsquare]
    have hfixed : Fintype.card (Function.fixedPoints (transHom a)) =
        Fintype.card (Fin r × V) - (transHom a).support.card := by
      rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
    rw [hfixed]
    obtain ⟨k, hk⟩ := hsupport a
    rw [Nat.sub_sub_self (Finset.card_le_univ (transHom a).support), hk]
    have hdiv : 8 * k / 2 = 4 * k := by omega
    rw [hdiv, pow_mul]
    rw [show (-1 : ℤˣ) ^ 4 = 1 by decide, one_pow]
  let altHom : Multiplicative W →* alternatingGroup (Fin r × V) :=
    transHom.codRestrict _ fun a => Equiv.Perm.mem_alternatingGroup.mpr (hsign a)
  let e0 : (Fin r × V) ≃ Fin (r * 8) := by
    apply Fintype.equivOfCardEq
    simp [V]
  let f : Multiplicative W →* alternatingGroup (Fin (r * 8)) :=
    e0.altCongrHom.toMonoidHom.comp altHom
  have hf : Function.Injective f := e0.altCongrHom.injective.comp (fun a b h =>
    htransInjective (congrArg Subtype.val h))
  let A : Subgroup (alternatingGroup (Fin (r * 8))) := f.range
  have hdomain : IsElementaryAbelian (Multiplicative W) 2 := by
    constructor
    · infer_instance
    · intro a
      by_cases ha : a = 1
      · exact Or.inl (orderOf_eq_one_iff.mpr ha)
      · exact Or.inr (orderOf_eq_prime (hsq a) ha)
  have hA : IsElementaryAbelian A 2 := by
    change IsElementaryAbelian f.range 2
    rw [MonoidHom.range_eq_map]
    have htop : IsElementaryAbelian (⊤ : Subgroup (Multiplicative W)) 2 := by
      constructor
      · infer_instance
      · intro a
        simpa using hdomain.2 a.1
    exact isElementaryAbelian_map_of_injective 2 ⊤ htop f hf
  refine ⟨A, hA, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    change Nat.card W = 2 ^ (3 * r)
    rw [Nat.card_pi]
    have hV : Nat.card V = 8 := by simp [V]
    simp_rw [hV]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← pow_mul]
  · intro x hx
    rcases x.2 with ⟨a, ha⟩
    have hs := hsupport a
    have hcard : x.1.1.support.card = (transHom a).support.card := by
      have hval := congrArg Subtype.val ha
      change e0.permCongr (transHom a) = x.1.1 at hval
      rw [← hval]
      have hsupp : (e0.permCongr (transHom a)).support =
          (transHom a).support.map e0.toEmbedding := by
        ext y
        obtain ⟨z, rfl⟩ := e0.surjective y
        simp [Equiv.Perm.mem_support]
      rw [hsupp, Finset.card_map]
    rwa [hcard]

public theorem exists_regularEightBlockProductSubgroup_of_mul_le (n r : Nat) (hr : r * 8 ≤ n) :
    ∃ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (3 * r) ∧
      ∀ x : A, x ≠ 1 → 8 ∣ x.1.1.support.card := by
  obtain ⟨B, hB, hBcard, hBsupport⟩ := exists_regularEightBlockProductSubgroup r
  let s := n - r * 8
  have hsum : r * 8 + s = n := Nat.add_sub_of_le hr
  let e : Fin (r * 8 + s) ≃ Fin n := finCongr hsum
  let f : alternatingGroup (Fin (r * 8)) →* alternatingGroup (Fin n) :=
    e.altCongrHom.toMonoidHom.comp
      ((alternatingProdBlockHom (r * 8) s).comp
        (MonoidHom.inl (alternatingGroup (Fin (r * 8)))
          (alternatingGroup (Fin s))))
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' := e.altCongrHom.injective hxy
    have hpair := alternatingProdBlockHom_injective (r * 8) s hxy'
    exact congrArg Prod.fst hpair
  let A : Subgroup (alternatingGroup (Fin n)) := B.map f
  refine ⟨A, isElementaryAbelian_map_of_injective 2 B hB f hf, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := B) (f := f) hf]
    exact hBcard
  · intro x hx
    rcases x.2 with ⟨a, haB, hax⟩
    have ha1 : (⟨a, haB⟩ : B) ≠ 1 := by
      intro haone
      apply hx
      apply Subtype.ext
      have ha : a = 1 := congrArg Subtype.val haone
      apply Subtype.ext
      simpa [ha] using hax.symm
    have haSupport := hBsupport ⟨a, haB⟩ ha1
    let emb : Fin (r * 8) ↪ Fin n :=
      ⟨fun i => e (finSumFinEquiv (Sum.inl i)), by
        intro i j hij
        exact Sum.inl_injective (finSumFinEquiv.injective (e.injective hij))⟩
    have hsupp : x.1.1.support = a.1.support.map emb := by
      ext y
      rw [Equiv.Perm.mem_support, Finset.mem_map]
      let u := finSumFinEquiv.symm (e.symm y)
      constructor
      · intro hy
        cases hu : u with
        | inl i =>
            refine ⟨i, ?_, ?_⟩
            · rw [Equiv.Perm.mem_support]
              intro hai
              apply hy
              have hval := congrArg Subtype.val hax
              have happ := DFunLike.congr_fun hval y
              have hxy : x.1.1 y = e (finSumFinEquiv (Sum.inl i)) := by
                simpa [f, coe_alternatingProdBlockHom_apply, permProdBlockHom_apply,
                  Equiv.permCongr_apply,
                  show finSumFinEquiv.symm (e.symm y) = Sum.inl i by simpa [u] using hu,
                  hai] using happ.symm
              exact hxy.trans (by
                have hrepr := congrArg (fun z => e (finSumFinEquiv z)) hu
                simpa [u] using hrepr.symm)
            · have hrepr := congrArg (fun z => e (finSumFinEquiv z)) hu
              simpa [emb, u] using hrepr.symm
        | inr j =>
            exfalso
            apply hy
            have hval := congrArg Subtype.val hax
            have happ := DFunLike.congr_fun hval y
            have hxy : x.1.1 y = e (finSumFinEquiv (Sum.inr j)) := by
              simpa [f, coe_alternatingProdBlockHom_apply, permProdBlockHom_apply,
                Equiv.permCongr_apply,
                show finSumFinEquiv.symm (e.symm y) = Sum.inr j by simpa [u] using hu]
                using happ.symm
            exact hxy.trans (by
              have hrepr := congrArg (fun z => e (finSumFinEquiv z)) hu
              simpa [u] using hrepr.symm)
      · rintro ⟨i, hi, rfl⟩
        rw [Equiv.Perm.mem_support] at hi
        intro hfix
        apply hi
        have hval := congrArg Subtype.val hax
        have happ := DFunLike.congr_fun hval (emb i)
        have : e (finSumFinEquiv (Sum.inl (a.1 i))) =
            e (finSumFinEquiv (Sum.inl i)) := by
          simpa [f, coe_alternatingProdBlockHom_apply, permProdBlockHom_apply,
            Equiv.permCongr_apply, emb] using happ.trans hfix
        exact Sum.inl_injective (finSumFinEquiv.injective (e.injective this))
    rw [hsupp, Finset.card_map]
    exact haSupport

end PRank

namespace SchurPresentation

/-- If every nontrivial element of an elementary abelian quotient subgroup
has support divisible by eight, its full preimage in the explicit Schur double
cover is elementary abelian. -/
public theorem elementaryAbelian_preimage_of_support_card_dvd_eight (n : Nat)
    (Lbar : Subgroup (alternatingGroup (Fin (n + 5))))
    (hLbar : IsMulCommutative ↥Lbar ∧
      ∀ x : ↥Lbar, orderOf x = 1 ∨ orderOf x = 2)
    (hsupport : ∀ x : ↥Lbar, x ≠ 1 → 8 ∣ x.1.1.support.card) :
    let L := Lbar.comap (schurAlternatingProjection n)
    IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2 := by
  let L := Lbar.comap (schurAlternatingProjection n)
  change IsMulCommutative ↥L ∧
    ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2
  have hker : Nat.card (schurAlternatingProjection n).ker = 2 := by
    simpa [schurAlternatingCovering] using
      natCard_ker_schurAlternatingCovering n
  have hsq : ∀ x : ↥L, x ^ 2 = 1 := by
    intro x
    let xbar : ↥Lbar := ⟨schurAlternatingProjection n x.1, x.2⟩
    by_cases hxbar : xbar = 1
    · apply Subtype.ext
      apply DoubleCoverUniqueness.ker_pow_two_eq_one
        (schurAlternatingProjection n) hker
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hxbar
    · have hxbar_order : orderOf xbar = 2 := by
        rcases hLbar.2 xbar with hx1 | hx2
        · exact (hxbar (orderOf_eq_one_iff.mp hx1)).elim
        · exact hx2
      have hxbar_sq : xbar.1 ^ 2 = 1 := by
        have hpow := pow_orderOf_eq_one xbar
        rw [hxbar_order] at hpow
        exact congrArg Subtype.val hpow
      have hsupp_dvd : 8 ∣ xbar.1.1.support.card :=
        hsupport xbar hxbar
      obtain ⟨t, ht⟩ := hsupp_dvd
      let m := 2 * t
      have hsupp_pos : 0 < xbar.1.1.support.card := by
        rw [Finset.card_pos]
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        apply hxbar
        apply Subtype.ext
        apply Subtype.ext
        exact Equiv.Perm.support_eq_empty_iff.mp hempty
      have htpos : 0 < t := by omega
      have hm : 1 ≤ m := by
        dsimp [m]
        omega
      have hsupp_le : xbar.1.1.support.card ≤ n + 5 := by
        simpa using Finset.card_le_univ xbar.1.1.support
      have h4m : 4 * m ≤ n + 5 := by
        dsimp [m]
        omega
      let y := canonicalLift n m h4m
      let ybar := schurAlternatingProjection n y
      have hybar_sq : ybar.1 ^ 2 = 1 := by
        have hyorder : orderOf ybar = 2 :=
          canonicalLift_proj_order_two n m h4m hm
        have hpow := pow_orderOf_eq_one ybar
        rw [hyorder] at hpow
        exact congrArg Subtype.val hpow
      have hcard_support : xbar.1.1.support.card = ybar.1.support.card := by
        rw [show ybar.1 = canonicalPerm n m h4m by
          exact canonicalLift_proj n m h4m]
        rw [canonicalPerm_support_card n m h4m]
        dsimp [m]
        omega
      have hxbar_ne_alt : xbar.1 ≠ 1 := by
        intro h
        apply hxbar
        apply Subtype.ext
        exact h
      have hconj : IsConj xbar.1 ybar :=
        alternating_involution_isConj_of_card_support_eq
          (congrArg Subtype.val hxbar_sq) hybar_sq hxbar_ne_alt hcard_support
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hsquare_eq : x.1 ^ 2 = y ^ 2 :=
        DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
          (schurAlternatingCovering n) hker hxbar_sq (by
            change c * schurAlternatingProjection n x.1 * c⁻¹ =
              schurAlternatingProjection n y
            simpa [xbar, ybar] using hc)
      have hy_sq : y ^ 2 = 1 := by
        rw [canonicalLift_sq]
        exact central_pow_of_even n ⟨t, by simp [m, Nat.two_mul]⟩
      exact Subtype.ext (hsquare_eq.trans hy_sq)
  constructor
  · apply IsMulCommutative.of_comm
    intro x y
    have hxinv : x⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq x
    have hyinv : y⁻¹ = y := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq y
    have hxyinv : (x * y)⁻¹ = x * y := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq (x * y)
    calc
      x * y = (x * y)⁻¹ := hxyinv.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxinv, hyinv]
  · intro x
    by_cases hx : x = 1
    · left
      simpa [hx]
    · right
      exact orderOf_eq_prime (hsq x) hx

/-- The support-divisibility preimage criterion transported to an arbitrary
Schur double cover. -/
public theorem elementaryAbelian_preimage_of_support_card_dvd_eight_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (Lbar : Subgroup (alternatingGroup (Fin (n + 5))))
    (hLbar : IsMulCommutative ↥Lbar ∧
      ∀ x : ↥Lbar, orderOf x = 1 ∨ orderOf x = 2)
    (hsupport : ∀ x : ↥Lbar, x ≠ 1 → 8 ∣ x.1.1.support.card) :
    let L := Lbar.comap f.toMonoidHom
    IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2 := by
  let L := Lbar.comap f.toMonoidHom
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hkerCard Lbar
  have hexplicit := elementaryAbelian_preimage_of_support_card_dvd_eight
    n Lbar hLbar hsupport
  let L0 := Lbar.comap (schurAlternatingProjection n)
  change IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2
  change IsMulCommutative ↥L0 ∧
    (∀ x : ↥L0, orderOf x = 1 ∨ orderOf x = 2) at hexplicit
  let : IsMulCommutative ↥L0 := hexplicit.1
  constructor
  · refine ⟨⟨?_⟩⟩
    intro a b
    apply e.injective
    simpa only [map_mul] using
      (Std.Commutative.comm (e a) (e b))
  · intro x
    have hx := hexplicit.2 (e x)
    rw [e.orderOf_eq] at hx
    exact hx




end SchurPresentation

open SchurPresentation
open PRank

public theorem exists_doubleCoverEightBlockWitness {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (hcenterP : IsPGroup 2 (Subgroup.center K))
    (htwo : 2 ∣ Nat.card (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    ∃ A : Subgroup K, IsElementaryAbelian A 2 ∧
      Nat.card A = 2 ^ (3 * (n / 8) + 1) := by
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let : IsQuasisimple (alternatingGroup (Fin n)) := by
    rw [← hq]
    exact SchurPresentation.alternatingGroup_isQuasisimple q
  obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
  let ef : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := ef.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective }
  have hkerCard : Nat.card c.toMonoidHom.ker = 2 := by
    change Nat.card f'.ker = 2
    rw [hf'ker, hfker]
    exact two_primary_alternating_center_card_eq_two n hn e hcenterP htwo
  have hmul : (n / 8) * 8 ≤ q + 5 := by
    rw [hq]
    exact Nat.div_mul_le_self n 8
  obtain ⟨Lbar, hLbar, hLbarCard, hsupport⟩ :=
    exists_regularEightBlockProductSubgroup_of_mul_le (q + 5) (n / 8) hmul
  let L := Lbar.comap c.toMonoidHom
  have hLEA : IsElementaryAbelian L 2 := by
    have h := elementaryAbelian_preimage_of_support_card_dvd_eight_general
      q c hkerCard Lbar hLbar hsupport
    exact h
  refine ⟨L, hLEA, ?_⟩
  have hcard := card_comap_mul c.toMonoidHom c.surjective Lbar
  change Nat.card L = 2 ^ (3 * (n / 8) + 1)
  rw [show L = Lbar.comap c.toMonoidHom by rfl, hcard, hLbarCard, hkerCard]
  rw [pow_succ]

namespace SchurPresentation
open GLS3.Chapter5.PRank

public theorem support_card_dvd_eight_of_mem_elementaryAbelian_schur
    (n : Nat) (A : Subgroup (SchurAlternatingGroup n))
    (hA : IsElementaryAbelian A 2) (x : A)
    (hproj : schurAlternatingProjection n x.1 ≠ 1) :
    8 ∣ (schurAlternatingProjection n x.1).1.support.card := by
  let σ := schurAlternatingProjection n x.1
  have hx1 : x ≠ 1 := by
    intro hx
    apply hproj
    simpa [hx] using map_one (schurAlternatingProjection n)
  have hxorder : orderOf x = 2 := by
    rcases hA.2 x with hxorder | hxorder
    · exact (hx1 (orderOf_eq_one_iff.mp hxorder)).elim
    · exact hxorder
  have hx2 : x.1 ^ 2 = 1 := by
    exact congrArg Subtype.val (by simpa [hxorder] using pow_orderOf_eq_one x)
  have hσorder : orderOf σ = 2 := by
    have hσ2 : σ ^ 2 = 1 := by
      change schurAlternatingProjection n x.1 ^ 2 = 1
      rw [← map_pow, hx2, map_one]
    exact orderOf_eq_prime hσ2 hproj
  have hσ2 : σ.1 ^ 2 = 1 := by
    exact congrArg Subtype.val (by simpa [hσorder] using pow_orderOf_eq_one σ)
  obtain ⟨k, hk⟩ := Equiv.Perm.two_dvd_card_support hσ2
  have hsign : Equiv.Perm.sign σ.1 = 1 := σ.2
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ2] at hsign
  have hfixed : Fintype.card (Function.fixedPoints σ.1) =
      Fintype.card (Fin (n + 5)) - σ.1.support.card := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  rw [hfixed, Nat.sub_sub_self (Finset.card_le_univ σ.1.support), hk] at hsign
  have hkeven : Even k := by
    have hdiv : 2 * k / 2 = k := by omega
    rw [hdiv] at hsign
    rw [neg_one_pow_eq_one_iff_even (by decide)] at hsign
    exact hsign
  obtain ⟨m, hm⟩ := hkeven
  have hsupport : σ.1.support.card = 4 * m := by omega
  have hmpos : 1 ≤ m := by
    have hspos : 0 < σ.1.support.card := by
      rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hproj
      apply Subtype.ext
      exact Equiv.Perm.support_eq_empty_iff.mp hempty
    omega
  have h4m : 4 * m ≤ n + 5 := by
    have := Finset.card_le_univ σ.1.support
    simpa [hsupport] using this
  have hlift := involutionLift_sq_of_support_card n m hmpos h4m σ hσorder
    hsupport x.1 rfl
  rw [hx2] at hlift
  have hzorder : orderOf (schurAlternatingCentral n) = 2 :=
    orderOf_eq_prime (schurAlternatingCentral_sq n)
      (schurAlternatingCentral_ne_one n)
  have hmdvd : 2 ∣ m := by
    rw [← hzorder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hlift.symm
  obtain ⟨t, ht⟩ := hmdvd
  refine ⟨t, ?_⟩
  calc
    σ.1.support.card = 4 * m := hsupport
    _ = 8 * t := by omega

open GLS3.Chapter5.PRank

public theorem support_card_dvd_eight_of_mem_elementaryAbelian
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (A : Subgroup G) (hA : IsElementaryAbelian A 2) (x : A)
    (hproj : f x.1 ≠ 1) : 8 ∣ (f x.1).1.support.card := by
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f (schurAlternatingCovering n)
    hkerCard (natCard_ker_schurAlternatingCovering n)
  let A0 : Subgroup (SchurAlternatingGroup n) := A.map e.toMonoidHom
  have hA0 : IsElementaryAbelian A0 2 :=
    isElementaryAbelian_map_of_injective 2 A hA e.toMonoidHom e.injective
  let x0 : A0 := ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  have hproj0 : schurAlternatingProjection n x0.1 ≠ 1 := by
    have hev := DFunLike.congr_fun he x.1
    change schurAlternatingProjection n (e x.1) ≠ 1
    rw [show schurAlternatingProjection n (e x.1) = f x.1 by exact hev]
    exact hproj
  have hs := support_card_dvd_eight_of_mem_elementaryAbelian_schur
    n A0 hA0 x0 hproj0
  have hev := DFunLike.congr_fun he x.1
  change 8 ∣ (f x.1).1.support.card
  rw [← show schurAlternatingProjection n (e x.1) = f x.1 by exact hev]
  exact hs

end SchurPresentation

namespace PRank

open MulAction
open scoped BigOperators

public theorem smallOrbitKernel_card_le
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [DecidableEq X]
    (hA : IsElementaryAbelian A 2)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X)))
    (hsupport : ∀ a : A, a ≠ 1 →
      8 ∣ ((MulAction.toPerm a : Equiv.Perm X)).support.card) :
    Nat.card (largeOrbitKernel A X) ≤
      2 ^ (3 * (Nat.card (SmallOrbitComplement A X) / 8)) := by
  classical
  haveI : Fintype (largeOrbitKernel A X) := Fintype.ofFinite _
  haveI : Fintype (SmallOrbitComplement A X) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (largeOrbitKernel A X)
      (SmallOrbitComplement A X)) := Fintype.ofFinite _
  obtain ⟨hB, hfaithY, hsmall⟩ := largeOrbitKernel_small_action hA hfaith
  have hsupportY : ∀ b : largeOrbitKernel A X, b ≠ 1 →
      8 ∣ ((MulAction.toPerm b : Equiv.Perm (SmallOrbitComplement A X))).support.card := by
    intro b hb
    have hbne : b.1 ≠ 1 := by
      intro hb1
      apply hb
      exact Subtype.ext hb1
    have hs := hsupport b.1 hbne
    have heq := smallOrbitComplement_support_card_eq (b := b)
    simpa only [heq] using hs
  by_cases hY8 : Nat.card (SmallOrbitComplement A X) < 8
  · have htrivial : ∀ b : largeOrbitKernel A X, b = 1 := by
      intro b
      by_contra hb
      obtain ⟨k, hk⟩ := hsupportY b hb
      have hle : ((MulAction.toPerm b : Equiv.Perm (SmallOrbitComplement A X))).support.card ≤
          Nat.card (SmallOrbitComplement A X) := by
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
      have hzero : ((MulAction.toPerm b : Equiv.Perm (SmallOrbitComplement A X))).support.card = 0 := by
        omega
      have hfix : ∀ y : SmallOrbitComplement A X, b • y = y := by
        intro y
        by_contra hy
        have hymem : y ∈ ((MulAction.toPerm b : Equiv.Perm (SmallOrbitComplement A X))).support :=
          Equiv.Perm.mem_support.mpr hy
        rw [Finset.card_eq_zero.mp hzero] at hymem
        simp at hymem
      apply hb
      apply hfaithY
      funext y
      simpa [hfix y]
    have : Subsingleton (largeOrbitKernel A X) :=
      ⟨fun b c => (htrivial b).trans (htrivial c).symm⟩
    have hcardone : Nat.card (largeOrbitKernel A X) = 1 := Nat.card_unique
    rw [hcardone]
    have hpos : 0 < 2 ^ (3 * (Nat.card (SmallOrbitComplement A X) / 8)) :=
      pow_pos (by omega) _
    omega
  · have hYge : 8 ≤ Nat.card (SmallOrbitComplement A X) := by omega
    letI : Module (ZMod 2) (Additive (largeOrbitKernel A X)) :=
      AddCommGroup.zmodModule (by
        intro x
        change x.toMul ^ 2 = 1
        rcases hB.2 x.toMul with hx | hx
        · have h1 : x.toMul = 1 := orderOf_eq_one_iff.mp hx
          simp [h1]
        · exact orderOf_dvd_iff_pow_eq_one.mp (by simp [hx]))
    let Q := MulAction.orbitRel.Quotient (largeOrbitKernel A X) (SmallOrbitComplement A X)
    let T := {q : Q // Nat.card q.orbit = 2}
    let S := {q : Q // Nat.card q.orbit = 4}
    obtain ⟨f, hf, hiso⟩ :=
      exists_smallOrbitIsotropicLinearMap hB hsmall hfaithY hsupportY
    have hcard := card_le_pow_half_smallOrbitSpace_of_isotropic
      (Nat.card T) (Nat.card S) f hf hiso
    have hdim := two_mul_smallOrbitDimension_le_card
      (A := largeOrbitKernel A X) (X := SmallOrbitComplement A X)
    have hdim' : 2 * (Nat.card T + 2 * Nat.card S) ≤
        Nat.card (SmallOrbitComplement A X) := by
      rw [← Nat.card_eq_fintype_card] at hdim
      simpa [Q, T, S] using hdim
    have hexp : (Nat.card T + 2 * Nat.card S) / 2 ≤
        3 * (Nat.card (SmallOrbitComplement A X) / 8) := by
      omega
    simpa using hcard.trans (Nat.pow_le_pow_right (by omega) hexp)

public theorem supportEight_ea_card_le
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Fintype X]
    [DecidableEq X]
    (hA : IsElementaryAbelian A 2)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X)))
    (hsupport : ∀ a : A, a ≠ 1 →
      8 ∣ ((MulAction.toPerm a : Equiv.Perm X)).support.card) :
    Nat.card A ≤ 2 ^ (3 * (Fintype.card X / 8)) := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _
  haveI : Fintype (LargeOrbitIndex A X) := Fintype.ofFinite _
  have hkernel := largeOrbitKernel_card_le (A := A) (X := X)
  have hsmall := smallOrbitKernel_card_le
    (A := A) (X := X) hA hfaith hsupport
  have hlarge := largeOrbitProduct_card_le (A := A) (X := X) hA
  have hP : IsPGroup 2 A := ea_is_pGroup Nat.prime_two hA
  have hdiv : ∀ q : LargeOrbitIndex A X, 8 ∣ Nat.card q.1.orbit := by
    intro q
    obtain ⟨e, he⟩ := hP.card_orbit (Quotient.out q.1)
    have horbit : Nat.card q.1.orbit = 2 ^ e := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q.1 Quotient.out_eq']
      exact he
    have he3 : 3 ≤ e := by
      by_contra hnot
      have helt : e < 3 := by omega
      have hlargeq := q.2
      rw [horbit] at hlargeq
      have hcases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · simp [h0] at hlargeq
      · simp [h1] at hlargeq
      · simp [h2] at hlargeq
    rw [horbit]
    refine ⟨2 ^ (e - 3), ?_⟩
    calc
      2 ^ e = 2 ^ ((e - 3) + 3) := by rw [Nat.sub_add_cancel he3]
      _ = 2 ^ (e - 3) * 2 ^ 3 := by rw [pow_add]
      _ = 8 * 2 ^ (e - 3) := by norm_num [Nat.mul_comm]
  have hlargeSum :
      (∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit) =
        8 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8 := by
    calc
      (∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit) =
          ∑ q : LargeOrbitIndex A X, 8 * (Nat.card q.1.orbit / 8) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact (Nat.mul_div_cancel' (hdiv q)).symm
      _ = 8 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8 := by
        rw [Finset.mul_sum]
  have hpartition := card_smallOrbitComplement_add_sum_largeOrbit
    (A := A) (X := X)
  rw [hlargeSum] at hpartition
  have hexp :
      3 * (Nat.card (SmallOrbitComplement A X) / 8) +
          3 * (∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8) =
        3 * (Fintype.card X / 8) := by
    omega
  calc
    Nat.card A ≤ Nat.card (largeOrbitKernel A X) *
        Nat.card ((q : LargeOrbitIndex A X) → q.1.orbit) := hkernel
    _ ≤ 2 ^ (3 * (Nat.card (SmallOrbitComplement A X) / 8)) *
        2 ^ (3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8) :=
      Nat.mul_le_mul hsmall hlarge
    _ = 2 ^ (3 * (Nat.card (SmallOrbitComplement A X) / 8) +
        3 * ∑ q : LargeOrbitIndex A X, Nat.card q.1.orbit / 8) := by
      rw [pow_add]
    _ = 2 ^ (3 * (Fintype.card X / 8)) := by rw [hexp]

open GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5.SchurPresentation

public theorem doubleCover_ea_card_le
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (q : Nat) (f : Covering G (alternatingGroup (Fin (q + 5))))
    (hkerCard : Nat.card f.toMonoidHom.ker = 2)
    (A : Subgroup G) (hA : IsElementaryAbelian A 2) :
    Nat.card A ≤ 2 ^ (3 * ((q + 5) / 8) + 1) := by
  classical
  let B : Subgroup (alternatingGroup (Fin (q + 5))) := A.map f.toMonoidHom
  have hB : IsElementaryAbelian B 2 := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨a0, ha0, haeq⟩ := a.2
      obtain ⟨b0, hb0, hbeq⟩ := b.2
      apply Subtype.ext
      change (a : alternatingGroup (Fin (q + 5))) * b = b * a
      rw [← haeq, ← hbeq, ← map_mul, ← map_mul]
      exact congrArg f.toMonoidHom (congrArg Subtype.val
        (isMulCommutative_iff.mp hA.1 ⟨a0, ha0⟩ ⟨b0, hb0⟩))
    · intro b
      by_cases hb : b = 1
      · left
        rw [hb, orderOf_one]
      · right
        obtain ⟨a, ha, hab⟩ := b.2
        have haOrder := hA.2 ⟨a, ha⟩
        have ha2 : (⟨a, ha⟩ : A) ^ 2 = 1 := by
          rcases haOrder with ha1 | ha2
          · rw [orderOf_eq_one_iff.mp ha1, one_pow]
          · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha2])
        apply orderOf_eq_prime (p := 2) (by
          apply Subtype.ext
          change (b : alternatingGroup (Fin (q + 5))) ^ 2 = 1
          rw [← hab, ← map_pow]
          simpa using congrArg f.toMonoidHom (congrArg Subtype.val ha2))
        exact hb
  letI : CommGroup B := {
    mul_comm := isMulCommutative_iff.mp hB.1 }
  have hBfaith : Function.Injective
      (fun b : B => (b • · : Fin (q + 5) → Fin (q + 5))) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext (fun x => congrFun hab x)
  have hBsupport : ∀ b : B, b ≠ 1 →
      8 ∣ ((MulAction.toPerm b : Equiv.Perm (Fin (q + 5)))).support.card := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := b.2
    let aA : A := ⟨a, ha⟩
    have hproj : f a ≠ 1 := by
      intro hfa
      apply hb
      apply Subtype.ext
      exact hab.symm.trans hfa
    have hs := support_card_dvd_eight_of_mem_elementaryAbelian
      q f hkerCard A hA aA hproj
    change 8 ∣ b.1.1.support.card
    change 8 ∣ (f a).1.support.card at hs
    rw [← hab]
    exact hs
  have hBcard : Nat.card B ≤ 2 ^ (3 * ((q + 5) / 8)) := by
    simpa using supportEight_ea_card_le
      (A := B) (X := Fin (q + 5)) hB hBfaith hBsupport
  let g : A →* alternatingGroup (Fin (q + 5)) := f.toMonoidHom.comp A.subtype
  have hgrange : g.range = B := by
    ext y
    simp [g, B]
  have hgker_le : Nat.card g.ker ≤ 2 := by
    calc
      Nat.card g.ker ≤ Nat.card f.toMonoidHom.ker := by
        let i : g.ker → f.toMonoidHom.ker := fun x => ⟨x.1.1, x.2⟩
        apply Nat.card_le_card_of_injective (f := i)
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : f.toMonoidHom.ker => z.1) hxy
      _ = 2 := hkerCard
  have hcard : Nat.card g.ker * Nat.card B = Nat.card A := by
    calc
      Nat.card g.ker * Nat.card B = Nat.card g.ker * Nat.card g.range := by rw [hgrange]
      _ = Nat.card A := by rw [← Subgroup.index_ker, g.ker.card_mul_index]
  calc
    Nat.card A = Nat.card g.ker * Nat.card B := hcard.symm
    _ ≤ 2 * 2 ^ (3 * ((q + 5) / 8)) := Nat.mul_le_mul hgker_le hBcard
    _ = 2 ^ (3 * ((q + 5) / 8) + 1) := by
      rw [pow_add]
      norm_num [Nat.mul_comm]

open MulAction

public theorem exists_orbitQuotientPrimeLinearMap
    (p : Nat) {A X : Type*} [CommGroup A] [MulAction A X] [Finite A]
    [Module (ZMod p) (Additive A)]
    (hp : p.Prime) (hA : IsElementaryAbelian A p)
    (x : X) (d : Nat)
    (hcard : Nat.card (MulAction.orbit A x) = p ^ d) :
    ∃ f : Additive A →ₗ[ZMod p] (Fin d → ZMod p),
      ∀ a : A, f (Additive.ofMul a) = 0 ↔
        a ∈ MulAction.stabilizer A x := by
  let : Fact p.Prime := ⟨hp⟩
  let N : Subgroup A := MulAction.stabilizer A x
  let : N.Normal := Subgroup.normal_of_isMulCommutative N
  letI : Fintype (Additive (A ⧸ N)) := Fintype.ofFinite _
  letI : Module (ZMod p) (Additive (A ⧸ N)) := AddCommGroup.zmodModule (by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ a =>
        change QuotientGroup.mk' N (a ^ p) = 1
        rcases hA.2 a with h | h
        · have ha : a = 1 := orderOf_eq_one_iff.mp h
          simp [ha]
        · rw [orderOf_dvd_iff_pow_eq_one.mp (by simp [h])]
          exact map_one _)
  have hquot : Nat.card (A ⧸ N) = p ^ d := by
    rw [← Subgroup.index_eq_card]
    change (MulAction.stabilizer A x).index = p ^ d
    rw [MulAction.index_stabilizer]
    simpa [Set.ncard_eq_toFinset_card, Nat.card_coe_set_eq] using hcard
  let e : Additive (A ⧸ N) ≃ₗ[ZMod p] (Fin d → ZMod p) := Classical.choice
    (exists_linearEquiv_fin_of_card_eq_prime_pow p hp (Additive (A ⧸ N)) d hquot)
  let qlin : Additive A →ₗ[ZMod p] Additive (A ⧸ N) :=
    ((QuotientGroup.mk' N).toAdditive).toZModLinearMap p
  let f : Additive A →ₗ[ZMod p] (Fin d → ZMod p) := e.toLinearMap.comp qlin
  refine ⟨f, ?_⟩
  intro a
  change e.toLinearMap.toFun (Additive.ofMul (QuotientGroup.mk' N a)) = 0 ↔ a ∈ N
  constructor
  · intro ha
    have hzero : Additive.ofMul (QuotientGroup.mk' N a) = 0 := by
      apply e.injective
      exact ha.trans e.map_zero.symm
    change QuotientGroup.mk' N a = 1 at hzero
    exact (QuotientGroup.eq_one_iff a).mp hzero
  · intro ha
    have hone : QuotientGroup.mk' N a = 1 :=
      (QuotientGroup.eq_one_iff a).mpr ha
    simpa [hone] using e.map_zero

public theorem exists_maximalOddOrbitCoordinates
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Finite X]
    (p : Nat) (hp : p.Prime) [Module (ZMod p) (Additive A)]
    (hA : IsElementaryAbelian A p)
    (d : Nat) (hcardA : Nat.card A = p ^ d)
    (horbit : ∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = p)
    (hcount : Nat.card {q : MulAction.orbitRel.Quotient A X //
      Nat.card q.orbit = p} = d)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X))) :
    let Q := MulAction.orbitRel.Quotient A X
    let D := {q : Q // Nat.card q.orbit = p}
    ∃ eD : Fin d ≃ D,
    ∃ e : Additive A ≃ₗ[ZMod p] (Fin d → ZMod p),
      ∀ a : A, ∀ i : Fin d,
        e (Additive.ofMul a) i = 0 ↔
          a ∈ MulAction.stabilizer A (Quotient.out (eD i).1) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let Q := MulAction.orbitRel.Quotient A X
  let D := {q : Q // Nat.card q.orbit = p}
  letI : Fintype Q := Fintype.ofFinite _
  letI : Fintype D := Fintype.ofFinite _
  letI : Fintype A := Fintype.ofFinite _
  let eD : Fin d ≃ D := by
    apply Fintype.equivOfCardEq
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    change d = Nat.card {q : Q // Nat.card q.orbit = p}
    exact hcount.symm
  have horbit_out (q : Q) :
      Nat.card (MulAction.orbit A (Quotient.out q)) = Nat.card q.orbit := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
  let raw : (i : Fin d) → Additive A →ₗ[ZMod p] (Fin 1 → ZMod p) := fun i =>
    Classical.choose (exists_orbitQuotientPrimeLinearMap p hp hA
      (Quotient.out (eD i).1) 1 (by
        rw [horbit_out]
        simpa using (eD i).2))
  let coord : (i : Fin d) → Additive A →ₗ[ZMod p] ZMod p := fun i =>
    { toFun := fun a => raw i a 0
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let f : Additive A →ₗ[ZMod p] (Fin d → ZMod p) := LinearMap.pi coord
  have hf : Function.Injective f := by
    intro a b hab
    have hz : f (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    apply Additive.toMul.injective
    have hone : (a - b).toMul = 1 := by
      apply hfaith
      funext x
      let q : Q := Quotient.mk'' x
      have hxorb : x ∈ MulAction.orbit A (Quotient.out q) := by
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
        exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
      rcases horbit q with hq1 | hqp
      · have : Fintype q.orbit := Fintype.ofFinite _
        have hc : Fintype.card q.orbit = 1 := by simpa using hq1
        obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hc
        have hx : (⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩ : q.orbit) = u := hu _
        have hm : (a - b).toMul • x ∈ q.orbit := by
          rw [MulAction.orbitRel.Quotient.mem_orbit]
          exact Quotient.sound ⟨(a - b).toMul, rfl⟩
        have hmx : (⟨(a - b).toMul • x, hm⟩ : q.orbit) = u := hu _
        simpa using congrArg Subtype.val (hmx.trans hx.symm)
      · let qi : D := ⟨q, hqp⟩
        let i : Fin d := eD.symm qi
        have hcoord : coord i (a - b) = 0 := by
          exact congrFun hz i
        have hraw : raw i (a - b) = 0 := by
          funext k
          fin_cases k
          exact hcoord
        have hi_eq : eD i = qi := eD.apply_symm_apply qi
        have hspec := Classical.choose_spec
          (exists_orbitQuotientPrimeLinearMap p hp hA
            (Quotient.out (eD i).1) 1 (by
              rw [horbit_out]
              simpa using (eD i).2))
            ((a - b).toMul)
        have hstab' : (a - b).toMul ∈
            MulAction.stabilizer A (Quotient.out (eD i).1) := by
          apply hspec.mp
          simpa [raw] using hraw
        have hq_eq : Quotient.out (eD i).1 = Quotient.out q := by
          simpa [qi] using congrArg (fun z : D => Quotient.out z.1) hi_eq
        have hstab : (a - b).toMul ∈
            MulAction.stabilizer A (Quotient.out q) := by
          rw [← hq_eq]
          exact hstab'
        obtain ⟨c, hc⟩ := hxorb
        rw [← hc]
        change (a - b).toMul • (c • Quotient.out q) =
          1 • (c • Quotient.out q)
        rw [← mul_smul, mul_comm (a - b).toMul c, mul_smul, hstab,
          one_smul]
    exact div_eq_one.mp (by simpa using hone)
  have hcard : Fintype.card (Additive A) =
      Fintype.card (Fin d → ZMod p) := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    simpa [Nat.card_eq_fintype_card] using hcardA
  let e : Additive A ≃ₗ[ZMod p] (Fin d → ZMod p) :=
    LinearEquiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)
  refine ⟨eD, e, ?_⟩
  intro a i
  change coord i (Additive.ofMul a) = 0 ↔ _
  have hs := Classical.choose_spec (exists_orbitQuotientPrimeLinearMap p hp hA
    (Quotient.out (eD i).1) 1 (by rw [horbit_out]; simpa using (eD i).2)) a
  have hs' : raw i (Additive.ofMul a) = 0 ↔
      a ∈ MulAction.stabilizer A (Quotient.out (eD i).1) := by
    simpa [raw] using hs
  rw [← hs']
  constructor
  · intro h
    funext k
    fin_cases k
    exact h
  · intro h
    exact congrFun h 0

open MulAction

public theorem maximalOddOrbit_structure
    {A X : Type*} [CommGroup A] [MulAction A X] [Finite A] [Finite X]
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : IsElementaryAbelian A p)
    (hfaith : Function.Injective (fun a : A => (a • · : X → X)))
    (hcard : Nat.card A = p ^ (Nat.card X / p)) :
    (∀ q : MulAction.orbitRel.Quotient A X,
      Nat.card q.orbit = 1 ∨ Nat.card q.orbit = p) ∧
    Nat.card {q : MulAction.orbitRel.Quotient A X //
      Nat.card q.orbit = p} = Nat.card X / p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype X := Fintype.ofFinite _
  let Q := MulAction.orbitRel.Quotient A X
  letI : Fintype Q := Fintype.ofFinite _
  have hP : IsPGroup p A := ea_is_pGroup hp hA
  let e : Q → Nat := fun q => Classical.choose
    (hP.card_orbit (Quotient.out q))
  have he (q : Q) : Nat.card q.orbit = p ^ e q := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact Classical.choose_spec (hP.card_orbit (Quotient.out q))
  have hsum : (∑ q : Q, Nat.card q.orbit) = Nat.card X := by
    have eX : (Σ q : Q, q.orbit) ≃ X :=
      Equiv.ofBijective (fun z : Σ q : Q, q.orbit => z.2.1)
        ⟨by
          intro z w hzw
          rcases z with ⟨q, x⟩
          rcases w with ⟨r, y⟩
          change x.1 = y.1 at hzw
          have hqr : q = r := calc
            q = Quotient.mk'' x.1 :=
              (MulAction.orbitRel.Quotient.mem_orbit.mp x.2).symm
            _ = Quotient.mk'' y.1 := by rw [hzw]
            _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp y.2
          apply Sigma.ext
          · exact hqr
          · subst r
            exact heq_of_eq (Subtype.ext hzw),
         by
          intro x
          exact ⟨⟨Quotient.mk'' x,
            ⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩⟩, rfl⟩⟩
    calc
      (∑ q : Q, Nat.card q.orbit) = ∑ q : Q, Fintype.card q.orbit := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Nat.card_eq_fintype_card]
      _ = Fintype.card (Σ q : Q, q.orbit) := Fintype.card_sigma.symm
      _ = Fintype.card X := Fintype.card_congr eX
      _ = Nat.card X := Nat.card_eq_fintype_card.symm
  let eval : A → (q : Q) → q.orbit := fun a q =>
    ⟨a • Quotient.out q, by
      rw [MulAction.orbitRel.Quotient.mem_orbit]
      calc
        Quotient.mk'' (s₁ := MulAction.orbitRel A X) (a • Quotient.out q) =
            Quotient.mk'' (s₁ := MulAction.orbitRel A X) (Quotient.out q) := by
          exact Quotient.sound ⟨a, rfl⟩
        _ = q := Quotient.out_eq' q⟩
  have heval : Function.Injective eval := by
    intro a b hab
    apply hfaith
    funext x
    let q : Q := Quotient.mk'' x
    have hx : x ∈ MulAction.orbit A (Quotient.out q) := by
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    obtain ⟨c, hc⟩ := hx
    have hrep : a • Quotient.out q = b • Quotient.out q :=
      congrArg Subtype.val (congrFun hab q)
    rw [← hc]
    change a • (c • Quotient.out q) = b • (c • Quotient.out q)
    calc
      a • (c • Quotient.out q) = c • (a • Quotient.out q) := by
        rw [← mul_smul, mul_comm a c, mul_smul]
      _ = c • (b • Quotient.out q) := by rw [hrep]
      _ = b • (c • Quotient.out q) := by
        rw [← mul_smul, mul_comm c b, mul_smul]
  have hprod : Nat.card A ≤ ∏ q : Q, Nat.card q.orbit := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card A ≤ Fintype.card ((q : Q) → q.orbit) :=
        Fintype.card_le_of_injective eval heval
      _ = ∏ q : Q, Fintype.card q.orbit := Fintype.card_pi
      _ = ∏ q : Q, Nat.card q.orbit := by
        apply Finset.prod_congr rfl
        intro q hq
        rw [Nat.card_eq_fintype_card]
  have hpow : p ^ (Nat.card X / p) ≤ p ^ (∑ q : Q, e q) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    simpa only [← he] using hcard ▸ hprod
  have hrank : Nat.card X / p ≤ ∑ q : Q, e q :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  have hele (q : Q) : e q ≤ Nat.card q.orbit / p := by
    by_cases hz : e q = 0
    · simp [hz]
    · rw [he]
      exact rank_le_size_div_p hp.one_lt (Nat.one_le_iff_ne_zero.mpr hz)
  have hsumle : (∑ q : Q, e q) ≤
      ∑ q : Q, Nat.card q.orbit / p :=
    Finset.sum_le_sum (fun q hq => hele q)
  have hdiv : (∑ q : Q, Nat.card q.orbit / p) ≤
      (∑ q : Q, Nat.card q.orbit) / p := by
    let s : Finset Q := Finset.univ
    have hmain : ∀ t : Finset Q,
        (∑ q ∈ t, Nat.card q.orbit / p) ≤
          (∑ q ∈ t, Nat.card q.orbit) / p := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        calc
          Nat.card a.orbit / p + ∑ q ∈ s, Nat.card q.orbit / p
              ≤ Nat.card a.orbit / p + (∑ q ∈ s, Nat.card q.orbit) / p :=
            Nat.add_le_add_left ih _
          _ ≤ (Nat.card a.orbit + ∑ q ∈ s, Nat.card q.orbit) / p := by
            rw [Nat.add_div hp.pos]
            omega
    simpa using hmain s
  have hend : (∑ q : Q, Nat.card q.orbit) / p = Nat.card X / p := by
    rw [hsum]
  have heqsum : (∑ q : Q, e q) =
      ∑ q : Q, Nat.card q.orbit / p := by
    omega
  have heq (q : Q) : e q = Nat.card q.orbit / p := by
    apply le_antisymm (hele q)
    by_contra hnot
    have hlt : e q < Nat.card q.orbit / p := Nat.lt_of_not_ge hnot
    have hall : ∀ i ∈ (Finset.univ : Finset Q),
        e i ≤ Nat.card i.orbit / p := fun i hi => hele i
    have hsumlt := Finset.sum_lt_sum hall ⟨q, Finset.mem_univ q, hlt⟩
    omega
  have horbit (q : Q) : Nat.card q.orbit = 1 ∨ Nat.card q.orbit = p := by
    by_cases hz : e q = 0
    · left
      rw [he q, hz, pow_zero]
    · right
      have hle1 : e q ≤ 1 := by
        by_contra hnot
        have hr2 : 2 ≤ e q := by omega
        have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
        have hstrict := rank_lt_size_div_p hp3 hr2
        have hequal : e q = p ^ e q / p := by
          rw [← he q]
          exact heq q
        exact (Nat.ne_of_lt hstrict) hequal
      have he1 : e q = 1 := by omega
      rw [he q, he1, pow_one]
  refine ⟨horbit, ?_⟩
  have hsumE : (∑ q : Q, e q) = Nat.card X / p := by omega
  have heIndicator (q : Q) : e q = if Nat.card q.orbit = p then 1 else 0 := by
    rcases horbit q with hq1 | hqp
    · rw [heq q, hq1]
      rw [if_neg (Ne.symm hp.ne_one)]
      exact Nat.div_eq_of_lt hp.one_lt
    · rw [heq q, hqp]
      rw [if_pos rfl]
      exact Nat.div_self hp.pos
  calc
    Nat.card {q : Q // Nat.card q.orbit = p} =
        Fintype.card {q : Q // Nat.card q.orbit = p} :=
      Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun q : Q => Nat.card q.orbit = p).card :=
      Fintype.card_subtype _
    _ = ∑ q : Q, if Nat.card q.orbit = p then 1 else 0 :=
      Finset.card_filter _ _
    _ = ∑ q : Q, e q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (heIndicator q).symm
    _ = Nat.card X / p := hsumE

open MulAction

public theorem alternatingSubgroup_action_faithful
    {n : Nat} (A : Subgroup (alternatingGroup (Fin n))) :
    Function.Injective (fun a : A => (a • · : Fin n → Fin n)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  exact congrFun hab x

public theorem alternating_maximalOddSubgroups_inSameMulAutOrbit (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (A B : Subgroup (alternatingGroup (Fin n)))
    (hA : IsElementaryAbelian A p) (hB : IsElementaryAbelian B p)
    (hcardA : Nat.card A = p ^ (n / p))
    (hcardB : Nat.card B = p ^ (n / p)) :
    ∃ α : MulAut (alternatingGroup (Fin n)),
      Subgroup.map α.toMonoidHom A = B := by
  classical
  let d := n / p
  letI : CommGroup A := { mul_comm := isMulCommutative_iff.mp hA.1 }
  letI : CommGroup B := { mul_comm := isMulCommutative_iff.mp hB.1 }
  letI : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (by
    intro a
    apply Additive.toMul.injective
    change a.toMul ^ p = 1
    rcases hA.2 a.toMul with ha | ha
    · rw [orderOf_eq_one_iff.mp ha, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]))
  letI : Module (ZMod p) (Additive B) := AddCommGroup.zmodModule (by
    intro b
    apply Additive.toMul.injective
    change b.toMul ^ p = 1
    rcases hB.2 b.toMul with hb | hb
    · rw [orderOf_eq_one_iff.mp hb, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hb]))
  have hfaithA := alternatingSubgroup_action_faithful A
  have hfaithB := alternatingSubgroup_action_faithful B
  have hcardFin : Nat.card (Fin n) = n := by simp
  obtain ⟨horbitA, hcountA⟩ := maximalOddOrbit_structure p hp hp2 hA hfaithA (by
    simpa [hcardFin] using hcardA)
  obtain ⟨horbitB, hcountB⟩ := maximalOddOrbit_structure p hp hp2 hB hfaithB (by
    simpa [hcardFin] using hcardB)
  obtain ⟨eDA, eA, hcoordA⟩ := exists_maximalOddOrbitCoordinates p hp hA d (by
      simpa [d] using hcardA) horbitA (by simpa [d, hcardFin] using hcountA) hfaithA
  obtain ⟨eDB, eB, hcoordB⟩ := exists_maximalOddOrbitCoordinates p hp hB d (by
      simpa [d] using hcardB) horbitB (by simpa [d, hcardFin] using hcountB) hfaithB
  let eAdd : Additive A ≃+ Additive B := eA.toAddEquiv.trans eB.symm.toAddEquiv
  let e : A ≃* B := {
    toFun := fun a => (eAdd (Additive.ofMul a)).toMul
    invFun := fun b => (eAdd.symm (Additive.ofMul b)).toMul
    left_inv := by intro a; simp [eAdd]
    right_inv := by intro b; simp [eAdd]
    map_mul' := by
      intro a b
      apply Additive.ofMul.injective
      exact eAdd.map_add (Additive.ofMul a) (Additive.ofMul b) }
  let QA := MulAction.orbitRel.Quotient A (Fin n)
  let QB := MulAction.orbitRel.Quotient B (Fin n)
  let DA := {q : QA // Nat.card q.orbit = p}
  let DB := {q : QB // Nat.card q.orbit = p}
  let NA := {q : QA // ¬ Nat.card q.orbit = p}
  let NB := {q : QB // ¬ Nat.card q.orbit = p}
  let FA := {q : QA // Nat.card q.orbit = 1}
  let FB := {q : QB // Nat.card q.orbit = 1}
  letI : Fintype QA := Fintype.ofFinite _
  letI : Fintype QB := Fintype.ofFinite _
  letI : Fintype DA := Fintype.ofFinite _
  letI : Fintype DB := Fintype.ofFinite _
  letI : Fintype NA := Fintype.ofFinite _
  letI : Fintype NB := Fintype.ofFinite _
  letI : Fintype FA := Fintype.ofFinite _
  letI : Fintype FB := Fintype.ofFinite _
  let eD : DA ≃ DB := eDA.symm.trans eDB
  have hnotA (q : QA) : (¬ Nat.card q.orbit = p) ↔ Nat.card q.orbit = 1 := by
    constructor
    · intro h
      rcases horbitA q with h1 | hp'
      · exact h1
      · exact False.elim (h hp')
    · intro h1 hp'
      exact hp.ne_one (hp'.symm.trans h1)
  have hnotB (q : QB) : (¬ Nat.card q.orbit = p) ↔ Nat.card q.orbit = 1 := by
    constructor
    · intro h
      rcases horbitB q with h1 | hp'
      · exact h1
      · exact False.elim (h hp')
    · intro h1 hp'
      exact hp.ne_one (hp'.symm.trans h1)
  let eNAF : NA ≃ FA := Equiv.subtypeEquivRight hnotA
  let eNBF : NB ≃ FB := Equiv.subtypeEquivRight hnotB
  have hfixedA := fixedOrbit_card_eq_sub p d hp.one_lt horbitA (by simpa [d, hcardFin] using hcountA)
  have hfixedB := fixedOrbit_card_eq_sub p d hp.one_lt horbitB (by simpa [d, hcardFin] using hcountB)
  change Nat.card FA = Nat.card (Fin n) - p * d at hfixedA
  change Nat.card FB = Nat.card (Fin n) - p * d at hfixedB
  let eF : FA ≃ FB := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hfixedA.trans hfixedB.symm)
  let eN : NA ≃ NB := eNAF.trans (eF.trans eNBF.symm)
  let eqOrbit : QA ≃ QB :=
    (Equiv.sumCompl (fun q : QA => Nat.card q.orbit = p)).symm.trans
      ((Equiv.sumCongr eD eN).trans
        (Equiv.sumCompl (fun q : QB => Nat.card q.orbit = p)))
  have hstab : ∀ q : QA, ∀ a : A,
      a ∈ MulAction.stabilizer A (Quotient.out q) ↔
        e a ∈ MulAction.stabilizer B (Quotient.out (eqOrbit q)) := by
    intro q a
    by_cases hqp : Nat.card q.orbit = p
    · let qD : DA := ⟨q, hqp⟩
      let i : Fin d := eDA.symm qD
      have heqOrbit : eqOrbit q = (eD qD).1 := by
        unfold eqOrbit
        simp only [Equiv.trans_apply]
        rw [Equiv.sumCompl_symm_apply_of_pos (p := fun q : QA => Nat.card q.orbit = p) hqp]
        rfl
      have hiA : (eDA i).1 = q := by
        exact congrArg Subtype.val (eDA.apply_symm_apply qD)
      have hiB : (eDB i).1 = (eD qD).1 := by
        rfl
      rw [heqOrbit, ← hiA, ← hiB]
      have hAcoord := hcoordA a i
      have hBcoord := hcoordB (e a) i
      rw [← hAcoord, ← hBcoord]
      have hecoord : eB.toLinearMap.toFun (Additive.ofMul (e a)) = eA.toLinearMap.toFun (Additive.ofMul a) := by
        simp [e, eAdd]
      change eA.toLinearMap.toFun (Additive.ofMul a) i = 0 ↔
        eB.toLinearMap.toFun (Additive.ofMul (e a)) i = 0
      rw [congrFun hecoord i]
    · have hq1 : Nat.card q.orbit = 1 := (hnotA q).mp hqp
      have heqOrbit : eqOrbit q = (eN ⟨q, hqp⟩).1 := by
        unfold eqOrbit
        simp only [Equiv.trans_apply]
        rw [Equiv.sumCompl_symm_apply_of_neg (p := fun q : QA => Nat.card q.orbit = p) hqp]
        rfl
      have heqNot : ¬ Nat.card (eqOrbit q).orbit = p := by
        rw [heqOrbit]
        exact (eN ⟨q, hqp⟩).2
      have heq1 : Nat.card (eqOrbit q).orbit = 1 := (hnotB (eqOrbit q)).mp heqNot
      constructor
      · intro ha
        exact mem_stabilizer_of_orbit_card_eq_one (eqOrbit q) heq1 (e a)
      · intro hb
        exact mem_stabilizer_of_orbit_card_eq_one q hq1 a
  obtain ⟨τ, hτ⟩ := exists_equivariantEquiv_of_stabilizer_equiv e eqOrbit hstab
  let α : MulAut (alternatingGroup (Fin n)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin n)) τ
  refine ⟨α, ?_⟩
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := hb
    have hαa : α a = (e ⟨a, ha⟩ : B) := by
      apply Subtype.ext
      apply Equiv.Perm.ext
      intro x
      change τ ((⟨a, ha⟩ : A) • τ.symm x) = e (⟨a, ha⟩ : A) • x
      simpa using hτ ⟨a, ha⟩ (τ.symm x)
    rw [← hab]
    change α a ∈ B
    rw [hαa]
    exact (e ⟨a, ha⟩).2
  · intro hb
    let aA : A := e.symm ⟨b, hb⟩
    refine ⟨aA.1, aA.2, ?_⟩
    have hαa : α aA = (e aA : B) := by
      apply Subtype.ext
      apply Equiv.Perm.ext
      intro x
      change τ (aA • τ.symm x) = e aA • x
      simpa using hτ aA (τ.symm x)
    change α aA.1 = b
    rw [hαa]
    simp [aA]

open GLS3.Chapter5.SchurPresentation

/-- The standard `p`-cycle in the alternating group on `Fin p`. -/
@[expose] public def oddPrimeCycle (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    alternatingGroup (Fin p) :=
  ⟨finRotate p, by
    rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
    exact (hp.even_sub_one hp2).neg_one_pow⟩

public theorem oddPrimeCycle_orderOf (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (oddPrimeCycle p hp hp2) = p := by
  have hcycle : (finRotate p).IsCycle := isCycle_finRotate_of_le hp.two_le
  have hpgt2 : 2 < p := by
    exact lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hsupport : (finRotate p).support.card = p := by
    rw [show p = (p - 2) + 2 by omega, support_finRotate,
      Finset.card_univ, Fintype.card_fin]
  calc
    orderOf (oddPrimeCycle p hp hp2) = orderOf (finRotate p) :=
      Subgroup.orderOf_coe (oddPrimeCycle p hp hp2) |>.symm
    _ = (finRotate p).support.card := hcycle.orderOf
    _ = p := hsupport

/-- The blockwise product of the cyclic groups generated by the standard
`p`-cycle. -/
@[expose] public def oddPrimeCycleProduct
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup (Fin r → alternatingGroup (Fin p)) :=
  Subgroup.pi Set.univ (fun _ => Subgroup.zpowers (oddPrimeCycle p hp hp2))

private theorem __ch5_proposition_5_2_10_oddPrimeCycleProduct_comm
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ a b : oddPrimeCycleProduct r p hp hp2, a * b = b * a := by
  intro a b
  apply Subtype.ext
  funext i
  obtain ⟨ka, hka⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i))
  obtain ⟨kb, hkb⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_pi Set.univ).mp b.2 i (Set.mem_univ i))
  change a.1 i * b.1 i = b.1 i * a.1 i
  rw [← hka, ← hkb]
  exact ((Commute.refl (oddPrimeCycle p hp hp2)).zpow_left ka).zpow_right kb |>.eq

private theorem __ch5_proposition_5_2_10_oddPrimeCycleProduct_pow_eq_one
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : oddPrimeCycleProduct r p hp hp2) :
    a ^ p = 1 := by
  apply Subtype.ext
  funext i
  apply (orderOf_dvd_iff_pow_eq_one).mp
  simpa only [oddPrimeCycle_orderOf p hp hp2] using
    (orderOf_dvd_of_mem_zpowers
      ((Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i)))

public theorem oddPrimeCycleProduct_isElementaryAbelian
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    IsElementaryAbelian (oddPrimeCycleProduct r p hp hp2) p := by
  constructor
  · exact isMulCommutative_iff.mpr
      (__ch5_proposition_5_2_10_oddPrimeCycleProduct_comm r p hp hp2)
  · intro a
    by_cases ha : a = 1
    · left
      exact orderOf_eq_one_iff.mpr ha
    · right
      let : Fact p.Prime := ⟨hp⟩
      exact orderOf_eq_prime (__ch5_proposition_5_2_10_oddPrimeCycleProduct_pow_eq_one r p hp hp2 a) ha

private def __ch5_proposition_5_2_10_oddPrimeCycleProductEquiv
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    oddPrimeCycleProduct r p hp hp2 ≃
      ((i : Fin r) → Subgroup.zpowers (oddPrimeCycle p hp hp2)) :=
  { toFun := fun a i =>
      ⟨a.1 i, (Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i)⟩
    invFun := fun a =>
      ⟨fun i => a i, (Subgroup.mem_pi Set.univ).mpr fun i hi => (a i).2⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro a
      funext i
      rfl }

public theorem oddPrimeCycleProduct_card
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (oddPrimeCycleProduct r p hp hp2) = p ^ r := by
  calc
    Nat.card (oddPrimeCycleProduct r p hp hp2) =
        ∏ i : Fin r, Nat.card (Subgroup.zpowers (oddPrimeCycle p hp hp2)) :=
      (Nat.card_congr (__ch5_proposition_5_2_10_oddPrimeCycleProductEquiv r p hp hp2)).trans Nat.card_pi
    _ = ∏ _ : Fin r, p := by
      simp [Nat.card_eq_fintype_card, Fintype.card_zpowers,
        oddPrimeCycle_orderOf p hp hp2]
    _ = p ^ Fintype.card (Fin r) := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = p ^ r := by rw [Fintype.card_fin]

/-- The block-cycle product embeds into the alternating group on `r * p`
points, giving a witness of order `p^r`. -/
public theorem exists_oddPrimeCycleProduct_witness
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ A : Subgroup (alternatingGroup (Fin (r * p))),
      IsElementaryAbelian A p ∧ Nat.card A = p ^ r := by
  let : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  let N := Fin r → alternatingGroup (Fin p)
  let S := N ⋊[alternatingBlockAction r p] alternatingGroup (Fin r)
  let f : N →* alternatingGroup (Fin (r * p)) :=
    (alternatingImprimitiveFinHom r p).comp
      (SemidirectProduct.inl : N →* S)
  have hf : Function.Injective f := by
    intro x y hxy
    change alternatingImprimitiveFinHom r p (SemidirectProduct.inl x) =
      alternatingImprimitiveFinHom r p (SemidirectProduct.inl y) at hxy
    have hsem : (SemidirectProduct.inl x : S) = SemidirectProduct.inl y :=
      alternatingImprimitiveFinHom_injective r p hxy
    exact SemidirectProduct.inl_injective hsem
  let A := (oddPrimeCycleProduct r p hp hp2).map f
  refine ⟨A, PRank.isElementaryAbelian_map_of_injective p
      (oddPrimeCycleProduct r p hp hp2)
      (oddPrimeCycleProduct_isElementaryAbelian r p hp hp2) f hf, ?_⟩
  rw [show A = (oddPrimeCycleProduct r p hp hp2).map f by rfl,
    Subgroup.card_map_of_injective hf,
    oddPrimeCycleProduct_card r p hp hp2]

open GLS3.Chapter5.SchurPresentation

private theorem __ch5_proposition_5_2_10_alternatingProdBlockLeft_injective (a b : Nat) :
    Function.Injective ((alternatingProdBlockHom a b).comp
      (MonoidHom.inl (alternatingGroup (Fin a))
        (alternatingGroup (Fin b)))) := by
  intro x y hxy
  have hprod : ((x, 1) : alternatingGroup (Fin a) ×
      alternatingGroup (Fin b)) = (y, 1) := by
    apply alternatingProdBlockHom_injective a b
    exact hxy
  exact congrArg Prod.fst hprod

/-- Disjoint odd-prime cycles give a witness in every larger alternating
`degree`, with the unused points fixed. -/
public theorem exists_oddPrimeCycleProduct_witness_of_mul_le
    (n r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrp : r * p ≤ n) :
    ∃ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A p ∧ Nat.card A = p ^ r := by
  obtain ⟨B, hB, hBcard⟩ := exists_oddPrimeCycleProduct_witness r p hp hp2
  let s := n - r * p
  let f : alternatingGroup (Fin (r * p)) →*
      alternatingGroup (Fin ((r * p) + s)) :=
    (alternatingProdBlockHom (r * p) s).comp
      (MonoidHom.inl (alternatingGroup (Fin (r * p)))
        (alternatingGroup (Fin s)))
  have hf : Function.Injective f :=
    __ch5_proposition_5_2_10_alternatingProdBlockLeft_injective (r * p) s
  let A := B.map f
  have hdegree : (r * p) + s = n := by
    dsimp [s]
    exact Nat.add_sub_of_le hrp
  have hA : IsElementaryAbelian A p := by
    exact PRank.isElementaryAbelian_map_of_injective p B hB f hf
  have hcard : Nat.card A = p ^ r := by
    rw [show A = B.map f by rfl, Subgroup.card_map_of_injective hf, hBcard]
  rw [← hdegree]
  exact ⟨A, hA, hcard⟩

open GLS3.Chapter5.SchurPresentation

@[expose] public def evenKleinFourProduct (r : Nat) :
    Subgroup (Fin r → alternatingGroup (Fin 4)) :=
  Subgroup.pi Set.univ (fun _ => alternatingGroup.kleinFour (Fin 4))

private theorem __ch5_proposition_5_2_10_evenKleinFourProduct_comm (r : Nat) :
    ∀ a b : evenKleinFourProduct r, a * b = b * a := by
  intro a b
  apply Subtype.ext
  funext i
  have : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have hcomm := isMulCommutative_iff.mp IsKleinFour.isMulCommutative
    (⟨a.1 i, (Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i)⟩ :
      alternatingGroup.kleinFour (Fin 4))
    (⟨b.1 i, (Subgroup.mem_pi Set.univ).mp b.2 i (Set.mem_univ i)⟩ :
      alternatingGroup.kleinFour (Fin 4))
  exact congrArg Subtype.val hcomm

private theorem __ch5_proposition_5_2_10_evenKleinFourProduct_sq (r : Nat)
    (a : evenKleinFourProduct r) : a ^ 2 = 1 := by
  apply Subtype.ext
  funext i
  have hi : a.1 i ∈ alternatingGroup.kleinFour (Fin 4) :=
    (Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i)
  have : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have h := Monoid.pow_exponent_eq_one (⟨a.1 i, hi⟩ : alternatingGroup.kleinFour (Fin 4))
  simpa using congrArg Subtype.val h

public theorem evenKleinFourProduct_isElementaryAbelian (r : Nat) :
    IsElementaryAbelian (evenKleinFourProduct r) 2 := by
  constructor
  · exact isMulCommutative_iff.mpr (__ch5_proposition_5_2_10_evenKleinFourProduct_comm r)
  · intro a
    by_cases ha : a = 1
    · left
      exact orderOf_eq_one_iff.mpr ha
    · right
      exact orderOf_eq_prime
        (by simpa [pow_two] using __ch5_proposition_5_2_10_evenKleinFourProduct_sq r a) ha

private def __ch5_proposition_5_2_10_evenKleinFourProductEquiv (r : Nat) :
    evenKleinFourProduct r ≃
      ((i : Fin r) → alternatingGroup.kleinFour (Fin 4)) :=
  { toFun := fun a i =>
      ⟨a.1 i, (Subgroup.mem_pi Set.univ).mp a.2 i (Set.mem_univ i)⟩
    invFun := fun a =>
      ⟨fun i => a i, (Subgroup.mem_pi Set.univ).mpr fun i hi => (a i).2⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro a
      funext i
      rfl }

public theorem evenKleinFourProduct_card (r : Nat) :
    Nat.card (evenKleinFourProduct r) = 2 ^ (2 * r) := by
  let : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  calc
    Nat.card (evenKleinFourProduct r) =
        ∏ i : Fin r, Nat.card (alternatingGroup.kleinFour (Fin 4)) :=
      (Nat.card_congr (__ch5_proposition_5_2_10_evenKleinFourProductEquiv r)).trans Nat.card_pi
    _ = ∏ _ : Fin r, 4 := by simp
    _ = 4 ^ r := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = 2 ^ (2 * r) := by
      rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]

public theorem exists_evenKleinFourProduct_witness (r : Nat) :
    ∃ A : Subgroup (alternatingGroup (Fin (r * 4))),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (2 * r) := by
  let : Nonempty (Fin 4) := ⟨⟨0, by omega⟩⟩
  let N := Fin r → alternatingGroup (Fin 4)
  let S := N ⋊[alternatingBlockAction r 4] alternatingGroup (Fin r)
  let f : N →* alternatingGroup (Fin (r * 4)) :=
    (alternatingImprimitiveFinHom r 4).comp
      (SemidirectProduct.inl : N →* S)
  have hf : Function.Injective f := by
    intro x y hxy
    change alternatingImprimitiveFinHom r 4 (SemidirectProduct.inl x) =
      alternatingImprimitiveFinHom r 4 (SemidirectProduct.inl y) at hxy
    have hxy' := alternatingImprimitiveFinHom_injective r 4 hxy
    exact SemidirectProduct.inl_injective hxy'
  let B : Subgroup N :=
    Subgroup.pi Set.univ (fun _ => alternatingGroup.kleinFour (Fin 4))
  let A : Subgroup (alternatingGroup (Fin (r * 4))) := B.map f
  have hB : IsElementaryAbelian B 2 :=
    evenKleinFourProduct_isElementaryAbelian r
  have hA : IsElementaryAbelian A 2 :=
    isElementaryAbelian_map_of_injective 2 B hB f hf
  refine ⟨A, hA, ?_⟩
  rw [Subgroup.card_map_of_injective (K := B) (f := f) hf]
  exact evenKleinFourProduct_card r

public theorem exists_evenKleinFourProduct_witness_of_mul_le
    (n r : Nat) (hr : 4 * r ≤ n) :
    ∃ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (2 * r) := by
  obtain ⟨B, hB, hBcard⟩ := exists_evenKleinFourProduct_witness r
  have hsum : r * 4 + (n - r * 4) = n := by omega
  let e : Fin (r * 4 + (n - r * 4)) ≃ Fin n := finCongr hsum
  let f : alternatingGroup (Fin (r * 4)) →*
      alternatingGroup (Fin n) :=
    (e.altCongrHom.toMonoidHom).comp
      ((SchurPresentation.alternatingProdBlockHom (r * 4) (n - r * 4)).comp
        (MonoidHom.inl (alternatingGroup (Fin (r * 4)))
          (alternatingGroup (Fin (n - r * 4)))))
  let A : Subgroup (alternatingGroup (Fin n)) := B.map f
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' := e.altCongrHom.injective hxy
    have hxy'' := SchurPresentation.alternatingProdBlockHom_injective
      (r * 4) (n - r * 4) hxy'
    exact congrArg Prod.fst hxy''
  refine ⟨A, isElementaryAbelian_map_of_injective 2 B hB f hf, ?_⟩
  rw [Subgroup.card_map_of_injective (K := B) (f := f) hf]
  exact hBcard

open MulAction

/-- For an abelian subgroup of an alternating group, deleting one orbit of
size two from the orbit-evaluation map remains injective. -/
public theorem card_le_card_orbit_evaluation_away_of_card_eq_two
    {n : Nat} (A : Subgroup (alternatingGroup (Fin n)))
    (hA : ∀ a b : ↥A, a * b = b * a)
    [Fintype ↥A] [Fintype (MulAction.orbitRel.Quotient ↥A (Fin n))]
    (q0 : MulAction.orbitRel.Quotient ↥A (Fin n))
    (hq0 : Nat.card q0.orbit = 2) :
    Nat.card ↥A ≤ Nat.card
      ((q : {q : MulAction.orbitRel.Quotient ↥A (Fin n) // q ≠ q0}) →
        q.1.orbit) := by
  classical
  let Q := MulAction.orbitRel.Quotient ↥A (Fin n)
  let Q' := {q : Q // q ≠ q0}
  letI : Fintype Q' := Fintype.ofFinite _
  change Nat.card ↥A ≤ Nat.card ((q : Q') → q.1.orbit)
  have : ∀ q : Q', Fintype q.1.orbit := fun q => Fintype.ofFinite _
  let f : ↥A → (q : Q') → q.1.orbit := fun a q =>
    ⟨a • Quotient.out q.1, by
      rw [MulAction.orbitRel.Quotient.mem_orbit]
      calc
        Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n))
              (a • Quotient.out q.1) =
            Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n))
              (Quotient.out q.1) := by
          apply Quotient.sound (s := MulAction.orbitRel ↥A (Fin n))
          exact ⟨a, rfl⟩
        _ = q.1 := Quotient.out_eq' q.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    let g : ↥A := b⁻¹ * a
    have hfix : ∀ y : Fin n, y ∉ q0.orbit → g • y = y := by
      intro y hy
      let q : Q := Quotient.mk'' y
      have hq : q ≠ q0 := by
        intro heq
        apply hy
        rw [← heq]
        exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
      let q' : Q' := ⟨q, hq⟩
      have hagree : a • Quotient.out q = b • Quotient.out q := by
        exact congrArg Subtype.val (congrFun hab q')
      have hgout : g • Quotient.out q = Quotient.out q := by
        calc
          g • Quotient.out q = b⁻¹ • (a • Quotient.out q) := by
            rw [mul_smul]
          _ = b⁻¹ • (b • Quotient.out q) := by rw [hagree]
          _ = Quotient.out q := by
            rw [← mul_smul, inv_mul_cancel, one_smul]
      have hstab : ∀ z : Fin n,
          z ∈ MulAction.orbit ↥A (Quotient.out q) → g • z = z := by
        intro z hz
        rcases hz with ⟨c, rfl⟩
        calc
          g • (c • Quotient.out q) = (g * c) • Quotient.out q := by
            rw [← mul_smul]
          _ = (c * g) • Quotient.out q := by rw [hA g c]
          _ = c • (g • Quotient.out q) := by rw [mul_smul]
          _ = c • Quotient.out q := by rw [hgout]
      apply hstab y
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    have hsupp : ∀ y ∈ g.1.1.support, y ∈ q0.orbit := by
      intro y hy
      by_contra hy0
      exact (Equiv.Perm.mem_support.mp hy) (hfix y hy0)
    let j : ↥g.1.1.support → q0.orbit := fun y =>
      ⟨y.1, hsupp y.1 y.2⟩
    have hj : Function.Injective j := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : q0.orbit => z.1) hxy
    have hcard : g.1.1.support.card ≤ 2 := by
      calc
        g.1.1.support.card = Fintype.card ↥g.1.1.support :=
          (Fintype.card_coe _).symm
        _ ≤ Fintype.card q0.orbit := Fintype.card_le_of_injective j hj
        _ = Nat.card q0.orbit := Nat.card_eq_fintype_card.symm
        _ = 2 := hq0
    have hg1 : g.1 = 1 :=
      alternating_eq_one_of_support_card_le_two g.1 hcard
    have hg : g = 1 := by
      apply Subtype.ext
      exact hg1
    dsimp [g] at hg
    exact (inv_mul_eq_one.mp hg).symm
  calc
    Nat.card ↥A = Fintype.card ↥A := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ((q : Q') → q.1.orbit) :=
      Fintype.card_le_of_injective f hf
    _ = Nat.card ((q : Q') → q.1.orbit) :=
      Nat.card_eq_fintype_card.symm

/-- If every Sylow three-subgroup has order twenty-seven and center of order
three, every elementary abelian three-subgroup has order at most nine. -/
public theorem elementaryAbelian_card_le_nine_of_sylow_card_center
    {G : Type*} [Group G] [Finite G]
    (hSylow : ∀ P : Sylow 3 G,
      Nat.card (P : Subgroup G) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup G)) = 3)
    (A : Subgroup G) (hA : IsElementaryAbelian A 3) :
    Nat.card A ≤ 9 := by
  have hAp : IsPGroup 3 A := by
    intro a
    rcases hA.2 a with h1 | h3
    · exact ⟨0, by rw [pow_zero, pow_one, orderOf_eq_one_iff.mp h1]⟩
    · exact ⟨1, by rw [pow_one, ← h3, pow_orderOf_eq_one]⟩
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hP := hSylow P
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hAp
  have hcardLe : Nat.card A ≤ Nat.card (P : Subgroup G) :=
    Nat.le_of_dvd (by rw [hP.1]; norm_num) (Subgroup.card_dvd_of_le hAP)
  have hrLe : r ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    rw [← hr]
    simpa [hP.1] using hcardLe
  by_cases hr2 : r ≤ 2
  · calc
      Nat.card A = 3 ^ r := hr
      _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hr2
      _ = 9 := by norm_num
  · have hr3 : r = 3 := by omega
    have hcardEq : Nat.card A = Nat.card (P : Subgroup G) := by
      rw [hr, hr3, hP.1]
      norm_num
    have hEq : A = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hAP hcardEq.ge
    have hcomm : IsMulCommutative (P : Subgroup G) := by
      rw [← hEq]
      exact hA.1
    have hcenterTop : Subgroup.center (P : Subgroup G) = ⊤ :=
      Subgroup.center_eq_top_iff.mpr hcomm
    have hcenterCard : Nat.card (Subgroup.center (P : Subgroup G)) = 27 := by
      rw [hcenterTop, Subgroup.card_top, hP.1]
    omega

/-- In a central threefold extension of an alternating group, an order-three
quotient element and the center generate an elementary abelian subgroup of
order nine. -/
public theorem exists_central_three_lift_witness
    {K : Type} [Group K] [Finite K]
    (n : Nat) (hn : 5 ≤ n)
    (f : K →* alternatingGroup (Fin n))
    (hsurj : Function.Surjective f)
    (hker : f.ker = Subgroup.center K)
    (hkerCard : Nat.card f.ker = 3)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = 3) :
    ∃ A : Subgroup K, IsElementaryAbelian A 3 ∧ Nat.card A = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkerP : IsPGroup 3 f.ker := by
    apply IsPGroup.iff_card.mpr
    exact ⟨1, by simpa using hkerCard⟩
  obtain ⟨y, hfy, hyOrder⟩ :=
    SchurPresentation.exists_order_three_lift_of_five_le
      (H := K) n hn f hsurj hker.le hkerP a ha
  let Z : Subgroup K := f.ker
  let X : Subgroup K := Subgroup.zpowers y
  have hZcard : Nat.card Z = 3 := by simpa [Z] using hkerCard
  have hXcard : Nat.card X = 3 := by simp [X, Nat.card_zpowers, hyOrder]
  have hyNotKer : y ∉ Z := by
    intro hyZ
    have : f y = 1 := MonoidHom.mem_ker.mp hyZ
    rw [hfy] at this
    have ha1 : a ≠ 1 := by
      intro haOne
      rw [haOne, orderOf_one] at ha
      omega
    exact ha1 this
  have hdisjoint : Disjoint Z X := by
    rw [disjoint_iff_inf_le]
    intro z hz
    let I : Subgroup X := Z.subgroupOf X
    have : Fact (Nat.card X).Prime := ⟨hXcard ▸ Nat.prime_three⟩
    rcases I.eq_bot_or_eq_top_of_prime_card with hI | hI
    · have hzI : (⟨z, hz.2⟩ : X) ∈ I := hz.1
      rw [hI, Subgroup.mem_bot] at hzI
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzI)
    · exfalso
      apply hyNotKer
      have hyI : (⟨y, Subgroup.mem_zpowers y⟩ : X) ∈ I := by
        rw [hI]
        exact Subgroup.mem_top _
      exact hyI
  have hcommutes : ∀ (z : Z) (x : X),
      Commute (Z.subtype z) (X.subtype x) := by
    intro z x
    have hzCenter : (z : K) ∈ Subgroup.center K := by
      rw [← hker]
      exact z.2
    exact (Subgroup.mem_center_iff.mp hzCenter (x : K)).symm
  let productHom : Z × X →* K :=
    MonoidHom.noncommCoprod Z.subtype X.subtype hcommutes
  have hproductInjective : Function.Injective productHom := by
    change Function.Injective
      (MonoidHom.noncommCoprod Z.subtype X.subtype hcommutes)
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Z.subtype_injective, X.subtype_injective, ?_⟩
    simpa using hdisjoint
  have hZX : IsElementaryAbelian (Z × X) 3 := by
    constructor
    · rw [isMulCommutative_iff]
      intro u v
      apply Prod.ext
      · apply Subtype.ext
        have hu : (u.1 : K) ∈ Subgroup.center K := by
          rw [← hker]
          exact u.1.2
        exact (Subgroup.mem_center_iff.mp hu (v.1 : K)).symm
      · apply Subtype.ext
        change (u.2 : K) * (v.2 : K) = (v.2 : K) * (u.2 : K)
        rcases u.2.2 with ⟨i, hi⟩
        rcases v.2.2 with ⟨j, hj⟩
        rw [← hi, ← hj]
        exact (Commute.refl y).zpow_zpow i j
    · intro u
      have hzDvd : orderOf u.1 ∣ 3 := by
        rw [← hZcard]
        exact orderOf_dvd_natCard u.1
      have hxDvd : orderOf u.2 ∣ 3 := by
        rw [← hXcard]
        exact orderOf_dvd_natCard u.2
      have hu3 : u ^ 3 = 1 := by
        apply Prod.ext
        · have hzPow : u.1 ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hzDvd
          exact hzPow
        · have hxPow : u.2 ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hxDvd
          exact hxPow
      exact (Nat.dvd_prime Nat.prime_three).mp
        (orderOf_dvd_of_pow_eq_one hu3)
  let A : Subgroup K := productHom.range
  have htop : IsElementaryAbelian (⊤ : Subgroup (Z × X)) 3 := by
    constructor
    · rw [isMulCommutative_iff]
      intro u v
      apply Subtype.ext
      exact isMulCommutative_iff.mp hZX.1 u.1 v.1
    · intro u
      simpa [Subgroup.orderOf_coe] using hZX.2 u.1
  have hEA : IsElementaryAbelian A 3 := by
    have hmap := isElementaryAbelian_map_of_injective 3
      (⊤ : Subgroup (Z × X)) htop productHom hproductInjective
    rw [← MonoidHom.range_eq_map] at hmap
    exact hmap
  refine ⟨A, hEA, ?_⟩
  have hcardRange : Nat.card A = Nat.card (Z × X) :=
      (Nat.card_congr (Equiv.ofInjective productHom hproductInjective)).symm
  calc
    Nat.card A = Nat.card (Z × X) := hcardRange
    _ = Nat.card Z * Nat.card X := Nat.card_prod _ _
    _ = 9 := by rw [hZcard, hXcard]

/-- An elementary abelian `p`-subgroup of a finite group has order a power
of `p`. -/
public lemma ea_card_pow {p : Nat} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hA : IsElementaryAbelian G p) :
    ∃ r : Nat, Nat.card G = p ^ r := by
  have hP : IsPGroup p G := ea_is_pGroup hp hA
  have : Fact p.Prime := ⟨hp⟩
  exact (IsPGroup.iff_card.mp hP)


open MulAction

/-- The size of any orbit of `A` on the point set is a power of `p`. -/
lemma orbit_card_is_power {n p : Nat} (hp : p.Prime)
    (A : Subgroup (alternatingGroup (Fin n))) (hA : IsElementaryAbelian ↥A p)
    (x : Fin n) : ∃ e : Nat, Nat.card (MulAction.orbit ↥A x) = p ^ e := by
  rcases ea_card_pow hp hA with ⟨r, hr⟩
  letI : Fintype ↥A := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit ↥A x) := Fintype.ofFinite _
  letI : Fintype ↥(MulAction.stabilizer ↥A x) := Fintype.ofFinite _
  -- |orbit x| · |stabilizer x| = |A| = p^r
  have hmain := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥A x
  have hm : Nat.card (MulAction.orbit ↥A x) * Nat.card ↥(MulAction.stabilizer ↥A x) =
      Nat.card ↥A := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hmain
  -- orbit divides p^r
  have hdvd : Nat.card (MulAction.orbit ↥A x) ∣ p ^ r := by
    rw [hr] at hm
    refine ⟨Nat.card ↥(MulAction.stabilizer ↥A x), ?_⟩
    exact hm.symm
  -- orbit is nonempty
  have horb : Nonempty (MulAction.orbit ↥A x) := ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  have hpos : Nat.card (MulAction.orbit ↥A x) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_pos_iff.mpr horb).ne'
  -- every prime divisor of the orbit size is `p`
  refine ⟨(Nat.card (MulAction.orbit ↥A x)).primeFactorsList.length, ?_⟩
  exact Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {q} hq hqd => by
    have hqp : q ∣ p := hq.dvd_of_dvd_pow (dvd_trans hqd hdvd)
    rcases hp.eq_one_or_self_of_dvd q hqp with hq1 | hqp_eq
    · exfalso
      exact hq.ne_one hq1
    · exact hqp_eq)

-- |q.orbit| equals the orbit of the representative `q.out`.
lemma orbit_eq_orbit_out {n : Nat} (A : Subgroup (alternatingGroup (Fin n)))
    (q : MulAction.orbitRel.Quotient ↥A (Fin n)) :
    q.orbit = MulAction.orbit ↥A (Quotient.out q) := by
  ext y
  rw [MulAction.orbitRel.Quotient.mem_orbit]
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro hy
    have hy' : Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) y =
        Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) (Quotient.out q) := by
      rw [hy]
      exact (Quotient.out_eq' q).symm
    exact MulAction.mem_orbit_iff.mpr
      (Quotient.exact (s := MulAction.orbitRel ↥A (Fin n)) hy')
  · intro h
    rw [← Quotient.out_eq' q]
    exact Quotient.sound (s := MulAction.orbitRel ↥A (Fin n)) h

/-- The action of `A` on the point set is faithful. -/
lemma action_faithful {n : Nat} (A : Subgroup (alternatingGroup (Fin n))) :
    Function.Injective (fun a : ↥A => (a • · : Fin n → Fin n)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro y
  exact congrFun hab y

-- the composite `b⁻¹ a` fixes `q.out` when `a` and `b` agree there
lemma smul_out_eq_of_agree {n : Nat} {A : Subgroup (alternatingGroup (Fin n))}
    {q : MulAction.orbitRel.Quotient ↥A (Fin n)}
    {a b : ↥A} (hab : a • Quotient.out q = b • Quotient.out q) :
    (b⁻¹ * a) • Quotient.out q = Quotient.out q := by
  calc
    (b⁻¹ * a) • Quotient.out q = b⁻¹ • (a • Quotient.out q) := by rw [mul_smul]
    _ = b⁻¹ • (b • Quotient.out q) := by rw [hab]
    _ = Quotient.out q := by
      rw [← mul_smul, inv_mul_cancel, one_smul]

/-- |A| ≤ the product of the orbit sizes: embed `A` into `∏_q (q.orbit)`. -/
lemma card_le_prod_orbit {n : Nat} (A : Subgroup (alternatingGroup (Fin n)))
    (hA : ∀ a b : ↥A, a * b = b * a)
    [Fintype ↥A] [Fintype (MulAction.orbitRel.Quotient ↥A (Fin n))] :
    Nat.card ↥A ≤
      ∏ q : MulAction.orbitRel.Quotient ↥A (Fin n), Nat.card (q.orbit) := by
  classical
  let Q := MulAction.orbitRel.Quotient ↥A (Fin n)
  have : ∀ q : Q, Fintype (q.orbit) := fun q => Fintype.ofFinite _
  -- the embedding f : A ↪ ∏_q q.orbit
  let f : ↥A → (q : Q) → q.orbit := fun a q =>
    ⟨a • Quotient.out q, by
      rw [MulAction.orbitRel.Quotient.mem_orbit]
      calc
        Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) (a • Quotient.out q) =
            Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) (Quotient.out q) := by
          apply Quotient.sound (s := MulAction.orbitRel ↥A (Fin n))
          exact ⟨a, rfl⟩
        _ = q := Quotient.out_eq' q⟩
  -- injective
  have hf : Function.Injective f := by
    intro a b hab
    have hq : ∀ q : Q, a • Quotient.out q = b • Quotient.out q := by
      intro q
      exact congrArg Subtype.val (congrFun hab q)
    apply action_faithful A
    funext y
    let q : Q := Quotient.mk'' y
    have hout : y ∈ MulAction.orbit ↥A (Quotient.out q) := by
      rw [MulAction.mem_orbit_iff]
      exact Quotient.exact (s := MulAction.orbitRel ↥A (Fin n)) (by
        calc
          Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) y = q := by rfl
          _ = Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) (Quotient.out q) :=
            (Quotient.out_eq' q).symm)
    have hfixq : (b⁻¹ * a) • Quotient.out q = Quotient.out q :=
        smul_out_eq_of_agree (hq q)
    have hfix : (b⁻¹ * a) • y = y :=
      stabilizer_fixes_orbit hA hfixq y hout
    calc
      a • y = b • (b⁻¹ • (a • y)) := by
        rw [← mul_smul, mul_inv_cancel, one_smul]
      _ = b • ((b⁻¹ * a) • y) := by rw [mul_smul]
      _ = b • y := by rw [hfix]
  -- |A| ≤ ∏|q.orbit|
  calc
    Nat.card ↥A = Fintype.card ↥A := Nat.card_eq_fintype_card
    _ ≤ ∏ q : Q, Fintype.card (q.orbit) := by
      calc
        Fintype.card ↥A ≤ Fintype.card ((q : Q) → q.orbit) :=
          Fintype.card_le_of_injective f hf
        _ = ∏ q : Q, Fintype.card (q.orbit) := Fintype.card_pi
    _ = ∏ q : Q, Nat.card (q.orbit) := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [Nat.card_eq_fintype_card]

/-- Every elementary abelian `p`-subgroup of the alternating group on `Fin n`
(odd `p`) has order at most `p^(⌊n/p⌋)`. -/
public theorem ea_subgroup_order_le (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (alternatingGroup (Fin n)))
    (hA : IsElementaryAbelian ↥A p) :
    Nat.card ↥A ≤ p ^ (n / p) := by
  rcases ea_card_pow hp hA with ⟨r, hr⟩
  classical
  let Q := MulAction.orbitRel.Quotient ↥A (Fin n)
  haveI : Fintype Q := Fintype.ofFinite _
  haveI : Fintype ↥A := Fintype.ofFinite _
  -- 1. |A| = p^r ≤ ∏_q |q.orbit|
  have hcom : ∀ a b : ↥A, a * b = b * a := isMulCommutative_iff.mp hA.1
  have hprod : Nat.card ↥A ≤ ∏ q : Q, Nat.card (q.orbit) := card_le_prod_orbit A hcom
  have hA_le : p ^ r ≤ ∏ q : Q, Nat.card (q.orbit) := by
    rw [← hr]
    exact hprod
  -- 2. each orbit size is a power of p
  let e : Q → Nat := fun q => Classical.choose (orbit_card_is_power hp A hA (Quotient.out q))
  have he : ∀ q : Q, Nat.card (q.orbit) = p ^ e q := by
    intro q
    rw [orbit_eq_orbit_out A q]
    exact Classical.choose_spec (orbit_card_is_power hp A hA (Quotient.out q))
  -- 3. the total number of points is n
  have hsum_le : (∑ q : Q, Nat.card (q.orbit)) ≤ n := by
    -- Fin n ≃ Σ_q q.orbit — disjoint union of the orbits
    have efin : (Σ q : Q, q.orbit) ≃ Fin n :=
      Equiv.ofBijective (fun x : Σ q : Q, q.orbit => x.2.1)
        ⟨by
          intro x y hxy
          rcases x with ⟨q, a⟩
          rcases y with ⟨r, b⟩
          change a.1 = b.1 at hxy
          have hqr : q = r := calc
            q = Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) a.1 :=
              (MulAction.orbitRel.Quotient.mem_orbit.mp a.2).symm
            _ = Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) b.1 := by rw [hxy]
            _ = r := MulAction.orbitRel.Quotient.mem_orbit.mp b.2
          apply Sigma.ext
          · exact hqr
          · subst r
            exact heq_of_eq (Subtype.ext (show (a : Fin n) = (b : Fin n) from hxy)),
         by
          intro y
          exact ⟨⟨Quotient.mk'' (s₁ := MulAction.orbitRel ↥A (Fin n)) y,
            ⟨y, (MulAction.orbitRel.Quotient.mem_orbit.mpr rfl)⟩⟩, rfl⟩⟩
    have hsum : (∑ q : Q, Nat.card (q.orbit)) = n := by
      calc
        (∑ q : Q, Nat.card (q.orbit)) = ∑ q : Q, Fintype.card (q.orbit) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Nat.card_eq_fintype_card]
        _ = Fintype.card (Σ q : Q, q.orbit) := by rw [Fintype.card_sigma]
        _ = Fintype.card (Fin n) := Fintype.card_congr efin
        _ = n := Fintype.card_fin n
    omega
  -- 4. rank bound: r ≤ Σ e_q ≤ Σ |O_q|/p ≤ n/p
  have hprod' : p ^ r ≤ ∏ q : Q, p ^ e q := by
    rw [Finset.prod_congr rfl (fun q hq => by rw [← he q])]
    exact hA_le
  have hpow_eq : p ^ r ≤ p ^ (∑ q : Q, e q) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact hprod'
  have hrank : r ≤ ∑ q : Q, e q := by
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow_eq
  -- each e_q ≤ |O_q|/p
  have h_e_le : ∀ q : Q, e q ≤ Nat.card (q.orbit) / p := by
    intro q
    rcases lt_or_eq_of_le (Nat.zero_le (e q)) with he_pos | he_zero
    · -- 0 < e q — nontrivial orbit: e q ≤ p^(e q)/p = |O_q|/p
      have hrq : 1 ≤ e q := by omega
      have hsize : Nat.card (q.orbit) = p ^ e q := he q
      rw [hsize]
      exact rank_le_size_div_p hp.one_lt hrq
    · -- 0 = e q — trivial orbit: e q = 0
      rw [← he_zero]
      exact Nat.zero_le _
  have hsum_rank : (∑ q : Q, e q) ≤ (∑ q : Q, Nat.card (q.orbit) / p) := by
    exact Finset.sum_le_sum (fun q hq => h_e_le q)
  have hdiv : (∑ q : Q, Nat.card (q.orbit) / p) ≤ (∑ q : Q, Nat.card (q.orbit)) / p := by
    -- sum of floors ≤ floor of sum: induct on the finite sum
    let s : Finset Q := Finset.univ
    have hmain : ∀ t : Finset Q,
        (∑ q ∈ t, Nat.card (q.orbit) / p) ≤ (∑ q ∈ t, Nat.card (q.orbit)) / p := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t hat ih =>
          rw [Finset.sum_insert hat]
          rw [Finset.sum_insert hat]
          calc
            Nat.card (a.orbit) / p + (∑ q ∈ t, Nat.card (q.orbit) / p)
                ≤ Nat.card (a.orbit) / p + (∑ q ∈ t, Nat.card (q.orbit)) / p :=
              add_le_add_right ih (Nat.card (a.orbit) / p)
            _ ≤ (Nat.card (a.orbit) + ∑ q ∈ t, Nat.card (q.orbit)) / p := by
              rw [Nat.add_div hp.pos]
              omega
    simpa using hmain s
  have hsum_div : (∑ q : Q, Nat.card (q.orbit)) / p ≤ n / p := by
    exact Nat.div_le_div_right hsum_le
  have hrank_le : r ≤ n / p := by
    calc
      r ≤ ∑ q : Q, e q := hrank
      _ ≤ (∑ q : Q, Nat.card (q.orbit) / p) := hsum_rank
      _ ≤ (∑ q : Q, Nat.card (q.orbit)) / p := hdiv
      _ ≤ n / p := hsum_div
  -- 5. conclusion
  rw [hr]
  exact Nat.pow_le_pow_right (n := p) hp.pos hrank_le

/-- `G` has elementary-abelian `p`-rank exactly `r`: the order `p^r` is
attained, and no elementary abelian `p`-subgroup has larger order. -/
public def HasPRank (G : Type*) [Group G] [Finite G]
    (p r : Nat) : Prop :=
  (∃ A : Subgroup G,
      IsElementaryAbelian A p ∧ Nat.card A = p ^ r) ∧
    ∀ A : Subgroup G,
      IsElementaryAbelian A p → Nat.card A ≤ p ^ r

/-- The witness and upper-bound specification of elementary abelian rank.
This lets importing modules compare rank conventions without exposing the
implementation of `HasPRank`. -/
public theorem hasPRank_iff {G : Type*} [Group G] [Finite G] {p r : Nat} :
    HasPRank G p r ↔
      (∃ A : Subgroup G, IsElementaryAbelian A p ∧ Nat.card A = p ^ r) ∧
        ∀ A : Subgroup G, IsElementaryAbelian A p → Nat.card A ≤ p ^ r :=
  Iff.rfl

/-- Package an explicit elementary-abelian witness together with a matching
upper bound into the exact-rank predicate. -/
public lemma hasPRank_of_witness_of_upper_bound
    {G : Type*} [Group G] [Finite G] (p r : Nat)
    (A : Subgroup G) (hA : IsElementaryAbelian A p)
    (hAcard : Nat.card A = p ^ r)
    (hupper : ∀ B : Subgroup G,
      IsElementaryAbelian B p → Nat.card B ≤ p ^ r) :
    HasPRank G p r := by
  exact ⟨⟨A, hA, hAcard⟩, hupper⟩

/-- The odd-prime exact rank of the alternating group in a degree divisible
by the prime is attained by disjoint standard cycles. -/
public theorem alternating_hasPRank_of_mul_eq
    (r p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPRank (alternatingGroup (Fin (r * p))) p r := by
  obtain ⟨A, hA, hAcard⟩ :=
    exists_oddPrimeCycleProduct_witness r p hp hp2
  apply hasPRank_of_witness_of_upper_bound p r A hA hAcard
  intro B hB
  have h := ea_subgroup_order_le (r * p) p hp hp2 B hB
  rw [Nat.mul_div_left r hp.pos] at h
  exact h

public theorem alternating_hasPRank_of_odd_prime
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPRank (alternatingGroup (Fin n)) p (n / p) := by
  by_cases hr : n / p = 0
  · rw [hr]
    let A : Subgroup (alternatingGroup (Fin n)) := ⊥
    have hA : IsElementaryAbelian A p := by
      constructor
      · rw [isMulCommutative_iff]
        intro a b
        have ha : (a : alternatingGroup (Fin n)) = 1 :=
          Subgroup.mem_bot.mp a.2
        have hb : (b : alternatingGroup (Fin n)) = 1 :=
          Subgroup.mem_bot.mp b.2
        apply Subtype.ext
        change (a : alternatingGroup (Fin n)) * (b : alternatingGroup (Fin n)) =
          (b : alternatingGroup (Fin n)) * (a : alternatingGroup (Fin n))
        rw [ha, hb]
      · intro a
        left
        apply orderOf_eq_one_iff.mpr
        apply Subtype.ext
        exact Subgroup.mem_bot.mp a.2
    apply hasPRank_of_witness_of_upper_bound p 0 A hA
    · simpa [A]
    · intro B hB
      have h := ea_subgroup_order_le n p hp hp2 B hB
      simpa [hr] using h
  · let r := n / p
    have hrp : r * p ≤ n := by
      exact Nat.div_mul_le_self n p
    obtain ⟨A, hA, hAcard⟩ :=
      exists_oddPrimeCycleProduct_witness_of_mul_le n r p hp hp2 hrp
    apply hasPRank_of_witness_of_upper_bound p r A hA hAcard
    exact ea_subgroup_order_le n p hp hp2

public theorem alternating_hasPRank_two_lower_bound_of_mul_le
    (n r : Nat) (hr : 4 * r ≤ n) :
    ∃ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (2 * r) := by
  exact exists_evenKleinFourProduct_witness_of_mul_le n r hr

public theorem alternating_hasPRank_two_lower_bound
    (n : Nat) :
    ∃ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 ∧ Nat.card A = 2 ^ (2 * (n / 4)) := by
  apply alternating_hasPRank_two_lower_bound_of_mul_le n (n / 4)
  omega

private theorem __ch5_proposition_5_2_10_even_orbit_rank_after_delete_two
    (n exponentSum orbitSum : Nat)
    (hrank : 2 * exponentSum ≤ orbitSum) (hsize : 2 + orbitSum ≤ n) :
    exponentSum ≤ 2 * (n / 4) := by
  omega

private theorem __ch5_proposition_5_2_10_even_orbit_rank_of_quarter_sum
    (n exponentSum quarterSum orbitSum : Nat)
    (hrank : exponentSum ≤ 2 * quarterSum)
    (hquarter : 4 * quarterSum ≤ orbitSum) (hsize : orbitSum ≤ n) :
    exponentSum ≤ 2 * (n / 4) := by
  have hq : quarterSum ≤ n / 4 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mpr (by omega)
  omega

/-- Every elementary abelian `2`-subgroup of the alternating group has
order at most the four-point-block bound. -/
public theorem alternating_two_ea_subgroup_order_le
    (n : Nat) (A : Subgroup (alternatingGroup (Fin n)))
    (hA : IsElementaryAbelian A 2) :
    Nat.card A ≤ 2 ^ (2 * (n / 4)) := by
  rcases ea_card_pow Nat.prime_two hA with ⟨r, hr⟩
  classical
  let Q := MulAction.orbitRel.Quotient ↥A (Fin n)
  haveI : Fintype Q := Fintype.ofFinite _
  haveI : Fintype ↥A := Fintype.ofFinite _
  have hcomm : ∀ a b : ↥A, a * b = b * a :=
    isMulCommutative_iff.mp hA.1
  let exponent : Q → Nat := fun q =>
    Classical.choose (orbit_card_is_power Nat.prime_two A hA (Quotient.out q))
  have horbit : ∀ q : Q, Nat.card q.orbit = 2 ^ exponent q := by
    intro q
    rw [orbit_eq_orbit_out A q]
    exact Classical.choose_spec
      (orbit_card_is_power Nat.prime_two A hA (Quotient.out q))
  have hsum : (∑ q : Q, Nat.card q.orbit) = n := by
    simpa [Q] using
      (sum_card_orbitRel_quotient (G := ↥A) (α := Fin n))
  by_cases htwo : ∃ q : Q, Nat.card q.orbit = 2
  · obtain ⟨q0, hq0⟩ := htwo
    let Q' := {q : Q // q ≠ q0}
    letI : Fintype Q' := Fintype.ofFinite _
    have hcard := card_le_card_orbit_evaluation_away_of_card_eq_two
      A hcomm q0 hq0
    change Nat.card ↥A ≤ Nat.card ((q : Q') → q.1.orbit) at hcard
    have hpow : 2 ^ r ≤ 2 ^ (∑ q : Q', exponent q.1) := by
      rw [← hr]
      calc
        Nat.card ↥A ≤ Nat.card ((q : Q') → q.1.orbit) := hcard
        _ = ∏ q : Q', Nat.card q.1.orbit := Nat.card_pi
        _ = ∏ q : Q', 2 ^ exponent q.1 := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [horbit q.1]
        _ = 2 ^ (∑ q : Q', exponent q.1) := by
          rw [Finset.prod_pow_eq_pow_sum]
    have hrank : r ≤ ∑ q : Q', exponent q.1 :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    have hterm : ∀ q : Q', 2 * exponent q.1 ≤ Nat.card q.1.orbit := by
      intro q
      by_cases he0 : exponent q.1 = 0
      · simp [he0]
      · have hepos : 1 ≤ exponent q.1 := by omega
        have he := rank_le_size_div_p (p := 2) (by omega) hepos
        rw [horbit q.1]
        have hdiv := Nat.div_mul_le_self (2 ^ exponent q.1) 2
        omega
    have htwice :
        2 * (∑ q : Q', exponent q.1) ≤ ∑ q : Q', Nat.card q.1.orbit := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun q hq => hterm q
    have hsize : 2 + (∑ q : Q', Nat.card q.1.orbit) ≤ n := by
      have herase :
          (∑ q ∈ Finset.univ.erase q0, Nat.card q.orbit) =
            ∑ q : Q', Nat.card q.1.orbit := by
        exact Finset.sum_subtype (Finset.univ.erase q0) (by simp) fun q =>
          Nat.card q.orbit
      have hall := Finset.sum_erase_add (Finset.univ : Finset Q)
        (fun q => Nat.card q.orbit) (Finset.mem_univ q0)
      have hsizeEq : 2 + (∑ q : Q', Nat.card q.1.orbit) = n := by
        calc
          2 + (∑ q : Q', Nat.card q.1.orbit) =
              (∑ q ∈ Finset.univ.erase q0, Nat.card q.orbit) +
                Nat.card q0.orbit := by rw [herase, hq0, Nat.add_comm]
          _ = ∑ q : Q, Nat.card q.orbit := hall
          _ = n := hsum
      exact hsizeEq.le
    have hexponent := __ch5_proposition_5_2_10_even_orbit_rank_after_delete_two n
      (∑ q : Q', exponent q.1) (∑ q : Q', Nat.card q.1.orbit)
      htwice hsize
    rw [hr]
    exact Nat.pow_le_pow_right (by omega) (hrank.trans hexponent)
  · have hcard := card_le_prod_orbit A hcomm
    have hpow : 2 ^ r ≤ 2 ^ (∑ q : Q, exponent q) := by
      rw [← hr]
      calc
        Nat.card ↥A ≤ ∏ q : Q, Nat.card q.orbit := hcard
        _ = ∏ q : Q, 2 ^ exponent q := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [horbit q]
        _ = 2 ^ (∑ q : Q, exponent q) := by
          rw [Finset.prod_pow_eq_pow_sum]
    have hrank : r ≤ ∑ q : Q, exponent q :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    have hterm : ∀ q : Q,
        exponent q ≤ 2 * (Nat.card q.orbit / 4) := by
      intro q
      by_cases he0 : exponent q = 0
      · simp [he0]
      by_cases he1 : exponent q = 1
      · exfalso
        apply htwo
        refine ⟨q, ?_⟩
        rw [horbit q, he1]
        norm_num
      · have he2 : 2 ≤ exponent q := by omega
        have he := rank_le_size_div_p (p := 2) (by omega)
          (r := exponent q) (by omega)
        have hdiv : 4 ∣ 2 ^ exponent q := pow_dvd_pow 2 he2
        obtain ⟨k, hk⟩ := hdiv
        rw [horbit q, hk]
        omega
    have hexponent :
        (∑ q : Q, exponent q) ≤ 2 * (∑ q : Q, Nat.card q.orbit / 4) := by
      calc
        (∑ q : Q, exponent q) ≤
            ∑ q : Q, 2 * (Nat.card q.orbit / 4) :=
          Finset.sum_le_sum fun q hq => hterm q
        _ = 2 * (∑ q : Q, Nat.card q.orbit / 4) := by
          rw [Finset.mul_sum]
    have hquarter :
        4 * (∑ q : Q, Nat.card q.orbit / 4) ≤
          ∑ q : Q, Nat.card q.orbit := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun q hq => by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (Nat.card q.orbit) 4
    have hbound := __ch5_proposition_5_2_10_even_orbit_rank_of_quarter_sum n
      (∑ q : Q, exponent q) (∑ q : Q, Nat.card q.orbit / 4)
      (∑ q : Q, Nat.card q.orbit) hexponent hquarter hsum.le
    rw [hr]
    exact Nat.pow_le_pow_right (by omega) (hrank.trans hbound)

public theorem alternating_hasPRank_two_of_upper_bound
    (n : Nat)
    (hupper : ∀ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 → Nat.card A ≤ 2 ^ (2 * (n / 4))) :
    HasPRank (alternatingGroup (Fin n)) 2 (2 * (n / 4)) := by
  obtain ⟨A, hA, hAcard⟩ := alternating_hasPRank_two_lower_bound n
  exact hasPRank_of_witness_of_upper_bound 2 (2 * (n / 4)) A hA hAcard hupper

/-- The exact elementary-abelian `2`-rank of the alternating group. -/
public theorem alternating_hasPRank_two (n : Nat) :
    HasPRank (alternatingGroup (Fin n)) 2 (2 * (n / 4)) := by
  exact alternating_hasPRank_two_of_upper_bound n
    (alternating_two_ea_subgroup_order_le n)

/-- When the center is trivial, the displayed center quotient identifies the
group itself with the alternating quotient. -/
private def __ch5_proposition_5_2_10_centerlessAlternatingEquiv
    {K : Type*} [Group K] [Finite K]
    (n : Nat) (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    K ≃* alternatingGroup (Fin n) := by
  let f : K →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  apply MulEquiv.ofBijective f
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff]
    change (e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center K))).ker = ⊥
    rw [MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' (Subgroup.center K)) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk', hcenter]
  · exact e.surjective.comp
      (QuotientGroup.mk'_surjective (Subgroup.center K))

private theorem __ch5_proposition_5_2_10_hasPRank_of_mulEquiv
    {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (p r : Nat) (e : G ≃* G') (hG : HasPRank G p r) :
    HasPRank G' p r := by
  constructor
  · obtain ⟨A, hA, hAcard⟩ := hG.1
    let A' : Subgroup G' := A.map e.toMonoidHom
    refine ⟨A', PRank.isElementaryAbelian_map_of_injective p A hA
      e.toMonoidHom e.injective, ?_⟩
    have hcard : Nat.card A' = Nat.card A := by
      exact Subgroup.card_map_of_injective
        (K := A) (f := e.toMonoidHom) e.injective
    rw [hcard, hAcard]
  · intro A' hA'
    let A : Subgroup G := A'.map e.symm.toMonoidHom
    have hA : IsElementaryAbelian A p :=
      PRank.isElementaryAbelian_map_of_injective p A' hA'
        e.symm.toMonoidHom e.symm.injective
    have hle := hG.2 A hA
    have hcard : Nat.card A = Nat.card A' := by
      exact Subgroup.card_map_of_injective
        (K := A') (f := e.symm.toMonoidHom) e.symm.injective
    rwa [hcard] at hle

/-- Transport an exact elementary-abelian rank statement across a group
equivalence. -/
public theorem centerless_alternating_hasPRank_of_odd_prime
    {K : Type*} [Group K] [Finite K]
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K p (n / p) := by
  apply __ch5_proposition_5_2_10_hasPRank_of_mulEquiv p (n / p)
    (__ch5_proposition_5_2_10_centerlessAlternatingEquiv n hcenter e).symm
  exact alternating_hasPRank_of_odd_prime n p hp hp2

public theorem proposition_5_2_10_a
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K p (n / p) := by
  exact centerless_alternating_hasPRank_of_odd_prime n p hp hp2 hcenter e

public theorem centerless_alternating_hasPRank_of_two_of_upper_bound
    {K : Type*} [Group K] [Finite K]
    (n : Nat) (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hupper : ∀ A : Subgroup (alternatingGroup (Fin n)),
      IsElementaryAbelian A 2 → Nat.card A ≤ 2 ^ (2 * (n / 4))) :
    HasPRank K 2 (2 * (n / 4)) := by
  apply __ch5_proposition_5_2_10_hasPRank_of_mulEquiv 2 (2 * (n / 4))
    (__ch5_proposition_5_2_10_centerlessAlternatingEquiv n hcenter e).symm
  exact alternating_hasPRank_two_of_upper_bound n hupper

/-- Proposition 5.2.10(b): the centerless alternating case has exact two-rank. -/
public theorem centerless_alternating_hasPRank_two
    {K : Type*} [Group K] [Finite K]
    (n : Nat) (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K 2 (2 * (n / 4)) := by
  apply __ch5_proposition_5_2_10_hasPRank_of_mulEquiv 2 (2 * (n / 4))
    (__ch5_proposition_5_2_10_centerlessAlternatingEquiv n hcenter e).symm
  exact alternating_hasPRank_two n

public theorem proposition_5_2_10_b
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K 2 (2 * (n / 4)) := by
  exact centerless_alternating_hasPRank_two n hcenter e

/-- Proposition 5.2.10(c), with the source condition `K ∈ 𝒦₃` made
explicit as three-primary center. -/
public theorem proposition_5_2_10_c
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (hcenterP : IsPGroup 3 (Subgroup.center K))
    (hthree : 3 ∣ Nat.card (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K 3 2 := by
  have hnExceptional := three_dvd_center_forces_exceptional_degree n hn e hthree
  rcases hnExceptional with hn6 | hn7
  · subst n
    let : IsQuasisimple (alternatingGroup (Fin 6)) :=
      SchurPresentation.alternatingGroup_isQuasisimple 1
    have hcenterCard := three_primary_exceptional_center_card_eq_three
      6 e (Or.inl rfl) hcenterP hthree
    obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering 6 e
    have hfkerCard : Nat.card f.toMonoidHom.ker = 3 := by
      rw [hfker]
      exact hcenterCard
    constructor
    · exact exists_central_three_lift_witness 6 (by norm_num)
        f.toMonoidHom f.surjective hfker hfkerCard
        SchurPresentation.Theorem523BaseNine.a6X
        SchurPresentation.Theorem523BaseNine.a6X_order
    · intro A hA
      have hupper := elementaryAbelian_card_le_nine_of_sylow_card_center
        (tripleCoverA6_sylow3 f hfkerCard) A hA
      simpa using hupper
  · subst n
    let : IsQuasisimple (alternatingGroup (Fin 7)) :=
      SchurPresentation.alternatingGroup_isQuasisimple 2
    have hcenterCard := three_primary_exceptional_center_card_eq_three
      7 e (Or.inr rfl) hcenterP hthree
    obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering 7 e
    have hfkerCard : Nat.card f.toMonoidHom.ker = 3 := by
      rw [hfker]
      exact hcenterCard
    constructor
    · exact exists_central_three_lift_witness 7 (by norm_num)
        f.toMonoidHom f.surjective hfker hfkerCard
        SchurPresentation.Theorem523BaseNine.a7X
        SchurPresentation.Theorem523BaseNine.a7X_order
    · intro A hA
      have hupper := elementaryAbelian_card_le_nine_of_sylow_card_center
        (tripleCoverA7_sylow3 f hfkerCard) A hA
      simpa using hupper



/-- The lower-bound half of Proposition 5.2.10(d), obtained from the product
of regular eight-point quotient blocks and the central involution. -/
public theorem doubleCover_hasPRank_two_lower_bound
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (hcenterP : IsPGroup 2 (Subgroup.center K))
    (htwo : 2 ∣ Nat.card (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    ∃ A : Subgroup K, IsElementaryAbelian A 2 ∧
      Nat.card A = 2 ^ (3 * (n / 8) + 1) := by
  exact exists_doubleCoverEightBlockWitness n hn hcenterP htwo e


/-- Proposition 5.2.10(d): a nontrivial two-primary alternating cover has
exact elementary-abelian two-rank `3 * floor(n / 8) + 1`. -/
public theorem proposition_5_2_10_d
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (hcenterP : IsPGroup 2 (Subgroup.center K))
    (htwo : 2 ∣ Nat.card (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    HasPRank K 2 (3 * (n / 8) + 1) := by
  obtain ⟨A, hA, hAcard⟩ :=
    doubleCover_hasPRank_two_lower_bound n hn hcenterP htwo e
  apply hasPRank_of_witness_of_upper_bound 2 (3 * (n / 8) + 1) A hA hAcard
  intro B hB
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let : IsQuasisimple (alternatingGroup (Fin n)) := by
    rw [← hq]
    exact SchurPresentation.alternatingGroup_isQuasisimple q
  obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
  let ef : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := ef.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective }
  have hkerCard : Nat.card c.toMonoidHom.ker = 2 := by
    change Nat.card f'.ker = 2
    rw [hf'ker, hfker]
    exact two_primary_alternating_center_card_eq_two n hn e hcenterP htwo
  have hupper := doubleCover_ea_card_le q c hkerCard B hB
  simpa [hq] using hupper

/-- Proposition 5.2.10, final assertion: in the centerless odd-prime case,
all elementary abelian subgroups attaining the maximal rank are conjugate by
an automorphism of the ambient group. -/
public theorem proposition_5_2_10_moreover
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcenter : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (A B : Subgroup K)
    (hA : IsElementaryAbelian A p) (hB : IsElementaryAbelian B p)
    (hcardA : Nat.card A = p ^ (n / p))
    (hcardB : Nat.card B = p ^ (n / p)) :
    ∃ α : MulAut K, Subgroup.map α.toMonoidHom A = B := by
  let f := __ch5_proposition_5_2_10_centerlessAlternatingEquiv n hcenter e
  let A' : Subgroup (alternatingGroup (Fin n)) := A.map f.toMonoidHom
  let B' : Subgroup (alternatingGroup (Fin n)) := B.map f.toMonoidHom
  have hA' : IsElementaryAbelian A' p :=
    isElementaryAbelian_map_of_injective p A hA f.toMonoidHom f.injective
  have hB' : IsElementaryAbelian B' p :=
    isElementaryAbelian_map_of_injective p B hB f.toMonoidHom f.injective
  have hcardA' : Nat.card A' = p ^ (n / p) := by
    have hmap : Nat.card A' = Nat.card A := by
      exact Subgroup.card_map_of_injective
        (K := A) (f := f.toMonoidHom) f.injective
    rw [hmap, hcardA]
  have hcardB' : Nat.card B' = p ^ (n / p) := by
    have hmap : Nat.card B' = Nat.card B := by
      exact Subgroup.card_map_of_injective
        (K := B) (f := f.toMonoidHom) f.injective
    rw [hmap, hcardB]
  obtain ⟨α, hα⟩ := alternating_maximalOddSubgroups_inSameMulAutOrbit
    n p hp hp2 A' B' hA' hB' hcardA' hcardB'
  exact exists_mulAut_map_eq_of_equiv_image f A B α hα
/- END KGroup.GLS3.Chapter5.proposition_5_2_10 -/

/- BEGIN Theory.AlternatingQuasisimpleOfCenterQuotient -/
namespace GLS3.Chapter5

/-- A quasisimple subgroup whose central quotient is alternating belongs to the
alternating quasisimple family. -/
public theorem isAlternatingQuasisimple_of_centerQuotient_equiv
    {G : Type*} [Group G] [Finite G] (I : Subgroup G)
    (n : Nat) (hn : 5 ≤ n)
    (hquotient : Nonempty
      (I ⧸ Subgroup.center I ≃* alternatingGroup (Fin n)))
    (hquasisimple : IsQuasisimple I) :
    IsAlternatingQuasisimple I := by
  unfold IsAlternatingQuasisimple
  refine ⟨hquasisimple, ?_⟩
  exact isInAlt_iff_exists_center_quotient.mpr
    ⟨n, Subgroup.center I, hn, rfl, hquotient⟩

end GLS3.Chapter5
/- END Theory.AlternatingQuasisimpleOfCenterQuotient -/

/- BEGIN Theory.AutomorphismQuotientCenter -/
namespace GLS3.Chapter5

/-- The automorphism induced on the central quotient. -/
public noncomputable def automorphismQuotientCenter
    {G : Type*} [Group G] (x : MulAut G) :
    G ⧸ Subgroup.center G ≃* G ⧸ Subgroup.center G :=
  Covering.quotientMulEquivOfMapEq x (Subgroup.center G) (Subgroup.center G)
    (Subgroup.characteristic_iff_map_eq.mp inferInstance x)

public theorem automorphismQuotientCenter_mk
    {G : Type*} [Group G] (x : MulAut G) (g : G) :
    automorphismQuotientCenter x
      (QuotientGroup.mk' (Subgroup.center G) g) =
      QuotientGroup.mk' (Subgroup.center G) (x g) := by
  simp [automorphismQuotientCenter, Covering.quotientMulEquivOfMapEq]

public theorem exists_center_quotient_action
    {K : Type*} [Group K] (n : Nat)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) :
    ∃ quotientAction : MulAut (alternatingGroup (Fin n)),
      ∀ k : K,
        e (QuotientGroup.mk' (Subgroup.center K) (x k)) =
          quotientAction (e (QuotientGroup.mk' (Subgroup.center K) k)) := by
  let quotientAction : MulAut (alternatingGroup (Fin n)) :=
    e.symm.trans ((automorphismQuotientCenter x).trans e)
  refine ⟨quotientAction, ?_⟩
  intro k
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact congrArg e (automorphismQuotientCenter_mk x k).symm


end GLS3.Chapter5
/- END Theory.AutomorphismQuotientCenter -/

/- BEGIN Theory.CenterMapLeCenter -/
namespace GLS3.Chapter5

/-- The center of a subgroup whose image is centerless is killed by a
central quotient map. -/
public theorem center_map_le_center_of_image_eq_centerless
    {K Q : Type*} [Group K] [Group Q]
    (q : K →* Q) (hqker : q.ker ≤ Subgroup.center K)
    (I : Subgroup K) (S : Subgroup Q) (himage : I.map q = S)
    (s : Nat) (hs : 5 ≤ s) (eS : S ≃* alternatingGroup (Fin s)) :
    (Subgroup.center I).map I.subtype ≤ Subgroup.center K := by
  intro z hz
  obtain ⟨zi, hzi, rfl⟩ := Subgroup.mem_map.mp hz
  apply hqker
  rw [MonoidHom.mem_ker]
  have hqziS : q zi.1 ∈ S := by
    rw [← himage]
    exact Subgroup.mem_map_of_mem q zi.2
  have hzS : (⟨q zi.1, hqziS⟩ : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨yi, hyi, hqyi⟩ := Subgroup.mem_map.mp (by
      rw [himage]
      exact y.2)
    let yiI : I := ⟨yi, hyi⟩
    have hcomm : yi * zi.1 = zi.1 * yi := by
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzi yiI)
    apply Subtype.ext
    apply congrArg q at hcomm
    rw [map_mul, map_mul] at hcomm
    simpa [← hqyi] using hcomm
  have hcenterS : Subgroup.center S = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyAlt : eS y ∈ Subgroup.center (alternatingGroup (Fin s)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := eS.surjective g
      simpa only [map_mul] using congrArg eS (Subgroup.mem_center_iff.mp hy k)
    have hs4 : 4 ≤ s := by omega
    rw [alternatingGroup.center_eq_bot (by simpa using hs4)] at hyAlt
    apply eS.injective
    simpa using (Subgroup.mem_bot.mp hyAlt)
  have hqone : q zi.1 = 1 := by
    have hzbot : (⟨q zi.1, hqziS⟩ : S) ∈ (⊥ : Subgroup S) := by
      rw [← hcenterS]
      exact hzS
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzbot)
  exact hqone

end GLS3.Chapter5
/- END Theory.CenterMapLeCenter -/

/- BEGIN Theory.ComponentAlternatingCenterQuotient -/
namespace GLS3.Chapter5

/-- A component whose image through a central quotient is an alternating
simple factor has the corresponding alternating central quotient. -/
public theorem component_centerQuotient_equiv_alternating_of_image_eq
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (q : G →* Q) (hker : q.ker ≤ Subgroup.center G)
    (I : Subgroup G) [IsQuasisimple I]
    (S : Subgroup Q) (himage : I.map q = S)
    (s : Nat) (hs : 5 ≤ s)
    (eS : S ≃* alternatingGroup (Fin s)) :
    Nonempty (I ⧸ Subgroup.center I ≃* alternatingGroup (Fin s)) := by
  let r : I →* S :=
    (q.comp I.subtype).codRestrict S (fun i => by
      rw [← himage]
      exact Subgroup.mem_map_of_mem q i.2)
  have hr : Function.Surjective r := by
    intro z
    have hz : z.1 ∈ I.map q := by rw [himage]; exact z.2
    obtain ⟨i, hi, hiz⟩ := Subgroup.mem_map.mp hz
    refine ⟨⟨i, hi⟩, ?_⟩
    apply Subtype.ext
    exact hiz
  let f : I →* alternatingGroup (Fin s) := eS.toMonoidHom.comp r
  have hf : Function.Surjective f := eS.surjective.comp hr
  have hfker : f.ker ≤ Subgroup.center I := by
    intro i hi
    have hqi : q i.1 = 1 := by
      have hri : r i = 1 := by
        apply eS.injective
        simpa [f] using MonoidHom.mem_ker.mp hi
      exact congrArg Subtype.val hri
    have hiCenterG : i.1 ∈ Subgroup.center G :=
      hker (MonoidHom.mem_ker.mpr hqi)
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hiCenterG j.1
  have hfkerEq : f.ker = Subgroup.center I := by
    apply SchurPresentation.ker_eq_center_of_surjective_of_center_eq_bot
      f hf hfker
    apply alternatingGroup.center_eq_bot
    simpa using (show 4 ≤ s by omega)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hfkerEq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end GLS3.Chapter5
/- END Theory.ComponentAlternatingCenterQuotient -/

/- BEGIN Theory.ComponentLayerOfDominatingComponent -/
namespace GLS3.Chapter5

/-- If a component contains every component of `C`, then it is exactly the
layer generated by the components of `C`. -/
public theorem componentLayer_eq_of_component_dominates
    {G : Type*} [Group G] (C I : Subgroup G)
    (hI : IsComponentOf I C)
    (hdominates : ∀ J : Subgroup G, IsComponentOf J C → J ≤ I) :
    componentLayer C = I := by
  unfold componentLayer
  apply le_antisymm
  · exact sSup_le fun J hJ => hdominates J hJ
  · exact le_sSup (s := {J : Subgroup G | IsComponentOf J C}) hI

end GLS3.Chapter5
/- END Theory.ComponentLayerOfDominatingComponent -/

/- BEGIN Theory.ComponentOfCentralSimplePreimage -/
namespace GLS3.Chapter5

open scoped commutatorElement

public theorem isComponentOf_commutator_comap_of_surjective_center
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G)
    (S : Subgroup Q) [Group.IsPerfect S] [IsSimpleGroup S]
    (C : Subgroup G)
    (hDleC : (commutator (S.comap q)).map (S.comap q).subtype ≤ C)
    (hDsubnormal : ((commutator (S.comap q)).map (S.comap q).subtype).subgroupOf C
      |>.IsSubnormal) :
    IsComponentOf ((commutator (S.comap q)).map (S.comap q).subtype) C := by
  let E : Subgroup G := S.comap q
  let D0 : Subgroup E := commutator E
  let D : Subgroup G := D0.map E.subtype
  have hEMap : E.map q = S := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hz
      obtain ⟨g, hg⟩ := hq z
      refine ⟨g, ?_, hg⟩
      change q g ∈ S
      rw [hg]
      exact hz
  let f : E →* S :=
    (q.comp E.subtype).codRestrict S (by
      intro e
      exact e.property)
  have hfSurj : Function.Surjective f := by
    intro s
    obtain ⟨g, hg⟩ := hq (s : Q)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change q g ∈ S
      rw [hg]
      exact s.property
    · apply Subtype.ext
      exact hg
  have hfker : f.ker ≤ Subgroup.center E := by
    intro z hz
    have hzq : q (z : G) = 1 := congrArg Subtype.val hz
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hzq) (y : G)
  let : Group.IsPerfect D0 :=
    SchurPresentation.commutator_isPerfect_of_surjective_of_ker_le_center
      f hfSurj hfker
  have hD0map : D0.map f = ⊤ := by
    change (commutator E).map f = ⊤
    rw [map_commutator_eq]
    rw [MonoidHom.range_eq_top.mpr hfSurj]
    exact Group.IsPerfect.commutator_eq_top
  have hrSurj : Function.Surjective (f.comp D0.subtype) := by
    intro s
    have hs : s ∈ D0.map f := by
      rw [hD0map]
      trivial
    obtain ⟨d, hd, hds⟩ := hs
    refine ⟨⟨d, hd⟩, ?_⟩
    exact hds
  have hrker : (f.comp D0.subtype).ker ≤ Subgroup.center D0 := by
    intro d hd
    have hdq : q (d : G) = 1 := by
      exact congrArg Subtype.val hd
    apply Subgroup.mem_center_iff.mpr
    intro e
    apply Subtype.ext
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hdq) (e : G))
  have hcenterS : Subgroup.center S = ⊥ := by
    rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      exact Group.IsPerfect.not_isMulCommutative S (Subgroup.center_eq_top_iff.mp h)
  have hrkerEqCenter : (f.comp D0.subtype).ker = Subgroup.center D0 :=
    SchurPresentation.ker_eq_center_of_surjective_of_center_eq_bot
      (f.comp D0.subtype) hrSurj hrker hcenterS
  let eQ : D0 ⧸ Subgroup.center D0 ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hrkerEqCenter.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (f.comp D0.subtype) hrSurj)
  let : IsQuasisimple D0 := {
    toIsPerfect := inferInstance
    simple := eQ.isSimpleGroup
  }
  let eD : D0 ≃* D := Subgroup.equivMapOfInjective D0 E.subtype E.subtype_injective
  have hcenterMap : (Subgroup.center D0).map eD.toMonoidHom = Subgroup.center D := by
    apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr eD ⟨y, hy⟩).2
    · intro z hz
      refine ⟨eD.symm z, ?_, eD.apply_symm_apply z⟩
      exact ((Subgroup.centerCongr eD).symm ⟨z, hz⟩).2
  have hQD : IsQuasisimple D := by
    have hperf : Group.IsPerfect D :=
      Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective
    have hsimple : IsSimpleGroup (D ⧸ Subgroup.center D) :=
      (MulEquiv.isSimpleGroup_congr
        (QuotientGroup.congr (Subgroup.center D0) (Subgroup.center D)
          eD hcenterMap)).mp (inferInstance : IsQuasisimple D0).simple
    exact { toIsPerfect := hperf, simple := hsimple }
  exact ⟨hDleC, hDsubnormal, hQD⟩

end GLS3.Chapter5
/- END Theory.ComponentOfCentralSimplePreimage -/

/- BEGIN Theory.ComponentPerfect -/
namespace GLS3.Chapter5

public theorem isPerfect_of_isComponentOf
    {G : Type*} [Group G] (I C : Subgroup G)
    (hI : IsComponentOf I C) : Group.IsPerfect I := by
  exact ⟨(isQuasisimple_def I).mp hI.2.2 |>.1⟩

public theorem isPerfect_of_isPComponentOf
    {G : Type*} [Group G] (p : Nat) (I C : Subgroup G)
    (hI : IsPComponentOf p I C) : Group.IsPerfect I := by
  change I ≤ C ∧ (I.subgroupOf C).IsSubnormal ∧
    _root_.commutator I = ⊤ ∧ _ at hI
  exact ⟨hI.2.2.1⟩

end GLS3.Chapter5
/- END Theory.ComponentPerfect -/

/- BEGIN Theory.IsQuasisimpleOfCentralQuotient -/
namespace GLS3.Chapter5

open scoped commutatorElement

public theorem center_map_eq_of_central_normal
    {G : Type*} [Group G] [Group.IsPerfect G]
    (O : Subgroup G) [O.Normal] (hOcenter : O ≤ Subgroup.center G) :
    Subgroup.map (QuotientGroup.mk' O) (Subgroup.center G) =
      Subgroup.center (G ⧸ O) := by
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  have hcomap : Subgroup.comap q (Subgroup.center (G ⧸ O)) =
      Subgroup.center G := by
    apply le_antisymm
    · intro x hx
      change q x ∈ Subgroup.center (G ⧸ O) at hx
      have hcomm : ∀ y : G, ⁅x, y⁆ ∈ O := by
        intro y
        apply (QuotientGroup.eq_one_iff _).mp
        change q ⁅x, y⁆ = 1
        rw [map_commutatorElement q x y]
        apply commutatorElement_eq_one_iff_mul_comm.mpr
        exact (Subgroup.mem_center_iff.mp hx (q y)).symm
      have hxupper : x ∈ Subgroup.upperCentralSeries G 2 := by
        rw [Subgroup.mem_upperCentralSeries_succ_iff]
        intro y
        rw [Subgroup.upperCentralSeries_one]
        exact hOcenter (hcomm y)
      rw [Group.IsPerfect.upperCentralSeries_eq_center G (by decide)] at hxupper
      exact hxupper
    · intro x hx
      change q x ∈ Subgroup.center (G ⧸ O)
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective O y
      rw [← commutatorElement_eq_one_iff_mul_comm]
      rw [← map_commutatorElement q z x]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hzero : ⁅z, x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp hx z)
      rw [hzero]
      exact Subgroup.one_mem O
  rw [← hcomap]
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective O) _

public theorem isQuasisimple_of_perfect_of_center_quotient
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (O : Subgroup G) [hO : O.Normal]
    (hOcenter : O ≤ Subgroup.center G)
    (hcenter : Subgroup.map (QuotientGroup.mk' O) (Subgroup.center G) =
      Subgroup.center (G ⧸ O))
    [hQ : IsQuasisimple (G ⧸ O)]
    [hquotientNontrivial : Nontrivial (G ⧸ Subgroup.center G)] :
    IsQuasisimple G := by
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  let e := QuotientGroup.quotientQuotientEquivQuotient O
    (Subgroup.center G) hOcenter
  let f : (G ⧸ O) ⧸ Subgroup.center (G ⧸ O) →*
      G ⧸ Subgroup.center G := e.toMonoidHom.comp (QuotientGroup.map
        (Subgroup.center (G ⧸ O))
        (Subgroup.map q (Subgroup.center G))
        (MonoidHom.id _) (by
          rw [hcenter]
          exact le_rfl))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center G) z
    obtain ⟨gO, hgO⟩ := QuotientGroup.mk'_surjective O g
    refine ⟨QuotientGroup.mk' (Subgroup.center (G ⧸ O)) gO, ?_⟩
    change f (QuotientGroup.mk' (Subgroup.center (G ⧸ O))
      (QuotientGroup.mk' O gO)) = QuotientGroup.mk' (Subgroup.center G) g
    rw [hgO]
    dsimp [f, e]
    exact QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
      O (Subgroup.center G) hOcenter g
  let : IsSimpleGroup ((G ⧸ O) ⧸ Subgroup.center (G ⧸ O)) := hQ.simple
  let : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    IsSimpleGroup.isSimpleGroup_of_surjective f hf
  exact { toIsPerfect := inferInstance, simple := inferInstance }

public theorem nontrivial_centerQuotient_of_perfect_of_nontrivial_centralQuotient
    {G : Type*} [Group G] [Group.IsPerfect G]
    (O : Subgroup G) [O.Normal]
    (hOcenter : O ≤ Subgroup.center G)
    [hQ : IsQuasisimple (G ⧸ O)] :
    Nontrivial (G ⧸ Subgroup.center G) := by
  rw [QuotientGroup.nontrivial_iff]
  intro hcenter
  have hcomm : _root_.commutator G = ⊥ :=
    commutator_eq_bot_iff_center_eq_top G |>.mpr hcenter
  have htopbot : (⊤ : Subgroup G) = ⊥ := by
    rw [← Group.IsPerfect.commutator_eq_top, hcomm]
  let : Subsingleton G := ⟨by
    intro x y
    have hx : x ∈ (⊥ : Subgroup G) := by
      rw [← htopbot]
      trivial
    have hy : y ∈ (⊥ : Subgroup G) := by
      rw [← htopbot]
      trivial
    exact (Subgroup.mem_bot.mp hx).trans (Subgroup.mem_bot.mp hy).symm⟩
  let : Subsingleton (G ⧸ O) := by
    refine ⟨fun x y => Quotient.inductionOn₂ x y ?_⟩
    intro g h
    have hgh : g = h := Subsingleton.elim g h
    exact (QuotientGroup.eq_iff_div_mem.mpr (by
      rw [hgh]
      simp))
  let : Subsingleton ((G ⧸ O) ⧸ Subgroup.center (G ⧸ O)) := by
    refine ⟨fun x y => Quotient.inductionOn₂ x y ?_⟩
    intro g h
    have hgh : g = h := Subsingleton.elim g h
    exact (QuotientGroup.eq_iff_div_mem.mpr (by
      rw [hgh]
      simp))
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hQ.simple.toNontrivial

public theorem isComponentOf_of_isPComponentOf_of_center_quotient
    {G : Type*} [Group G] [Finite G]
    (p : Nat) (I C : Subgroup G)
    (hIle : I ≤ C)
    (hsubnormal : (I.subgroupOf C).IsSubnormal)
    (hperfect : _root_.commutator I = ⊤)
    (O : Subgroup I) (hO : O.Normal)
    (_hOp : IsPCore p O) (hOcenter : O ≤ Subgroup.center I)
    [hQ : IsQuasisimple (I ⧸ O)]
    [hquotientNontrivial : Nontrivial (I ⧸ Subgroup.center I)] :
    IsComponentOf I C := by
  let : O.Normal := hO
  let : Group.IsPerfect I := ⟨hperfect⟩
  have hcenter : Subgroup.map (QuotientGroup.mk' O) (Subgroup.center I) =
      Subgroup.center (I ⧸ O) := center_map_eq_of_central_normal O hOcenter
  have hQsimple : IsQuasisimple I := by
    exact isQuasisimple_of_perfect_of_center_quotient O hOcenter
      hcenter
  change I ≤ C ∧ (I.subgroupOf C).IsSubnormal ∧ IsQuasisimple I
  exact ⟨hIle, hsubnormal, hQsimple⟩

public theorem isComponentOf_of_isPComponentOf
    {G : Type*} [Group G] [Finite G]
    (p : Nat) (I C : Subgroup G)
    (hI : IsPComponentOf p I C) :
    IsComponentOf I C := by
  change I ≤ C ∧ (I.subgroupOf C).IsSubnormal ∧
    _root_.commutator I = ⊤ ∧ ∃ O : Subgroup I, ∃ hO : O.Normal,
      IsPCore p O ∧ O ≤ Subgroup.center I ∧
        @IsQuasisimple (I ⧸ O)
          (@QuotientGroup.Quotient.group I inferInstance O hO) at hI
  rcases hI with ⟨hIle, hsubnormal, hperfect, ⟨O, hO, hOp,
    hOcenter, hQ⟩⟩
  let : O.Normal := hO
  let : Group.IsPerfect I := ⟨hperfect⟩
  let : IsQuasisimple (I ⧸ O) := hQ
  let : Nontrivial (I ⧸ Subgroup.center I) :=
    nontrivial_centerQuotient_of_perfect_of_nontrivial_centralQuotient
      O hOcenter
  exact isComponentOf_of_isPComponentOf_of_center_quotient p I C
    hIle hsubnormal hperfect O hO hOp hOcenter


end GLS3.Chapter5
/- END Theory.IsQuasisimpleOfCentralQuotient -/

/- BEGIN Theory.PcoreSubgroupLe -/
namespace GLS3.Chapter5

/-- Every normal `p`-subgroup contained in `H` is contained in the defined
`p`-core subgroup. -/
public theorem le_pCoreSubgroup
    {G : Type*} [Group G] (p : Nat) (H P : Subgroup G)
    (hP_le : P ≤ H) (hP_normal : P.Normal) (hP_group : IsPGroup p P) :
    P ≤ pCoreSubgroup p H := by
  unfold pCoreSubgroup
  exact le_sSup ⟨hP_le, hP_normal, hP_group⟩

end GLS3.Chapter5
/- END Theory.PcoreSubgroupLe -/

/- BEGIN Theory.PerfectHomToSolvableTrivial -/
namespace GLS3.Chapter5

/-- A homomorphic image of a perfect group cannot be a nontrivial solvable
group. -/
public theorem monoidHom_eq_one_of_isPerfect_of_isSolvable
    {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    [Group.IsSolvable B] (f : A →* B) : f = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.range := inferInstance
  rcases subsingleton_or_nontrivial f.range with hsub | hnontrivial
  · let : Subsingleton f.range := hsub
    apply MonoidHom.ext
    intro a
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨f a, ⟨a, rfl⟩⟩ : f.range) 1)
  · exfalso
    exact (Group.IsPerfect.not_isSolvable f.range) inferInstance

end GLS3.Chapter5
/- END Theory.PerfectHomToSolvableTrivial -/

/- BEGIN Theory.OddPrimeFixedQuotientStructure -/
namespace GLS3.Chapter5

/-- For an odd-prime-order automorphism of a quasisimple central extension of
an alternating group, the quotient fixed subgroup has the full structure from
Proposition 5.2.6(b). -/
public theorem exists_oddPrime_fixedQuotient_structure
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p) :
    ∃ y : K, orderOf y = p ∧ x = MulAut.conj y ∧
      let ybar := e (QuotientGroup.mk' (Subgroup.center K) y)
      orderOf ybar = p ∧
      ∃ (Rbar Lbar H1bar H2bar : Subgroup
          (alternatingGroup (Fin n)))
        (tbar : alternatingGroup (Fin n)),
        automorphismFixedSubgroup (MulAut.conj ybar) =
            (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar ∧
          H1bar = Rbar ⊔ Lbar ∧
          (Rbar.subgroupOf H1bar).Normal ∧
          Disjoint H1bar H2bar ∧
          (∀ a : H1bar, ∀ b : H2bar, Commute a.1 b.1) ∧
          Disjoint Lbar
            (Subgroup.centralizer
              (Rbar : Set (alternatingGroup (Fin n)))) ∧
          Nonempty (Rbar ≃* Multiplicative
            (Fin (Fintype.card (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset) → ZMod p)) ∧
          Nonempty (Lbar ≃* alternatingGroup
            (Fin (Fintype.card (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset))) ∧
          (∃ eH2 : H2bar ≃* alternatingGroup
              (Fin (Fintype.card (Function.fixedPoints
                (ybar : Equiv.Perm (Fin n))))),
            ∀ u : H2bar,
              (eH2 u).1.support.card = u.1.1.support.card) ∧
          tbar ^ 2 = 1 ∧
          ((Fintype.card (Function.fixedPoints
              (ybar : Equiv.Perm (Fin n))) ≤ 1 ∨
              Fintype.card
                (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset = 1) →
            tbar = 1) ∧
          ((2 ≤ Fintype.card (Function.fixedPoints
                (ybar : Equiv.Perm (Fin n))) ∧
              2 ≤ Fintype.card
                (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset) →
            (H1bar.subgroupOf
                (H1bar ⊔ Subgroup.zpowers tbar)).index = 2 ∧
            (H2bar.subgroupOf
                (H2bar ⊔ Subgroup.zpowers tbar)).index = 2) := by
  obtain ⟨quotientAction, hcompat⟩ :=
    exists_center_quotient_action n e x
  obtain ⟨y, hy, hxy⟩ := proposition_5_2_6_a
    n p hn hp e x hx quotientAction hcompat hp2
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hstructure⟩ :=
    proposition_5_2_6_b n p hn hp e x hx quotientAction hcompat hp2
      y hy hxy
  refine ⟨y, hy, hxy, ?_⟩
  dsimp only
  let ybar : alternatingGroup (Fin n) :=
    e (QuotientGroup.mk' (Subgroup.center K) y)
  have hybarNe : ybar ≠ 1 := by
    intro hybarOne
    have hyquot : QuotientGroup.mk' (Subgroup.center K) y = 1 := by
      apply e.injective
      simpa [ybar] using hybarOne
    have hycenter : y ∈ Subgroup.center K :=
      (QuotientGroup.eq_one_iff y).mp hyquot
    have hxone : x = 1 := by
      rw [hxy]
      apply MulEquiv.ext
      intro k
      change y * k * y⁻¹ = k
      rw [(Subgroup.mem_center_iff.mp hycenter k).symm,
        mul_inv_cancel_right]
    have : p = 1 := by rw [← hx, hxone, orderOf_one]
    exact hp.ne_one this
  have hybarOrder : orderOf ybar = p := by
    have hdvd : orderOf ybar ∣ p := by
      rw [← hy]
      exact orderOf_map_dvd (alternatingQuotientHom e) y
    rcases (Nat.dvd_prime hp).mp hdvd with hone | hporder
    · exact False.elim (hybarNe (orderOf_eq_one_iff.mp hone))
    · exact hporder
  rcases hstructure with ⟨hdecomp, hH1, hRnormal, hdisjoint, hcomm, hfaithful,
    hR, hL, hH2, ht, hsmall, hlarge⟩
  refine ⟨hybarOrder, Rbar, Lbar, H1bar, H2bar, tbar, ?_⟩
  exact ⟨hdecomp, hH1,
    hRnormal, hdisjoint, hcomm, hfaithful, hR, hL, hH2, ht,
    hsmall, hlarge⟩

end GLS3.Chapter5
/- END Theory.OddPrimeFixedQuotientStructure -/

/- BEGIN Theory.ComponentImageSubnormal -/
namespace GLS3.Chapter5

/-- The image of a component under a surjective homomorphism remains perfect
and subnormal in the image of its ambient subgroup. -/
public theorem component_image_isPerfect_isSubnormal
    {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (C I : Subgroup G) (hI : IsComponentOf I C) :
    Group.IsPerfect (I.map q) ∧
      ((I.map q).subgroupOf (C.map q)).IsSubnormal := by
  let Cbar : Subgroup Q := C.map q
  let Ibar : Subgroup Q := I.map q
  let qC : C →* Cbar :=
    (q.comp C.subtype).codRestrict Cbar (fun c =>
      Subgroup.mem_map_of_mem q c.property)
  have hqC : Function.Surjective qC := by
    intro z
    obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp z.property
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact hgz
  let qI : I →* Ibar :=
    (q.comp I.subtype).codRestrict Ibar (fun i =>
      Subgroup.mem_map_of_mem q i.property)
  have hqI : Function.Surjective qI := by
    intro z
    obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp z.property
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact hgz
  let : Group.IsPerfect I := isPerfect_of_isComponentOf I C hI
  have hperfect : Group.IsPerfect Ibar :=
    Group.IsPerfect.ofSurjective hqI
  have hsubnormal :
      (Subgroup.map qC (I.subgroupOf C)).IsSubnormal :=
    hI.2.1.map hqC
  have hmap_eq : Subgroup.map qC (I.subgroupOf C) = Ibar.subgroupOf Cbar := by
    ext z
    constructor
    · intro hz
      change z.1 ∈ Ibar
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨y.1, hy, ?_⟩
      exact congrArg Subtype.val hyz
    · intro hz
      change z.1 ∈ Ibar at hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨⟨y, hI.1 hy⟩, hy, ?_⟩
      apply Subtype.ext
      exact hyz
  rw [hmap_eq] at hsubnormal
  exact ⟨hperfect, hsubnormal⟩

end GLS3.Chapter5
/- END Theory.ComponentImageSubnormal -/

/- BEGIN Theory.ComponentLeCommutator -/
namespace GLS3.Chapter5

/-- A component lies in the derived subgroup of its ambient subgroup. -/
public theorem isComponentOf_le_commutator
    {G : Type*} [Group G] (I C : Subgroup G)
    (hI : IsComponentOf I C) :
    I ≤ ⁅C, C⁆ := by
  have hperfect : Group.IsPerfect I := isPerfect_of_isComponentOf I C hI
  intro i hi
  have hcomm : (⟨i, hi⟩ : I) ∈ commutator I :=
    hperfect.mem_commutator
  have hmap : i ∈ Subgroup.map I.subtype (commutator I) := by
    simpa only [Subgroup.coe_subtype] using
      (Subgroup.mem_map_of_mem I.subtype hcomm)
  rw [Subgroup.map_subtype_commutator] at hmap
  exact Subgroup.commutator_mono hI.1 hI.1 hmap

/-- A `p`-component lies in the derived subgroup of its ambient subgroup. -/
public theorem isPComponentOf_le_commutator
    {G : Type*} [Group G] (p : Nat) (I C : Subgroup G)
    (hI : IsPComponentOf p I C) :
    I ≤ ⁅C, C⁆ := by
  have hperfect : Group.IsPerfect I := isPerfect_of_isPComponentOf p I C hI
  intro i hi
  have hcomm : (⟨i, hi⟩ : I) ∈ commutator I :=
    hperfect.mem_commutator
  have hmap : i ∈ Subgroup.map I.subtype (commutator I) := by
    simpa only [Subgroup.coe_subtype] using
      (Subgroup.mem_map_of_mem I.subtype hcomm)
  rw [Subgroup.map_subtype_commutator] at hmap
  exact Subgroup.commutator_mono hI.1 hI.1 hmap

end GLS3.Chapter5
/- END Theory.ComponentLeCommutator -/

/- BEGIN Theory.SubnormalInNormalSubgroup -/
namespace GLS3.Chapter5

/-- Subnormality descends from an ambient subgroup to a normal intermediate
subgroup. -/
public theorem subnormal_subgroupOf_of_normal_subgroupOf
    {G : Type*} [Group G] (I H C : Subgroup G)
    (hIH : I ≤ H) (hHC : H ≤ C)
    (hHnormal : (H.subgroupOf C).Normal)
    (hIsubnormal : (I.subgroupOf C).IsSubnormal) :
    (I.subgroupOf H).IsSubnormal := by
  let Ic : Subgroup C := I.subgroupOf C
  let Hc : Subgroup C := H.subgroupOf C
  have hIcHc : Ic ≤ Hc := by
    intro i hi
    exact hIH hi
  have hInf : (Ic ⊓ Hc).IsSubnormal :=
    hIsubnormal.inf hHnormal.isSubnormal
  have hInfH : ((Ic ⊓ Hc).subgroupOf Hc).IsSubnormal :=
    hInf.subgroupOf
  rw [inf_eq_left.mpr hIcHc] at hInfH
  let eH : Hc ≃* H := Subgroup.subgroupOfEquivOfLe hHC
  have hmap :
      (Subgroup.map eH.toMonoidHom (Ic.subgroupOf Hc)).IsSubnormal :=
    hInfH.map eH.surjective
  have heq : Subgroup.map eH.toMonoidHom (Ic.subgroupOf Hc) =
      I.subgroupOf H := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [← hzy]
      exact hz
    · intro hy
      refine Subgroup.mem_map.mpr ⟨eH.symm y, ?_, eH.apply_symm_apply y⟩
      exact hy
  rw [heq] at hmap
  exact hmap

end GLS3.Chapter5
/- END Theory.SubnormalInNormalSubgroup -/

/- BEGIN Theory.CenterEqualsPcoreOfContainment -/
namespace GLS3.Chapter5

/-- The center of a component is its ambient `2`-core once the two structural
containments have been established. -/
public theorem center_map_eq_pCoreSubgroup_of_two_primary
    {K : Type*} [Group K] [Finite K]
    (I : Subgroup K)
    (hcenter : (Subgroup.center I).map I.subtype ≤ Subgroup.center K)
    (hcenterI2 : IsPGroup 2 (Subgroup.center I))
    (hreverse : pCoreSubgroup 2 (Subgroup.center K) ≤
      (Subgroup.center I).map I.subtype) :
    (Subgroup.center I).map I.subtype =
      pCoreSubgroup 2 (Subgroup.center K) := by
  apply le_antisymm
  · apply le_pCoreSubgroup
    · exact hcenter
    · constructor
      intro g hg z
      have hzcenter := Subgroup.mem_center_iff.mp (hcenter hg) z
      rw [hzcenter, mul_inv_cancel_right]
      exact hg
    · exact hcenterI2.map I.subtype
  · exact hreverse

end GLS3.Chapter5
/- END Theory.CenterEqualsPcoreOfContainment -/

/- BEGIN Theory.PcoreSubgroupProperties -/
namespace GLS3.Chapter5

public theorem pCoreSubgroup_le
    {G : Type*} [Group G] (p : Nat) (H : Subgroup G) :
    pCoreSubgroup p H ≤ H := by
  unfold pCoreSubgroup
  exact sSup_le fun P hP => hP.1

public theorem pCoreSubgroup_normal
    {G : Type*} [Group G] (p : Nat) (H : Subgroup G) :
    (pCoreSubgroup p H).Normal := by
  unfold pCoreSubgroup
  exact Subgroup.sSup_normal _ fun P hP => hP.2.1

public theorem pCoreSubgroup_isPGroup
    {G : Type*} [Group G] (p : Nat) (H : Subgroup G) :
    IsPGroup p (pCoreSubgroup p H) := by
  unfold pCoreSubgroup
  apply Sylow.sSup_of_normal
  · intro P hP
    exact hP.2.2
  · intro P hP
    exact hP.2.1

public theorem pCoreSubgroup_isPCore
    {G : Type*} [Group G] (p : Nat) (H : Subgroup G) :
    (∀ P : Subgroup G, P.Normal → IsPGroup p P → P ≤ H) →
      IsPCore p (pCoreSubgroup p H) := by
  intro hH
  change (pCoreSubgroup p H).Normal ∧
    IsPGroup p (pCoreSubgroup p H) ∧
      ∀ P : Subgroup G, P.Normal → IsPGroup p P → P ≤ pCoreSubgroup p H
  refine ⟨pCoreSubgroup_normal p H, pCoreSubgroup_isPGroup p H, ?_⟩
  intro P hP hPgroup
  exact le_pCoreSubgroup p H P (hH P hP hPgroup) hP hPgroup

end GLS3.Chapter5
/- END Theory.PcoreSubgroupProperties -/

/- BEGIN Theory.PerfectComponentProductProjection -/
namespace GLS3.Chapter5

/-- The projection of a perfect group into a solvable factor of a product is
trivial. -/
public theorem perfect_product_projection_eq_one_of_isSolvable_left
    {I A B : Type*} [Group I] [Group A] [Group B]
    [Group.IsPerfect I] [Group.IsSolvable A]
    (f : I →* A × B) :
    (MonoidHom.fst A B).comp f = 1 := by
  exact monoidHom_eq_one_of_isPerfect_of_isSolvable
    ((MonoidHom.fst A B).comp f)

/-- A perfect group map into a product with solvable left factor has trivial
left coordinate. -/
public theorem perfect_product_projection_left_eq_one_of_isSolvable_left
    {I A B : Type*} [Group I] [Group A] [Group B]
    [Group.IsPerfect I] [Group.IsSolvable A]
    (f : I →* A × B) (i : I) :
    (f i).1 = 1 := by
  have h := congrArg (fun g : I →* A => g i)
    (perfect_product_projection_eq_one_of_isSolvable_left f)
  exact h

end GLS3.Chapter5
/- END Theory.PerfectComponentProductProjection -/

/- BEGIN Theory.FixedSubgroupMapLe -/
namespace GLS3.Chapter5

/-- A homomorphism intertwining two automorphisms maps the first fixed
subgroup into the second fixed subgroup. -/
public theorem automorphismFixedSubgroup_map_le
    {G H : Type*} [Group G] [Group H]
    (x : MulAut G) (y : MulAut H) (q : G →* H)
    (hcompat : ∀ g : G, q (x g) = y (q g)) :
    (automorphismFixedSubgroup x).map q ≤
      automorphismFixedSubgroup y := by
  rintro z ⟨g, hg, rfl⟩
  change y (q g) = q g
  rw [← hcompat g]
  exact congrArg q (show x g = g from hg)

end GLS3.Chapter5
/- END Theory.FixedSubgroupMapLe -/

/- BEGIN Theory.ComponentImageNontrivial -/
namespace GLS3.Chapter5

/-- A component cannot vanish under a homomorphism whose kernel is central in
the ambient group. -/
public theorem component_image_ne_bot_of_ker_le_center
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (q : G →* Q) (C I : Subgroup G) (hI : IsComponentOf I C)
    (hker : q.ker ≤ Subgroup.center G) :
    I.map q ≠ ⊥ := by
  intro hmap
  have hIker : I ≤ q.ker := (Subgroup.map_eq_bot_iff I).mp hmap
  have hIcenter : I ≤ Subgroup.center G := hIker.trans hker
  let : IsQuasisimple I := hI.2.2
  let : Nontrivial (I ⧸ Subgroup.center I) :=
    IsQuasisimple.simple.toNontrivial
  let : Nontrivial I :=
    (QuotientGroup.mk'_surjective (Subgroup.center I)).nontrivial
  let : IsMulCommutative I := ⟨⟨fun a b => by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hIcenter a.2) b.1).symm⟩⟩
  let : Group.IsPerfect I := IsQuasisimple.toIsPerfect
  exact Group.IsPerfect.not_isSolvable I (inferInstance : Group.IsSolvable I)

end GLS3.Chapter5
/- END Theory.ComponentImageNontrivial -/

/- BEGIN Theory.ComponentLeExtensionBase -/
namespace GLS3.Chapter5

/-- A component of a cyclic extension lies in the normal base product. -/
public theorem isComponentOf_le_extension_base
    {G : Type*} [Group G] (A B C I : Subgroup G) (t : G)
    (hdecomp : C = (A ⊔ B) ⊔ Subgroup.zpowers t)
    (hTA : Subgroup.zpowers t ≤ Subgroup.normalizer A)
    (hTB : Subgroup.zpowers t ≤ Subgroup.normalizer B)
    (hI : IsComponentOf I C) :
    I ≤ A ⊔ B := by
  subst C
  let C : Subgroup G := (A ⊔ B) ⊔ Subgroup.zpowers t
  have hcomm : I ≤ ⁅C, C⁆ := isComponentOf_le_commutator I C hI
  intro i hi
  have hci : i ∈ ⁅C, C⁆ := hcomm hi
  have hci' : i ∈ Subgroup.map C.subtype (commutator C) := by
    rw [Subgroup.map_subtype_commutator]
    exact hci
  obtain ⟨ci, hci_mem, hci_eq⟩ := Subgroup.mem_map.mp hci'
  have hbase : ci ∈ (A ⊔ B).subgroupOf C := by
    exact extensionProduct_derived_le_base A B t hTA hTB hci_mem
  have hbase' : (ci : G) ∈ A ⊔ B := hbase
  rw [← hci_eq]
  exact hbase'

end GLS3.Chapter5
/- END Theory.ComponentLeExtensionBase -/

/- BEGIN Theory.ComponentEqualsAlternatingFactorOfLe -/
namespace GLS3.Chapter5

/-- A component contained in a normal factor equivalent to an alternating
group is the whole factor. -/
public theorem isComponentOf_eq_alternatingFactor_of_le
    {G : Type*} [Group G] (s : Nat) (H C I : Subgroup G)
    (hHle : H ≤ C) (hHnormal : (H.subgroupOf C).Normal)
    (hH : Nonempty (H ≃* alternatingGroup (Fin s)))
    (hI : IsComponentOf I C) (hIle : I ≤ H) :
    I = H ∧ 5 ≤ s := by
  let J : Subgroup H := I.subgroupOf H
  have hJsubnormal : J.IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf I H C
      hIle hHle hHnormal hI.2.1
  let : IsQuasisimple I := hI.2.2
  let : IsQuasisimple J := isQuasisimple_subgroupOf I H hIle
  obtain ⟨eH⟩ := hH
  let Jalt : Subgroup (alternatingGroup (Fin s)) := J.map eH.toMonoidHom
  have hJaltSubnormal : Jalt.IsSubnormal := hJsubnormal.map eH.surjective
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hIbot : I = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hzJ : (⟨z, hIle hz⟩ : H) ∈ J := hz
      rw [hbot] at hzJ
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hzJ)
    let : Nontrivial (I ⧸ Subgroup.center I) :=
      (inferInstance : IsQuasisimple I).simple.toNontrivial
    let : Nontrivial I :=
      (QuotientGroup.mk'_surjective (Subgroup.center I)).nontrivial
    exact I.nontrivial_iff_ne_bot.mp inferInstance hIbot
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr hJne
  let eJ : J ≃* Jalt := eH.subgroupMap J
  let : Nontrivial Jalt := eJ.injective.nontrivial
  let : IsQuasisimple Jalt :=
    isQuasisimple_of_surjective_of_ker_le_center eJ.toMonoidHom eJ.surjective
      (by rw [eJ.toMonoidHom.ker_eq_bot_iff.mpr eJ.injective]; exact bot_le)
  obtain ⟨hJaltTop, hs5⟩ :=
    quasisimple_subnormal_alternating_eq_top s Jalt hJaltSubnormal
  have hJtop : J = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    have hzTop : eH z ∈ Jalt := by rw [hJaltTop]; trivial
    obtain ⟨j, hj, heq⟩ := Subgroup.mem_map.mp hzTop
    have hjz : j = z := eH.injective heq
    simpa [hjz] using hj
  exact ⟨le_antisymm hIle (Subgroup.subgroupOf_eq_top.mp hJtop), hs5⟩

end GLS3.Chapter5
/- END Theory.ComponentEqualsAlternatingFactorOfLe -/

/- BEGIN Theory.ComponentImageEqualsSimpleFactor -/
namespace GLS3.Chapter5

/-- A nontrivial component image contained in a normal simple factor is the
whole factor. -/
public theorem component_image_eq_simple_factor
    {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (C I : Subgroup G) (H2 : Subgroup Q)
    (hI : IsComponentOf I C)
    (hH2le : H2 ≤ C.map q)
    (hH2normal : (H2.subgroupOf (C.map q)).Normal)
    [IsSimpleGroup H2]
    (himage_le : I.map q ≤ H2)
    (himage_ne_bot : I.map q ≠ ⊥) :
    I.map q = H2 := by
  let Cbar : Subgroup Q := C.map q
  let Ibar : Subgroup Q := I.map q
  have hIbar_subnormal : (Ibar.subgroupOf Cbar).IsSubnormal :=
    (component_image_isPerfect_isSubnormal q hq C I hI).2
  have hIbar_subnormal_H2 :
      (Ibar.subgroupOf H2).IsSubnormal := by
    apply subnormal_subgroupOf_of_normal_subgroupOf Ibar H2 Cbar
      himage_le hH2le hH2normal
    exact hIbar_subnormal
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup H2) hIbar_subnormal_H2 with hbot | htop
  · have hIbar_bot : Ibar = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxH : (⟨x, himage_le hx⟩ : H2) ∈ Ibar.subgroupOf H2 := hx
      rw [hbot] at hxH
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxH)
    exact False.elim (himage_ne_bot hIbar_bot)
  · exact le_antisymm himage_le (Subgroup.subgroupOf_eq_top.mp htop)

end GLS3.Chapter5
/- END Theory.ComponentImageEqualsSimpleFactor -/

/- BEGIN Theory.SubnormalSimpleDirectFactor -/
namespace GLS3.Chapter5

/-- A subnormal subgroup contained in the simple right factor of an internal
product is either trivial or the whole right factor. -/
public theorem subnormal_le_simple_right_factor_eq_bot_or_eq_top
    {G : Type*} [Group G] (R L I : Subgroup G)
    [IsSimpleGroup L]
    (hdisjoint : Disjoint R L)
    (hcommute : ∀ r : R, ∀ l : L, Commute r.1 l.1)
    (hIle : I ≤ L)
    (hIsubnormal : (I.subgroupOf (R ⊔ L)).IsSubnormal) :
    I = ⊥ ∨ I = L := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute_apply
    R L hdisjoint hcommute
  let f : ↥(R ⊔ L) →* L :=
    (MonoidHom.snd R L).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro l
    refine ⟨e (1, l), ?_⟩
    simp [f]
  let J : Subgroup (↥(R ⊔ L)) := I.subgroupOf (R ⊔ L)
  have hmap : (Subgroup.map f J).IsSubnormal := hIsubnormal.map hf
  have hmap_eq : Subgroup.map f J = I.subgroupOf L := by
    ext l
    constructor
    · intro hl
      obtain ⟨z, hz, hzl⟩ := Subgroup.mem_map.mp hl
      have hzI : (z : G) ∈ I := hz
      have hzL : (z : G) ∈ L := hIle hzI
      have heq : e (1, (⟨z, hzL⟩ : L)) = z := by
        apply Subtype.ext
        rw [he]
        simp
      have hsecond : f z = ⟨z, hzL⟩ := by
        calc
          f z = f (e (1, (⟨z, hzL⟩ : L))) := congrArg f heq.symm
          _ = ⟨z, hzL⟩ := by simp [f]
      have : (⟨z, hzL⟩ : L) = l := hsecond.symm.trans hzl
      rw [← this]
      exact hzI
    · intro hl
      apply Subgroup.mem_map.mpr
      refine ⟨⟨(l : G), (show (l : G) ∈ R ⊔ L from (le_sup_right : L ≤ R ⊔ L) l.2)⟩, ?_, ?_⟩
      · exact hl
      · have heq : e (1, l) =
            (⟨(l : G), (show (l : G) ∈ R ⊔ L from
              (le_sup_right : L ≤ R ⊔ L) l.2)⟩ : ↥(R ⊔ L)) := by
            rw [he]
            simp
        have h := congrArg (fun q : R × L => q.2)
          (congrArg e.symm heq)
        change (e.symm
          (⟨(l : G), (show (l : G) ∈ R ⊔ L from
            (le_sup_right : L ≤ R ⊔ L) l.2)⟩ : ↥(R ⊔ L))).2 = l
        calc
          _ = (e.symm (e (1, l))).2 := h.symm
          _ = l := by simp
  rw [hmap_eq] at hmap
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup L) hmap with hbot | htop
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro i hi
    have hiL : (⟨i, hIle hi⟩ : L) ∈ I.subgroupOf L := hi
    rw [hbot] at hiL
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hiL)
  · right
    exact le_antisymm hIle (Subgroup.subgroupOf_eq_top.mp htop)

end GLS3.Chapter5
/- END Theory.SubnormalSimpleDirectFactor -/

/- BEGIN Theory.ExceptionalThreeCoreCard -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5

public theorem three_core_center_card_eq_three_of_center_card_eq_six
    {K : Type} [Group K] [Finite K]
    (O3 : Subgroup K) (hO3 : IsPCore 3 O3)
    (hO3center : O3 ≤ Subgroup.center K)
    (hcenter : Nat.card (Subgroup.center K) = 6) :
    Nat.card O3 = 3 := by
  have hcenterDvd : Nat.card (Subgroup.center K) ∣ 6 := by
    rw [hcenter]
  have hcases := pCore_card_eq_one_or_three O3 hO3.isPGroup
    hO3center hcenterDvd
  rcases hcases with hone | hthree
  · have hO3bot : O3 = ⊥ := Subgroup.card_eq_one.mp hone
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by
      rw [hcenter]
      norm_num)
    let zK : K := z.1
    let P : Subgroup K := Subgroup.zpowers zK
    have hzK : orderOf zK = 3 := by
      simpa [zK] using (Subgroup.orderOf_coe z).trans hz
    have hPcenter : P ≤ Subgroup.center K :=
      Subgroup.zpowers_le_of_mem z.2
    have hPnormal : P.Normal := by
      constructor
      intro g hg n
      have hcomm : Commute n g :=
        by
          show n * g = g * n
          exact Subgroup.mem_center_iff.mp (hPcenter hg) n
      rw [hcomm.eq, mul_inv_cancel_right]
      exact hg
    have hPgroup : IsPGroup 3 P := by
      refine IsPGroup.of_card (n := 1) ?_
      simp [P, Nat.card_zpowers, hzK]
    have hPle : P ≤ O3 := hO3.maximal P hPnormal hPgroup
    have hzO3 : zK ∈ O3 := hPle (Subgroup.mem_zpowers zK)
    rw [hO3bot] at hzO3
    have hzKone : zK = 1 := Subgroup.mem_bot.mp hzO3
    rw [hzKone, orderOf_one] at hzK
    omega
  · exact hthree

end GLS3.Chapter5
/- END Theory.ExceptionalThreeCoreCard -/

/- BEGIN Theory.ExceptionalTwoKernelCover -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5

public theorem exists_exceptional_two_kernel_cover
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hnExceptional : n = 6 ∨ n = 7)
    (htwo : 2 ∣ Nat.card (Subgroup.center K)) :
    ∃ (X : Subgroup K) (_ : X.Normal)
      (fbar : (K ⧸ X) →* alternatingGroup (Fin n)),
      X ≤ Subgroup.center K ∧
      Function.Surjective fbar ∧
      fbar.ker ≤ Subgroup.center (K ⧸ X) ∧
      Nat.card fbar.ker = 2 ∧
      fbar.comp (QuotientGroup.mk' X) = alternatingQuotientHom e ∧
      Disjoint X (pCoreSubgroup 2 (Subgroup.center K)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hqsurj : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hqkerCard : Nat.card q.ker = Nat.card (Subgroup.center K) := by
    rw [alternatingQuotientHom_ker e]
  have htwoKer : 2 ∣ Nat.card q.ker := by
    rw [hqkerCard]
    exact htwo
  letI : CommGroup q.ker := {
    mul_comm := fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hqker a.2) b.1).symm }
  let P : Sylow 2 q.ker := default
  let : (P : Subgroup q.ker).Normal := inferInstance
  obtain ⟨C, hPC⟩ :=
    Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let X : Subgroup K := C.map q.ker.subtype
  have hXker : X ≤ q.ker := by
    rintro x ⟨c, hc, rfl⟩
    exact c.2
  have hXcenter : X ≤ Subgroup.center K := hXker.trans hqker
  let hXnormal : X.Normal := ⟨fun x hx a => by
    simpa [Subgroup.mem_center_iff.mp (hXcenter hx) a] using hx⟩
  let : X.Normal := hXnormal
  let fbar : (K ⧸ X) →* alternatingGroup (Fin n) :=
    QuotientGroup.lift X q hXker
  have hfbarSurj : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective X q hqsurj hXker
  have hqXker : (QuotientGroup.mk' X).ker.subgroupOf q.ker = C := by
    rw [QuotientGroup.ker_mk']
    change Subgroup.comap q.ker.subtype (C.map q.ker.subtype) = C
    exact Subgroup.comap_map_eq_self_of_injective q.ker.subtype_injective C
  have hfbarCardSylow : Nat.card fbar.ker = Nat.card P := by
    rw [show fbar = QuotientGroup.lift X q hXker by rfl,
      QuotientGroup.ker_lift]
    exact (SchurPresentation.natCard_map_eq_index_of_subgroupOf_ker_eq'
      q.ker C (QuotientGroup.mk' X) hqXker).trans hPC.index_eq_card
  have hfbarCenter : fbar.ker ≤ Subgroup.center (K ⧸ X) := by
    rw [show fbar = QuotientGroup.lift X q hXker by rfl,
      QuotientGroup.ker_lift]
    exact SchurPresentation.map_le_center_of_le_center_of_surjective'
      (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X) hqker
  have hfbarP : IsPGroup 2 fbar.ker := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card
    rw [hfbarCardSylow, hk]
  have hfbarDiv : 2 ∣ Nat.card fbar.ker := by
    rw [hfbarCardSylow]
    exact P.dvd_card_of_dvd_card htwoKer
  let : IsSimpleGroup (↥(alternatingGroup (Fin n))) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hcenterAlt : Subgroup.center (↥(alternatingGroup (Fin n))) = ⊥ := by
    apply alternatingGroup.center_eq_bot
    simpa only [Nat.card_fin] using (show 4 ≤ n by omega)
  have hkerCenter : fbar.ker = Subgroup.center (K ⧸ X) :=
    SchurPresentation.ker_eq_center_of_surjective_of_center_eq_bot
      fbar hfbarSurj hfbarCenter hcenterAlt
  let ebar : (K ⧸ X) ⧸ Subgroup.center (K ⧸ X) ≃*
      ↥(alternatingGroup (Fin n)) :=
    (QuotientGroup.quotientMulEquivOfEq hkerCenter.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fbar hfbarSurj)
  let qX : K →* K ⧸ X := QuotientGroup.mk' X
  let : IsQuasisimple (K ⧸ X) := {
    toIsPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective X)
    simple := ebar.isSimpleGroup }
  have hcenterP : IsPGroup 2 (Subgroup.center (K ⧸ X)) := by
    rw [← hkerCenter]
    exact hfbarP
  have htwoCenter : 2 ∣ Nat.card (Subgroup.center (K ⧸ X)) := by
    rw [← hkerCenter]
    exact hfbarDiv
  have hcenterCard : Nat.card (Subgroup.center (K ⧸ X)) = 2 :=
    two_primary_alternating_center_card_eq_two n hn ebar hcenterP htwoCenter
  have hfactor : fbar.comp qX = q := by
    apply MonoidHom.ext
    intro k
    change fbar (qX k) = q k
    exact QuotientGroup.lift_mk' X hXker k
  have hPcoreLe : pCoreSubgroup 2 (Subgroup.center K) ≤ q.ker := by
    rw [alternatingQuotientHom_ker e]
    exact pCoreSubgroup_le 2 (Subgroup.center K)
  let P2 : Subgroup q.ker :=
    (pCoreSubgroup 2 (Subgroup.center K)).subgroupOf q.ker
  have hP2 : IsPGroup 2 P2 := by
    exact (pCoreSubgroup_isPGroup 2 (Subgroup.center K)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPcoreLe).symm
  have hP2le : P2 ≤ P := hP2.le_sylow_of_normal P
  have hdisjoint : Disjoint X (pCoreSubgroup 2 (Subgroup.center K)) := by
    rw [Subgroup.disjoint_def]
    intro z hzX hzP
    obtain ⟨c, hc, hcz⟩ := hzX
    have hcP2 : c ∈ P2 := by
      change q.ker.subtype c ∈ pCoreSubgroup 2 (Subgroup.center K)
      rw [hcz]
      exact hzP
    have hcOne : c = 1 :=
      Subgroup.disjoint_def.mp hPC.disjoint.symm hc (hP2le hcP2)
    rw [← hcz, hcOne, map_one]
  refine ⟨X, hXnormal, fbar, hXcenter, hfbarSurj, hfbarCenter, ?_, hfactor,
    hdisjoint⟩
  rw [hkerCenter, hcenterCard]

end GLS3.Chapter5
/- END Theory.ExceptionalTwoKernelCover -/

/- BEGIN Theory.PcoreTwoCardDvd -/
noncomputable section

namespace GLS3.Chapter5

public theorem pCore_two_card_dvd_two_of_isInAlt
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hKAlt : IsInAlt K) :
    Nat.card (pCoreSubgroup 2 (Subgroup.center K)) ∣ 2 := by
  rw [isInAlt_iff_exists_center_quotient] at hKAlt
  obtain ⟨n, _Z, hn, _hZ, ⟨e⟩⟩ := hKAlt
  have hcenterDvd : Nat.card (Subgroup.center K) ∣ 2 ∨
      Nat.card (Subgroup.center K) ∣ 6 := by
    by_cases hnExceptional : n = 6 ∨ n = 7
    · exact Or.inr (exceptional_alternating_center_card_dvd_six n e
        hnExceptional)
    · left
      let q := n - 5
      have hq : q + 5 = n := Nat.sub_add_cancel hn
      let : IsQuasisimple (alternatingGroup (Fin n)) := by
        rw [← hq]
        exact SchurPresentation.alternatingGroup_isQuasisimple q
      obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
      have h6 : n ≠ 6 := fun hn6 => hnExceptional (Or.inl hn6)
      have h7 : n ≠ 7 := fun hn7 => hnExceptional (Or.inr hn7)
      have hq6 : q + 5 ≠ 6 := by simpa [hq] using h6
      have hq7 : q + 5 ≠ 7 := by simpa [hq] using h7
      let ef : Fin (q + 5) ≃ Fin n := finCongr hq
      let eA := ef.symm.altCongrHom
      let f' : K →* alternatingGroup (Fin (q + 5)) :=
        eA.toMonoidHom.comp f.toMonoidHom
      let c : Covering K (alternatingGroup (Fin (q + 5))) := {
        toMonoidHom := f'
        surjective := eA.surjective.comp f.surjective }
      have hkernel := Covering.coveringKernel_card_dvd_of_universal
        (SchurPresentation.schurAlternatingCovering q)
        (SchurPresentation.theorem_5_2_3_b_universality q hq6 hq7) c
      rw [SchurPresentation.theorem_5_2_3_a q] at hkernel
      have hf'ker : f'.ker = f.toMonoidHom.ker := by
        rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
          MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom
            eA.injective]
      rw [← hfker, ← hf'ker]
      simpa [c] using hkernel
  have hP_le : pCoreSubgroup 2 (Subgroup.center K) ≤
      Subgroup.center K := pCoreSubgroup_le 2 (Subgroup.center K)
  have hP_dvd_center : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) ∣
      Nat.card (Subgroup.center K) :=
    Subgroup.card_dvd_of_le hP_le
  have hP : IsPGroup 2 (pCoreSubgroup 2 (Subgroup.center K)) :=
    pCoreSubgroup_isPGroup 2 (Subgroup.center K)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hP
  have hPcoprime :
      (Nat.card (pCoreSubgroup 2 (Subgroup.center K))).Coprime 3 := by
    rw [hr]
    exact Nat.Coprime.pow_left r (by norm_num)
  rcases hcenterDvd with htwo | hsix
  · exact hP_dvd_center.trans htwo
  · apply hPcoprime.dvd_of_dvd_mul_right
    exact hP_dvd_center.trans hsix

end GLS3.Chapter5
/- END Theory.PcoreTwoCardDvd -/

/- BEGIN Theory.PerfectSubgroupDirectProductLeRight -/
namespace GLS3.Chapter5

/-- A perfect subnormal subgroup of an internal product with solvable left
factor is contained in the right factor. -/
public theorem perfect_subnormal_le_right_factor_of_disjoint_of_commute
    {G : Type*} [Group G]
    (A B I : Subgroup G)
    [Group.IsPerfect I] [Group.IsSolvable A]
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1)
    (hI : I ≤ A ⊔ B)
    (hsubnormal : (I.subgroupOf (A ⊔ B)).IsSubnormal) :
    I ≤ B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute_apply
    A B hdisjoint hcommute
  let f : I →* A × B :=
    e.symm.toMonoidHom.comp
      (I.subtype.codRestrict (A ⊔ B) (fun i => hI i.property))
  have hproj : (MonoidHom.fst A B).comp f = 1 :=
    perfect_product_projection_eq_one_of_isSolvable_left f
  intro i hi
  let q : A × B := e.symm ⟨i, hI hi⟩
  have hqleft : q.1 = 1 := by
    have h := congrArg (fun g : I →* A => g ⟨i, hi⟩) hproj
    simpa [f, q, MonoidHom.comp_apply] using h
  have hqi : (i : G) = q.2.1 := by
    have hback := e.apply_symm_apply ⟨i, hI hi⟩
    have hformula := he q
    rw [hformula] at hback
    have hval := congrArg Subtype.val hback
    change q.1.1 * q.2.1 = i at hval
    rw [hqleft] at hval
    simpa using hval.symm
  rw [hqi]
  exact q.2.2

end GLS3.Chapter5
/- END Theory.PerfectSubgroupDirectProductLeRight -/

/- BEGIN Theory.PerfectSubgroupDirectProductLeRightNoSubnormal -/
namespace GLS3.Chapter5

/-- A perfect subgroup of an internal product with solvable left factor is
contained in the right factor. -/
public theorem perfect_subgroup_le_right_factor_of_disjoint_of_commute
    {G : Type*} [Group G]
    (A B I : Subgroup G)
    [Group.IsPerfect I] [Group.IsSolvable A]
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1)
    (hI : I ≤ A ⊔ B) :
    I ≤ B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute_apply
    A B hdisjoint hcommute
  let f : I →* A × B :=
    e.symm.toMonoidHom.comp
      (I.subtype.codRestrict (A ⊔ B) (fun i => hI i.property))
  have hproj : (MonoidHom.fst A B).comp f = 1 :=
    perfect_product_projection_eq_one_of_isSolvable_left f
  intro i hi
  let q : A × B := e.symm ⟨i, hI hi⟩
  have hqleft : q.1 = 1 := by
    have h := congrArg (fun g : I →* A => g ⟨i, hi⟩) hproj
    simpa [f, q, MonoidHom.comp_apply] using h
  have hqi : (i : G) = q.2.1 := by
    have hback := e.apply_symm_apply ⟨i, hI hi⟩
    have hformula := he q
    rw [hformula] at hback
    have hval := congrArg Subtype.val hback
    change q.1.1 * q.2.1 = i at hval
    rw [hqleft] at hval
    simpa using hval.symm
  rw [hqi]
  exact q.2.2

end GLS3.Chapter5
/- END Theory.PerfectSubgroupDirectProductLeRightNoSubnormal -/

/- BEGIN Theory.PerfectSubgroupDirectProductProjection -/
namespace GLS3.Chapter5

/-- A perfect subnormal subgroup of a commuting disjoint product has trivial
projection to the solvable factor. -/
public theorem exists_perfect_subnormal_left_projection_eq_one
    {G : Type*} [Group G]
    (A B I : Subgroup G)
    [Group.IsPerfect I] [Group.IsSolvable A]
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1)
    (hI : I ≤ A ⊔ B)
    (_hsubnormal : (I.subgroupOf (A ⊔ B)).IsSubnormal) :
    ∃ e : (A × B) ≃* ↥(A ⊔ B),
      (MonoidHom.fst A B).comp
          (e.symm.toMonoidHom.comp
            (I.subtype.codRestrict (A ⊔ B) (fun i => hI i.property))) = 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute
    A B hdisjoint hcommute
  let f : I →* A × B :=
    e.symm.toMonoidHom.comp
      (I.subtype.codRestrict (A ⊔ B) (fun i => hI i.property))
  refine ⟨e, ?_⟩
  simpa [f] using perfect_product_projection_eq_one_of_isSolvable_left f

end GLS3.Chapter5
/- END Theory.PerfectSubgroupDirectProductProjection -/

/- BEGIN Theory.SolvableOfMulEquiv -/
namespace GLS3.Chapter5

/-- Solvability transfers across a multiplicative equivalence. -/
public theorem isSolvable_of_mulEquiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [Group.IsSolvable H] : Group.IsSolvable G := by
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end GLS3.Chapter5
/- END Theory.SolvableOfMulEquiv -/

/- BEGIN Theory.ComponentImageInFixedSubgroup -/
namespace GLS3.Chapter5

/-- A component maps to a component of the compatible quotient fixed subgroup
when the quotient kernel is central. -/
public theorem component_image_isComponentOf_fixedSubgroup
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    (I : Subgroup G)
    (hI : IsComponentOf I (automorphismFixedSubgroup alpha)) :
    IsComponentOf (I.map f) (automorphismFixedSubgroup beta) := by
  let C := automorphismFixedSubgroup alpha
  let Cbar := automorphismFixedSubgroup beta
  let J := I.map f
  have hCmap : C.map f ≤ Cbar :=
    automorphismFixedSubgroup_map_le alpha beta f hcompat
  have hJdata := component_image_isPerfect_isSubnormal f hf C I hI
  have hJne : J ≠ ⊥ :=
    component_image_ne_bot_of_ker_le_center f C I hI hker
  let : IsQuasisimple I := hI.2.2
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr hJne
  let r : I →* J :=
    (f.comp I.subtype).codRestrict J (fun i =>
      Subgroup.mem_map_of_mem f i.2)
  have hr : Function.Surjective r := by
    intro j
    obtain ⟨i, hi, hij⟩ := Subgroup.mem_map.mp j.2
    refine ⟨⟨i, hi⟩, ?_⟩
    apply Subtype.ext
    exact hij
  have hrker : r.ker ≤ Subgroup.center I := by
    intro i hi
    have hfi : f i.1 = 1 := congrArg Subtype.val hi
    have hiCenter : i.1 ∈ Subgroup.center G :=
      hker (MonoidHom.mem_ker.mpr hfi)
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hiCenter j.1
  let : IsQuasisimple J :=
    isQuasisimple_of_surjective_of_ker_le_center r hr hrker
  have hCmapNormal : (C.map f).subgroupOf Cbar |>.Normal :=
    automorphismFixedSubgroup_image_normal
      f hf hker alpha beta hcompat hCmap
  have hJleCmap : J ≤ C.map f := Subgroup.map_mono hI.1
  have hJsubnormal : (J.subgroupOf Cbar).IsSubnormal :=
    subnormal_subgroupOf_of_subnormal_of_normal J (C.map f) Cbar
      hJleCmap hCmap hJdata.2 hCmapNormal
  exact ⟨hJleCmap.trans hCmap, hJsubnormal, inferInstance⟩

end GLS3.Chapter5
/- END Theory.ComponentImageInFixedSubgroup -/

/- BEGIN Theory.PerfectLiftEqualsDerivedPreimage -/
namespace GLS3.Chapter5

open scoped commutatorElement

private theorem __ch5_PerfectLiftEqualsDerivedPreimage_commutatorElement_mul_central_left_right
    {G : Type*} [Group G] (za zb ia ib : G)
    (hza : za ∈ Subgroup.center G) (hzb : zb ∈ Subgroup.center G) :
    ⁅za * ia, zb * ib⁆ = ⁅ia, ib⁆ := by
  have hzaComm (g : G) : Commute za g :=
    (Subgroup.mem_center_iff.mp hza g).symm
  have hzbComm (g : G) : Commute zb g :=
    (Subgroup.mem_center_iff.mp hzb g).symm
  have hzaZb : Commute za zb := hzaComm zb
  have hcoreZaInv : Commute (ia * ib) za⁻¹ :=
    (hzaComm (ia * ib)).symm.inv_right
  have hcoreZbInv : Commute (ia * ib * ia⁻¹) zb⁻¹ :=
    (hzbComm (ia * ib * ia⁻¹)).symm.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  rw [(hzaComm ia).mul_inv, (hzbComm ib).mul_inv]
  calc
    (za * ia) * (zb * ib) * (za⁻¹ * ia⁻¹) * (zb⁻¹ * ib⁻¹) =
        ((za * zb) * (ia * ib)) * (za⁻¹ * ia⁻¹) * (zb⁻¹ * ib⁻¹) := by
          rw [(hzbComm ia).symm.mul_mul_mul_comm]
    _ = ((za * zb) * za⁻¹ * ((ia * ib) * ia⁻¹)) *
          (zb⁻¹ * ib⁻¹) := by
          rw [hcoreZaInv.mul_mul_mul_comm]
    _ = ((za * zb) * za⁻¹) * zb⁻¹ *
          ((ia * ib * ia⁻¹) * ib⁻¹) := by
          rw [hcoreZbInv.mul_mul_mul_comm]
    _ = ia * ib * ia⁻¹ * ib⁻¹ := by
          rw [show (za * zb) * za⁻¹ * zb⁻¹ = 1 by
            exact commutatorElement_eq_one_iff_mul_comm.mpr hzaZb.eq]
          simp [mul_assoc]

/-- A perfect subgroup mapping onto `S` through a central quotient is the
derived subgroup of the full preimage of `S`. -/
public theorem perfect_lift_eq_commutator_comap
    {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (hker : q.ker ≤ Subgroup.center G)
    (S : Subgroup Q) (I : Subgroup G)
    (hIle : I ≤ S.comap q) (hImap : I.map q = S)
    (hperfect : _root_.commutator I = ⊤) :
    I = (_root_.commutator (S.comap q)).map (S.comap q).subtype := by
  let E : Subgroup G := S.comap q
  let D : Subgroup G := (_root_.commutator E).map E.subtype
  have hIleD : I ≤ D := by
    dsimp [D]
    rw [Subgroup.map_subtype_commutator]
    intro i hi
    have hiComm : i ∈ ⁅I, I⁆ := by
      rw [← Subgroup.map_subtype_commutator, hperfect]
      exact ⟨⟨i, hi⟩, trivial, rfl⟩
    exact Subgroup.commutator_mono hIle hIle hiComm
  have hDleI : D ≤ I := by
    change (_root_.commutator E).map E.subtype ≤ I
    rw [Subgroup.map_subtype_commutator, Subgroup.commutator_le]
    intro a ha b hb
    have hqa : q a ∈ I.map q := by rw [hImap]; exact ha
    have hqb : q b ∈ I.map q := by rw [hImap]; exact hb
    obtain ⟨ia, hia, hiaq⟩ := Subgroup.mem_map.mp hqa
    obtain ⟨ib, hib, hibq⟩ := Subgroup.mem_map.mp hqb
    let za : G := a * ia⁻¹
    let zb : G := b * ib⁻¹
    have hzaCenter : za ∈ Subgroup.center G := hker (by
      rw [MonoidHom.mem_ker]
      dsimp [za]
      rw [map_mul, map_inv, hiaq]
      simp)
    have hzbCenter : zb ∈ Subgroup.center G := hker (by
      rw [MonoidHom.mem_ker]
      dsimp [zb]
      rw [map_mul, map_inv, hibq]
      simp)
    have haeq : a = za * ia := by simp [za, mul_assoc]
    have hbeq : b = zb * ib := by simp [zb, mul_assoc]
    rw [haeq, hbeq,
      __ch5_PerfectLiftEqualsDerivedPreimage_commutatorElement_mul_central_left_right za zb ia ib
        hzaCenter hzbCenter]
    exact I.mul_mem (I.mul_mem (I.mul_mem hia hib) (I.inv_mem hia))
      (I.inv_mem hib)
  exact le_antisymm hIleD hDleI

end GLS3.Chapter5
/- END Theory.PerfectLiftEqualsDerivedPreimage -/

/- BEGIN Theory.ComponentSimpleFactorForcesTop -/
namespace GLS3.Chapter5

/-- A component lying in a simple factor of a normal internal product is the
whole simple factor, provided it is nontrivial. -/
public theorem isComponentOf_eq_simple_factor_of_le
    {G : Type*} [Group G] (R L C I : Subgroup G)
    (hH1le : R ⊔ L ≤ C)
    (hH1normal : ((R ⊔ L).subgroupOf C).Normal)
    [IsSimpleGroup L]
    (hdisjoint : Disjoint R L)
    (hcommute : ∀ r : R, ∀ l : L, Commute r.1 l.1)
    (hI : IsComponentOf I C)
    (hIleL : I ≤ L)
    (hIne : I ≠ ⊥) :
    I = L := by
  have hIleH1 : I ≤ R ⊔ L := hIleL.trans le_sup_right
  have hsubnormalH1 : (I.subgroupOf (R ⊔ L)).IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf I (R ⊔ L) C
      hIleH1 hH1le hH1normal hI.2.1
  rcases subnormal_le_simple_right_factor_eq_bot_or_eq_top
      R L I hdisjoint hcommute hIleL hsubnormalH1 with hbot | htop
  · exact False.elim (hIne hbot)
  · exact htop

end GLS3.Chapter5
/- END Theory.ComponentSimpleFactorForcesTop -/

/- BEGIN Theory.ComponentLeAlternatingFactor -/
namespace GLS3.Chapter5

/-- Once a component is in the base of a cyclic extension, its perfectness
forces it into the non-solvable factor of the base product. -/
public theorem isComponentOf_le_right_factor
    {G : Type*} [Group G] (R L C I : Subgroup G) (t : G)
    (hdecomp : C = (R ⊔ L) ⊔ Subgroup.zpowers t)
    (hTR : Subgroup.zpowers t ≤ Subgroup.normalizer R)
    (hTL : Subgroup.zpowers t ≤ Subgroup.normalizer L)
    [Group.IsSolvable R]
    (hdisjoint : Disjoint R L)
    (hcommute : ∀ r : R, ∀ l : L, Commute r.1 l.1)
    (hI : IsComponentOf I C) :
    I ≤ L := by
  let : Group.IsPerfect I := isPerfect_of_isComponentOf I C hI
  have hbase : I ≤ R ⊔ L := isComponentOf_le_extension_base R L C I t
    hdecomp hTR hTL hI
  exact perfect_subgroup_le_right_factor_of_disjoint_of_commute
    R L I hdisjoint hcommute hbase

end GLS3.Chapter5
/- END Theory.ComponentLeAlternatingFactor -/

/- BEGIN Theory.OddPrimeComponentLeAlternatingFactor -/
namespace GLS3.Chapter5

/-- In the odd-prime centralizer structure, every component lies in the
alternating direct factor. -/
public theorem isComponentOf_le_oddPrime_alternatingFactor
    {G : Type*} [Group G]
    (R L H C I : Subgroup G) (t : G)
    [IsMulCommutative R] [Group.IsSolvable R]
    (hdecomp : C = ((R ⊔ L) ⊔ H) ⊔ Subgroup.zpowers t)
    (hRnormal : (R.subgroupOf (R ⊔ L)).Normal)
    (hfaithful : Disjoint L (Subgroup.centralizer (R : Set G)))
    (hdisjoint : Disjoint (R ⊔ L) H)
    (hcommute : ∀ a : ↥(R ⊔ L), ∀ b : H, Commute a.1 b.1)
    (htH1 : Subgroup.zpowers t ≤
      Subgroup.normalizer ((R ⊔ L : Subgroup G) : Set G))
    (htH : Subgroup.zpowers t ≤ Subgroup.normalizer H)
    (hI : IsComponentOf I C) :
    I ≤ H := by
  let B : Subgroup G := (R ⊔ L) ⊔ H
  have hIleB : I ≤ B :=
    isComponentOf_le_extension_base (R ⊔ L) H C I t
      hdecomp htH1 htH hI
  have hBleC : B ≤ C := by
    rw [hdecomp]
    exact le_sup_left
  have hBnormal : (B.subgroupOf C).Normal := by
    subst C
    exact extensionProduct_base_normal (R ⊔ L) H
      (Subgroup.zpowers t) htH1 htH
  have hIsubnormalB : (I.subgroupOf B).IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf I B C
      hIleB hBleC hBnormal hI.2.1
  have hH1normalizesR : R ⊔ L ≤ Subgroup.normalizer R :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hRnormal
  have hLnormalizesR : L ≤ Subgroup.normalizer R :=
    le_sup_right.trans hH1normalizesR
  have hHcentralizesR : H ≤ Subgroup.centralizer (R : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hcommute
      ⟨r, (show R ≤ R ⊔ L from le_sup_left) hr⟩ ⟨h, hh⟩).eq
  have hRnormalB : (R.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (show R ≤ B from le_sup_left.trans le_sup_left)]
    exact sup_le hH1normalizesR
      (hHcentralizesR.trans
        (Subgroup.centralizer_le_normalizer (R : Set G)))
  let : IsQuasisimple I := hI.2.2
  have hcommRI : ⁅R, I⁆ = ⊥ :=
    commutator_eq_bot_of_isQuasisimple_relative_subnormal_normal_abelian
      R I B (le_sup_left.trans le_sup_left) hRnormalB hIleB hIsubnormalB
  have hIcentralizesR : I ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa only [Subgroup.commutator_comm I R] using hcommRI
  have hcentralB :
      Subgroup.centralizer (R : Set G) ⊓ B = R ⊔ H := by
    exact centralizer_inf_semidirect_sup_factor_eq
      R L H hLnormalizesR hfaithful hdisjoint hcommute
  have hIleRH : I ≤ R ⊔ H := by
    intro i hi
    exact (show Subgroup.centralizer (R : Set G) ⊓ B ≤ R ⊔ H
      from hcentralB.le) ⟨hIcentralizesR hi, hIleB hi⟩
  let : Group.IsPerfect I := IsQuasisimple.toIsPerfect
  exact perfect_subgroup_le_right_factor_of_disjoint_of_commute
    R H I (hdisjoint.mono le_sup_left le_rfl)
      (fun r h => hcommute
        ⟨r.1, (show R ≤ R ⊔ L from le_sup_left) r.2⟩ h) hIleRH

end GLS3.Chapter5
/- END Theory.OddPrimeComponentLeAlternatingFactor -/

/- BEGIN Theory.PerfectSubgroupExtensionLeRightFactor -/
namespace GLS3.Chapter5

/-- A perfect subgroup of a cyclic extension with solvable left factor lies in
the right factor. -/
public theorem perfect_subgroup_le_extension_right_factor
    {G : Type*} [Group G]
    (A B I : Subgroup G) (t : G)
    [Group.IsPerfect I] [Group.IsSolvable A]
    (hI : I ≤ (A ⊔ B) ⊔ Subgroup.zpowers t)
    (hTA : Subgroup.zpowers t ≤ Subgroup.normalizer A)
    (hTB : Subgroup.zpowers t ≤ Subgroup.normalizer B)
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1) :
    I ≤ B := by
  apply perfect_subgroup_le_right_factor_of_disjoint_of_commute A B I
    hdisjoint hcommute
  exact perfect_subgroup_le_extension_base A B I t hI hTA hTB

end GLS3.Chapter5
/- END Theory.PerfectSubgroupExtensionLeRightFactor -/

/- BEGIN Theory.PerfectSubgroupDirectProductCoordinates -/
namespace GLS3.Chapter5

/-- In the direct-product coordinates, a perfect subnormal subgroup has zero
projection to the solvable factor. -/
public theorem exists_perfect_subnormal_directProduct_left_coord_eq_one
    {G : Type*} [Group G]
    (A B I : Subgroup G)
    [Group.IsPerfect I] [Group.IsSolvable A]
    (hdisjoint : Disjoint A B)
    (hcommute : ∀ a : A, ∀ b : B, Commute a.1 b.1)
    (hI : I ≤ A ⊔ B)
    (_hsubnormal : (I.subgroupOf (A ⊔ B)).IsSubnormal) :
    ∃ e : (A × B) ≃* ↥(A ⊔ B),
      ∀ i : I,
        (e.symm ⟨i.1, hI i.2⟩).1 = 1 := by
  obtain ⟨e, hproj⟩ := exists_perfect_subnormal_left_projection_eq_one
    A B I hdisjoint hcommute hI _hsubnormal
  refine ⟨e, ?_⟩
  intro i
  have hi := congrArg (fun f : I →* A => f i) hproj
  simpa [MonoidHom.comp_apply] using hi

end GLS3.Chapter5
/- END Theory.PerfectSubgroupDirectProductCoordinates -/

/- BEGIN Theory.SolvableOfAlternatingPrimeRotationFactor -/
namespace GLS3.Chapter5

/-- The rotation factor in the odd-prime centralizer structure is solvable. -/
public theorem isSolvable_of_nonempty_mulEquiv_multiplicative_pi_zmod
    {R : Type*} [Group R] (p r : Nat)
    [Group.IsSolvable (Multiplicative (Fin r → ZMod p))]
    (hR : Nonempty (R ≃* Multiplicative (Fin r → ZMod p))) :
    Group.IsSolvable R := by
  obtain ⟨e⟩ := hR
  exact isSolvable_of_mulEquiv e

end GLS3.Chapter5
/- END Theory.SolvableOfAlternatingPrimeRotationFactor -/

/- BEGIN Theory.InvolutionQuotientActionNatural -/
namespace GLS3.Chapter5

/-- If an involutory quotient action has a fixed-subgroup component, then it
comes from conjugation by an involution of the ambient symmetric group. -/
public theorem involution_quotientAction_eq_conjNormal_of_component
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = 2)
    (beta : MulAut (alternatingGroup (Fin n)))
    (hcompat : ∀ k : K,
      e (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        beta (e (QuotientGroup.mk' (Subgroup.center K) k)))
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    ∃ sigma : Equiv.Perm (Fin n), orderOf sigma = 2 ∧
      beta = MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma := by
  have hbetaOrder : orderOf beta = 2 :=
    quotientAction_order Nat.prime_two e x hx beta hcompat
  have hq : Function.Surjective (alternatingQuotientHom e) :=
    alternatingQuotientHom_surjective e
  have hqker : (alternatingQuotientHom e).ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hIbar : IsComponentOf (I.map (alternatingQuotientHom e))
      (automorphismFixedSubgroup beta) :=
    component_image_isComponentOf_fixedSubgroup (alternatingQuotientHom e)
      hq hqker x beta hcompat I hI
  have hconjInj :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n
      ((by omega : 4 ≤ 5).trans hn)
  have finish (sigma : Equiv.Perm (Fin n))
      (hsigma : MulAut.conjNormal
        (H := alternatingGroup (Fin n)) sigma = beta) :
      ∃ tau : Equiv.Perm (Fin n), orderOf tau = 2 ∧
        beta = MulAut.conjNormal (H := alternatingGroup (Fin n)) tau := by
    refine ⟨sigma, ?_, hsigma.symm⟩
    calc
      orderOf sigma = orderOf (MulAut.conjNormal
          (H := alternatingGroup (Fin n)) sigma) :=
        (orderOf_injective _ hconjInj sigma).symm
      _ = orderOf beta := congrArg orderOf hsigma
      _ = 2 := hbetaOrder
  by_cases hn6 : n = 6
  · subst n
    by_cases hnatural : beta ∈ naturalAlternatingAutomorphismSubgroup
    · obtain ⟨sigma, hsigma⟩ := hnatural
      exact finish sigma hsigma
    · obtain ⟨eD⟩ :=
        a6_outsideNatural_involution_fixed_equiv_dihedral beta hbetaOrder hnatural
      let : Group.IsSolvable (DihedralGroup 5) := dihedralGroup_isSolvable 5
      let : Group.IsSolvable (automorphismFixedSubgroup beta) :=
        isSolvable_of_mulEquiv eD
      let J := I.map (alternatingQuotientHom e)
      let : IsQuasisimple J := hIbar.2.2
      let : Nontrivial (J ⧸ Subgroup.center J) :=
        (inferInstance : IsQuasisimple J).simple.toNontrivial
      let : Nontrivial J :=
        (QuotientGroup.mk'_surjective (Subgroup.center J)).nontrivial
      let : Group.IsSolvable (J.subgroupOf (automorphismFixedSubgroup beta)) :=
        inferInstance
      let : Group.IsSolvable J :=
        isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hIbar.1).symm
      exact False.elim (Group.IsPerfect.not_isSolvable J inferInstance)
  · obtain ⟨sigma, hsigma⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        n hn hn6).2 beta
    exact finish sigma hsigma

end GLS3.Chapter5
/- END Theory.InvolutionQuotientActionNatural -/

/- BEGIN Theory.InvolutionComponentLeAlternatingFactor -/
namespace GLS3.Chapter5

/-- In the involution centralizer structure, every component lies in the
alternating fixed-point factor. -/
public theorem isComponentOf_le_involution_alternatingFactor
    {G : Type*} [Group G]
    (R L H1 H C I : Subgroup G) (t : G) (r : Nat)
    (hdecomp : C = (H1 ⊔ H) ⊔ Subgroup.zpowers t)
    (hH1 : H1 = R ⊔ L)
    (hRnormal : (R.subgroupOf H1).Normal)
    (hdisjoint : Disjoint H1 H)
    (hcommute : ∀ a : H1, ∀ b : H, Commute a.1 b.1)
    (hmodule : IsTraceZeroPermutationModule R L r)
    (hindex : ∃ P : Subgroup (InvolutionWreath r),
      P.index = 2 ∧ Nonempty (H1 ≃* P))
    (htH1 : Subgroup.zpowers t ≤ Subgroup.normalizer (H1 : Set G))
    (htH : Subgroup.zpowers t ≤ Subgroup.normalizer (H : Set G))
    (hI : IsComponentOf I C) :
    I ≤ H := by
  let : IsMulCommutative R := IsMulCommutative.of_comm fun a b => by
    obtain ⟨eR, _eL, _haction⟩ := hmodule
    apply eR.injective
    simpa only [map_mul] using mul_comm (eR a) (eR b)
  by_cases hr : 3 ≤ r
  · subst H1
    let : Group.IsSolvable R := Group.isSolvable_of_comm
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R))
    exact isComponentOf_le_oddPrime_alternatingFactor R L H C I t
      hdecomp hRnormal
      (traceZeroPermutationModule_disjoint_centralizer R L r hr hmodule)
      hdisjoint hcommute htH1 htH hI
  · have hr2 : r ≤ 2 := by omega
    obtain ⟨P, _hPindex, ⟨eP⟩⟩ := hindex
    let : Group.IsSolvable (InvolutionWreath r) :=
      involutionWreath_isSolvable_of_le_two r hr2
    let : Group.IsSolvable P := inferInstance
    let : Group.IsSolvable H1 := isSolvable_of_mulEquiv eP
    have hIle : I ≤ H1 ⊔ H :=
      isComponentOf_le_extension_base H1 H C I t
        hdecomp htH1 htH hI
    let : Group.IsPerfect I := hI.2.2.toIsPerfect
    exact perfect_subgroup_le_right_factor_of_disjoint_of_commute
      H1 H I hdisjoint hcommute hIle

end GLS3.Chapter5
/- END Theory.InvolutionComponentLeAlternatingFactor -/

/- BEGIN Theory.AlternatingPrimeCentralizerRotationSolvable -/
namespace GLS3.Chapter5

/-- The rotation factor in the odd-prime fixed-subgroup structure is solvable.
This keeps the subtype-level instance needed by the component projection
lemmas separate from the large structural theorem. -/
public theorem alternatingPrimeCentralizer_rotationFactor_isSolvable
    {G : Type*} [Group G] (p r : Nat) (Rbar : Subgroup G)
    [Group.IsSolvable (Multiplicative (Fin r → ZMod p))]
    (hR : Nonempty (Rbar ≃* Multiplicative (Fin r → ZMod p))) :
    Group.IsSolvable Rbar := by
  exact isSolvable_of_nonempty_mulEquiv_multiplicative_pi_zmod p r hR

end GLS3.Chapter5
/- END Theory.AlternatingPrimeCentralizerRotationSolvable -/

/- BEGIN Theory.InvolutionComponentClassification -/
namespace GLS3.Chapter5

/-- Proposition 5.2.9(a) for involutions. -/
public theorem involution_component_eq_layer_and_isAlternating
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = 2)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    I = componentLayer (automorphismFixedSubgroup x) ∧
      IsAlternatingQuasisimple I := by
  obtain ⟨beta, hcompat⟩ := exists_center_quotient_action n e x
  obtain ⟨sigma, hsigma, hbeta⟩ :=
    involution_quotientAction_eq_conjNormal_of_component
      n hn e x hx beta hcompat I hI
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  let r := Fintype.card sigma.cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints sigma)
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1, hRnormal,
      hdisjoint, hcommute, hmodule, hindex, _hR, _hL, hH2, _ht2,
      htH1, htH2, _hsmall, _hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n sigma hsigma
  have hH2le : H2bar ≤ automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 : H1bar ≤ Subgroup.centralizer
      (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal : (H2bar.subgroupOf (automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  have componentImage (J : Subgroup K)
      (hJ : IsComponentOf J (automorphismFixedSubgroup x)) :
      J.map q = H2bar ∧ 5 ≤ s := by
    have hJbeta : IsComponentOf (J.map q)
        (automorphismFixedSubgroup beta) :=
      component_image_isComponentOf_fixedSubgroup q hq hqker x beta
        hcompat J hJ
    have hJbar : IsComponentOf (J.map q)
        (automorphismFixedSubgroup
          (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma)) := by
      simpa [hbeta] using hJbeta
    have hJle : J.map q ≤ H2bar :=
      isComponentOf_le_involution_alternatingFactor
        Rbar Lbar H1bar H2bar
        (automorphismFixedSubgroup
          (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
        (J.map q) tbar r hdecomp hH1 hRnormal hdisjoint hcommute
        hmodule hindex htH1 htH2 hJbar
    exact isComponentOf_eq_alternatingFactor_of_le s H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (J.map q) hH2le hH2normal ⟨hH2.choose⟩ hJbar hJle
  have componentLift (J : Subgroup K)
      (hJ : IsComponentOf J (automorphismFixedSubgroup x)) :
      J = (_root_.commutator (H2bar.comap q)).map
        (H2bar.comap q).subtype := by
    have hJmap : J.map q = H2bar := (componentImage J hJ).1
    have hJle : J ≤ H2bar.comap q := by
      intro j hj
      change q j ∈ H2bar
      rw [← hJmap]
      exact Subgroup.mem_map_of_mem q hj
    let : IsQuasisimple J := hJ.2.2
    exact perfect_lift_eq_commutator_comap q hqker H2bar J hJle hJmap
      (inferInstance : Group.IsPerfect J).commutator_eq_top
  have hIlift := componentLift I hI
  have hdominates : ∀ J : Subgroup K,
      IsComponentOf J (automorphismFixedSubgroup x) → J ≤ I := by
    intro J hJ
    rw [componentLift J hJ, hIlift]
  have hlayer : componentLayer (automorphismFixedSubgroup x) = I :=
    componentLayer_eq_of_component_dominates
      (automorphismFixedSubgroup x) I hI hdominates
  let : IsQuasisimple I := hI.2.2
  obtain ⟨eH2, _hroot⟩ := hH2
  have hs5 : 5 ≤ s := (componentImage I hI).2
  have hquotient : Nonempty
      (I ⧸ Subgroup.center I ≃* alternatingGroup (Fin s)) :=
    component_centerQuotient_equiv_alternating_of_image_eq q hqker I H2bar
      (componentImage I hI).1 s hs5 eH2
  exact ⟨hlayer.symm,
    isAlternatingQuasisimple_of_centerQuotient_equiv I s hs5 hquotient
      (inferInstance : IsQuasisimple I)⟩

end GLS3.Chapter5
/- END Theory.InvolutionComponentClassification -/

/- BEGIN Theory.InvolutionComponentImageEqualsAlternatingFactor -/
namespace GLS3.Chapter5

/-- For an involutory automorphism, the image of every fixed-subgroup
component in the alternating central quotient is the alternating fixed-point
factor. -/
public theorem involution_component_image_eq_alternatingFactor
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = 2)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    ∃ H2bar : Subgroup (alternatingGroup (Fin n)),
      I.map (alternatingQuotientHom e) = H2bar ∧
      ∃ s : Nat, 5 ≤ s ∧ Nonempty (H2bar ≃* alternatingGroup (Fin s)) := by
  obtain ⟨beta, hcompat⟩ := exists_center_quotient_action n e x
  obtain ⟨sigma, hsigma, hbeta⟩ :=
    involution_quotientAction_eq_conjNormal_of_component
      n hn e x hx beta hcompat I hI
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hIbar : IsComponentOf (I.map q)
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma)) := by
    have hIbeta : IsComponentOf (I.map q)
        (automorphismFixedSubgroup beta) :=
      component_image_isComponentOf_fixedSubgroup q hq hqker x beta
        hcompat I hI
    simpa [hbeta] using hIbeta
  let r := Fintype.card sigma.cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints sigma)
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1, hRnormal,
      hdisjoint, hcommute, hmodule, hindex, _hR, _hL, hH2, _ht2,
      htH1, htH2, _hsmall, _hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n sigma hsigma
  have hIbarLe : I.map q ≤ H2bar :=
    isComponentOf_le_involution_alternatingFactor
      Rbar Lbar H1bar H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) tbar r hdecomp hH1 hRnormal hdisjoint hcommute
      hmodule hindex htH1 htH2 hIbar
  have hH2le : H2bar ≤ automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 :
      H1bar ≤ Subgroup.centralizer
        (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal : (H2bar.subgroupOf (automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  obtain ⟨himage, hs5⟩ := isComponentOf_eq_alternatingFactor_of_le
    s H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) hH2le hH2normal ⟨hH2.choose⟩ hIbar hIbarLe
  exact ⟨H2bar, by simpa [q] using himage, s, hs5, ⟨hH2.choose⟩⟩

end GLS3.Chapter5
/- END Theory.InvolutionComponentImageEqualsAlternatingFactor -/

/- BEGIN Theory.InvolutionComponentImageWithSupport -/
namespace GLS3.Chapter5

/-- For an involutory automorphism, the image of every fixed-subgroup
component in the alternating central quotient is the alternating fixed-point
factor. -/
public theorem involution_component_image_eq_alternatingFactor_with_support
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = 2)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    ∃ H2bar : Subgroup (alternatingGroup (Fin n)),
      I.map (alternatingQuotientHom e) = H2bar ∧
      ∃ s : Nat, 5 ≤ s ∧ ∃ eH2 : H2bar ≃* alternatingGroup (Fin s),
        ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
  obtain ⟨beta, hcompat⟩ := exists_center_quotient_action n e x
  obtain ⟨sigma, hsigma, hbeta⟩ :=
    involution_quotientAction_eq_conjNormal_of_component
      n hn e x hx beta hcompat I hI
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hIbar : IsComponentOf (I.map q)
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma)) := by
    have hIbeta : IsComponentOf (I.map q)
        (automorphismFixedSubgroup beta) :=
      component_image_isComponentOf_fixedSubgroup q hq hqker x beta
        hcompat I hI
    simpa [hbeta] using hIbeta
  let r := Fintype.card sigma.cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints sigma)
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1, hRnormal,
      hdisjoint, hcommute, hmodule, hindex, _hR, _hL, hH2, _ht2,
      htH1, htH2, _hsmall, _hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n sigma hsigma
  have hIbarLe : I.map q ≤ H2bar :=
    isComponentOf_le_involution_alternatingFactor
      Rbar Lbar H1bar H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) tbar r hdecomp hH1 hRnormal hdisjoint hcommute
      hmodule hindex htH1 htH2 hIbar
  have hH2le : H2bar ≤ automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 :
      H1bar ≤ Subgroup.centralizer
        (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal : (H2bar.subgroupOf (automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  obtain ⟨himage, hs5⟩ := isComponentOf_eq_alternatingFactor_of_le
    s H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) hH2le hH2normal ⟨hH2.choose⟩ hIbar hIbarLe
  exact ⟨H2bar, by simpa [q] using himage, s, hs5, hH2.choose, hH2.choose_spec⟩

end GLS3.Chapter5
/- END Theory.InvolutionComponentImageWithSupport -/

/- BEGIN Theory.OddPrimeComponentEqualsAlternatingFactor -/
namespace GLS3.Chapter5

/-- In one fixed odd-prime centralizer decomposition, every component is the
alternating direct factor. -/
public theorem oddPrime_component_eq_alternatingFactor
    {G : Type*} [Group G]
    (p r s : Nat) (hrpos : 0 < r)
    (R L H C I : Subgroup G) (t : G)
    (hdecomp : C = ((R ⊔ L) ⊔ H) ⊔ Subgroup.zpowers t)
    (hRnormal : (R.subgroupOf (R ⊔ L)).Normal)
    (hfaithful : Disjoint L (Subgroup.centralizer (R : Set G)))
    (hdisjoint : Disjoint (R ⊔ L) H)
    (hcommute : ∀ a : ↥(R ⊔ L), ∀ b : H, Commute a.1 b.1)
    (hR : Nonempty (R ≃* Multiplicative (Fin r → ZMod p)))
    (hH : Nonempty (H ≃* alternatingGroup (Fin s)))
    (hsmall : (s ≤ 1 ∨ r = 1) → t = 1)
    (hlarge : (2 ≤ s ∧ 2 ≤ r) →
      ((R ⊔ L).subgroupOf ((R ⊔ L) ⊔ Subgroup.zpowers t)).index = 2 ∧
      (H.subgroupOf (H ⊔ Subgroup.zpowers t)).index = 2)
    (hI : IsComponentOf I C) :
    I = H ∧ 5 ≤ s := by
  obtain ⟨htRL, htH⟩ := primeCentralizer_zpowers_le_normalizer_factors
    r s (R ⊔ L) H t hrpos hsmall hlarge
  let : IsMulCommutative R := IsMulCommutative.of_comm fun a b => by
    obtain ⟨eR⟩ := hR
    apply eR.injective
    simpa only [map_mul] using mul_comm (eR a) (eR b)
  let : Group.IsSolvable R :=
    alternatingPrimeCentralizer_rotationFactor_isSolvable p r R hR
  have hIle : I ≤ H :=
    isComponentOf_le_oddPrime_alternatingFactor R L H C I t hdecomp
      hRnormal hfaithful hdisjoint hcommute htRL htH hI
  have hHle : H ≤ C := by rw [hdecomp]; exact le_sup_right.trans le_sup_left
  have hRLcentralizesH : R ⊔ L ≤ Subgroup.centralizer (H : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hHnormal : (H.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHle, hdecomp]
    exact sup_le
      (sup_le
        (hRLcentralizesH.trans
          (Subgroup.centralizer_le_normalizer (H : Set G)))
        Subgroup.le_normalizer)
      htH
  let J : Subgroup H := I.subgroupOf H
  have hJsubnormal : J.IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf I H C hIle hHle hHnormal hI.2.1
  let : IsQuasisimple I := hI.2.2
  let : IsQuasisimple J := isQuasisimple_subgroupOf I H hIle
  obtain ⟨eH⟩ := hH
  let Jalt : Subgroup (alternatingGroup (Fin s)) := J.map eH.toMonoidHom
  have hJaltSubnormal : Jalt.IsSubnormal := hJsubnormal.map eH.surjective
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hIbot : I = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hzJ : (⟨z, hIle hz⟩ : H) ∈ J := hz
      rw [hbot] at hzJ
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hzJ)
    let : Nontrivial (I ⧸ Subgroup.center I) :=
      (inferInstance : IsQuasisimple I).simple.toNontrivial
    let : Nontrivial I :=
      (QuotientGroup.mk'_surjective (Subgroup.center I)).nontrivial
    exact I.nontrivial_iff_ne_bot.mp inferInstance hIbot
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr hJne
  let eJ : J ≃* Jalt := eH.subgroupMap J
  let : Nontrivial Jalt := eJ.injective.nontrivial
  let : IsQuasisimple Jalt :=
    isQuasisimple_of_surjective_of_ker_le_center eJ.toMonoidHom eJ.surjective
      (by rw [eJ.toMonoidHom.ker_eq_bot_iff.mpr eJ.injective]; exact bot_le)
  obtain ⟨hJaltTop, hs5⟩ :=
    quasisimple_subnormal_alternating_eq_top s Jalt hJaltSubnormal
  have hJtop : J = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    have hzTop : eH z ∈ Jalt := by rw [hJaltTop]; trivial
    obtain ⟨j, hj, heq⟩ := Subgroup.mem_map.mp hzTop
    have hjz : j = z := eH.injective heq
    simpa [hjz] using hj
  exact ⟨le_antisymm hIle (Subgroup.subgroupOf_eq_top.mp hJtop), hs5⟩

end GLS3.Chapter5
/- END Theory.OddPrimeComponentEqualsAlternatingFactor -/

/- BEGIN Theory.OddPrimeComponentImageEqualsAlternatingFactor -/
namespace GLS3.Chapter5

/-- For an odd-prime automorphism, the image of every fixed-subgroup component
in the alternating central quotient is exactly the alternating direct factor
from Proposition 5.2.6(b). -/
public theorem oddPrime_component_image_eq_alternatingFactor
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    ∃ H2bar : Subgroup (alternatingGroup (Fin n)),
      I.map (alternatingQuotientHom e) = H2bar ∧
      ∃ s : Nat, 5 ≤ s ∧ ∃ eH2 : H2bar ≃* alternatingGroup (Fin s),
        ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
  obtain ⟨y, _hy, hxy, hybarOrder, Rbar, Lbar, H1bar, H2bar, tbar,
      hdecomp, hH1, hRnormal, hdisjoint, hcommute, hfaithful,
      hR, _hL, hH2, _ht, hsmall, hlarge⟩ :=
    exists_oddPrime_fixedQuotient_structure n p hn hp hp2 e x hx
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  let ybar : alternatingGroup (Fin n) :=
    e (QuotientGroup.mk' (Subgroup.center K) y)
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hqy : q y = ybar := rfl
  have hcompat : ∀ k : K, q (x k) = MulAut.conj ybar (q k) := by
    intro k
    rw [hxy]
    change q (y * k * y⁻¹) = ybar * q k * ybar⁻¹
    rw [map_mul, map_mul, map_inv, hqy]
  have hIbar : IsComponentOf (I.map q)
      (automorphismFixedSubgroup (MulAut.conj ybar)) :=
    component_image_isComponentOf_fixedSubgroup q hq hqker x
      (MulAut.conj ybar) hcompat I hI
  subst H1bar
  let r := Fintype.card (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints (ybar : Equiv.Perm (Fin n)))
  have hybarNe : ybar ≠ 1 := by
    intro hybar
    have hsource : e (QuotientGroup.mk' (Subgroup.center K) y) = 1 := hybar
    have hpone : p = 1 := hybarOrder.symm.trans (by rw [hsource, orderOf_one])
    exact hp.ne_one hpone
  have hcycles : (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hybarNe (Subtype.ext
      (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp hempty))
  have hrpos : 0 < r :=
    Fintype.card_pos_iff.mpr ⟨⟨hcycles.choose, hcycles.choose_spec⟩⟩
  obtain ⟨htH1, htH2⟩ := primeCentralizer_zpowers_le_normalizer_factors
    r s (Rbar ⊔ Lbar) H2bar tbar hrpos hsmall hlarge
  let : IsMulCommutative Rbar := IsMulCommutative.of_comm fun a b => by
    obtain ⟨eR⟩ := hR
    apply eR.injective
    simpa only [map_mul] using mul_comm (eR a) (eR b)
  let : Group.IsSolvable Rbar :=
    alternatingPrimeCentralizer_rotationFactor_isSolvable p r Rbar hR
  have hIbarLe : I.map q ≤ H2bar :=
    isComponentOf_le_oddPrime_alternatingFactor Rbar Lbar H2bar
      (automorphismFixedSubgroup (MulAut.conj ybar)) (I.map q) tbar
      hdecomp hRnormal hfaithful hdisjoint hcommute htH1 htH2 hIbar
  have hH2le : H2bar ≤ automorphismFixedSubgroup (MulAut.conj ybar) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 :
      Rbar ⊔ Lbar ≤ Subgroup.centralizer (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal :
      (H2bar.subgroupOf (automorphismFixedSubgroup (MulAut.conj ybar))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  let J : Subgroup H2bar := (I.map q).subgroupOf H2bar
  have hJsubnormal : J.IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf (I.map q) H2bar
      (automorphismFixedSubgroup (MulAut.conj ybar))
      hIbarLe hH2le hH2normal hIbar.2.1
  let : IsQuasisimple (I.map q) := hIbar.2.2
  let : IsQuasisimple J := isQuasisimple_subgroupOf (I.map q) H2bar hIbarLe
  obtain ⟨eH2, heH2support⟩ := hH2
  let Jalt : Subgroup (alternatingGroup (Fin s)) := J.map eH2.toMonoidHom
  have hJaltSubnormal : Jalt.IsSubnormal := hJsubnormal.map eH2.surjective
  have hJne : J ≠ ⊥ := by
    intro hbot
    have himageBot : I.map q = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hzJ : (⟨z, hIbarLe hz⟩ : H2bar) ∈ J := hz
      rw [hbot] at hzJ
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hzJ)
    exact component_image_ne_bot_of_ker_le_center q
      (automorphismFixedSubgroup x) I hI hqker himageBot
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr hJne
  let eJ : J ≃* Jalt := eH2.subgroupMap J
  let : Nontrivial Jalt := eJ.injective.nontrivial
  let : IsQuasisimple Jalt :=
    isQuasisimple_of_surjective_of_ker_le_center eJ.toMonoidHom eJ.surjective
      (by rw [eJ.toMonoidHom.ker_eq_bot_iff.mpr eJ.injective]; exact bot_le)
  obtain ⟨hJaltTop, hs5⟩ :=
    quasisimple_subnormal_alternating_eq_top s Jalt hJaltSubnormal
  have hJtop : J = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    have hzTop : eH2 z ∈ Jalt := by rw [hJaltTop]; trivial
    obtain ⟨j, hj, heq⟩ := Subgroup.mem_map.mp hzTop
    have hjz : j = z := eH2.injective heq
    simpa [hjz] using hj
  have himageEq : I.map q = H2bar :=
    le_antisymm hIbarLe (Subgroup.subgroupOf_eq_top.mp hJtop)
  exact ⟨H2bar, by simpa [q] using himageEq, s, hs5, eH2, heH2support⟩

end GLS3.Chapter5
/- END Theory.OddPrimeComponentImageEqualsAlternatingFactor -/

/- BEGIN Theory.OddPrimeComponentClassification -/
namespace GLS3.Chapter5

/-- Proposition 5.2.9(a) for odd prime order. -/
public theorem oddPrime_component_eq_layer_and_isAlternating
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    I = componentLayer (automorphismFixedSubgroup x) ∧
      IsAlternatingQuasisimple I := by
  obtain ⟨y, _hy, hxy, hybarOrder, Rbar, Lbar, H1bar, H2bar, tbar,
      hdecomp, hH1, hRnormal, hdisjoint, hcommute, hfaithful,
      hR, _hL, hH2, _ht, hsmall, hlarge⟩ :=
    exists_oddPrime_fixedQuotient_structure n p hn hp hp2 e x hx
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  let ybar : alternatingGroup (Fin n) :=
    e (QuotientGroup.mk' (Subgroup.center K) y)
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hqy : q y = ybar := rfl
  have hcompat : ∀ k : K, q (x k) = MulAut.conj ybar (q k) := by
    intro k
    rw [hxy]
    change q (y * k * y⁻¹) = ybar * q k * ybar⁻¹
    rw [map_mul, map_mul, map_inv, hqy]
  subst H1bar
  let r := Fintype.card (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints (ybar : Equiv.Perm (Fin n)))
  have hybarNe : ybar ≠ 1 := by
    intro hybar
    have hsource : e (QuotientGroup.mk' (Subgroup.center K) y) = 1 := hybar
    have hpone : p = 1 := hybarOrder.symm.trans (by rw [hsource, orderOf_one])
    exact hp.ne_one hpone
  have hcycles : (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hybarNe (Subtype.ext
      (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp hempty))
  have hrpos : 0 < r :=
    Fintype.card_pos_iff.mpr ⟨⟨hcycles.choose, hcycles.choose_spec⟩⟩
  have componentImage (J : Subgroup K)
      (hJ : IsComponentOf J (automorphismFixedSubgroup x)) :
      J.map q = H2bar := by
    have hJbar : IsComponentOf (J.map q)
        (automorphismFixedSubgroup (MulAut.conj ybar)) :=
      component_image_isComponentOf_fixedSubgroup q hq hqker x
        (MulAut.conj ybar) hcompat J hJ
    exact (oddPrime_component_eq_alternatingFactor p r s hrpos Rbar Lbar
      H2bar (automorphismFixedSubgroup (MulAut.conj ybar)) (J.map q) tbar
      hdecomp hRnormal hfaithful hdisjoint hcommute hR ⟨hH2.choose⟩ hsmall hlarge hJbar).1
  have hs5 : 5 ≤ s :=
    (oddPrime_component_eq_alternatingFactor p r s hrpos Rbar Lbar
      H2bar (automorphismFixedSubgroup (MulAut.conj ybar)) (I.map q) tbar
      hdecomp hRnormal hfaithful hdisjoint hcommute hR ⟨hH2.choose⟩ hsmall hlarge
      (component_image_isComponentOf_fixedSubgroup q hq hqker x
        (MulAut.conj ybar) hcompat I hI)).2
  have componentLift (J : Subgroup K)
      (hJ : IsComponentOf J (automorphismFixedSubgroup x)) :
      J = (_root_.commutator (H2bar.comap q)).map (H2bar.comap q).subtype := by
    have hJmap : J.map q = H2bar := componentImage J hJ
    have hJle : J ≤ H2bar.comap q := by
      intro j hj
      change q j ∈ H2bar
      rw [← hJmap]
      exact Subgroup.mem_map_of_mem q hj
    let : IsQuasisimple J := hJ.2.2
    exact perfect_lift_eq_commutator_comap q hqker H2bar J hJle hJmap
      (inferInstance : Group.IsPerfect J).commutator_eq_top
  have hIlift := componentLift I hI
  have hdominates : ∀ J : Subgroup K,
      IsComponentOf J (automorphismFixedSubgroup x) → J ≤ I := by
    intro J hJ
    rw [componentLift J hJ, hIlift]
  have hlayer : componentLayer (automorphismFixedSubgroup x) = I :=
    componentLayer_eq_of_component_dominates
      (automorphismFixedSubgroup x) I hI hdominates
  let : IsQuasisimple I := hI.2.2
  obtain ⟨eH2, _heH2support⟩ := hH2
  have hquotient : Nonempty
      (I ⧸ Subgroup.center I ≃* alternatingGroup (Fin s)) :=
    component_centerQuotient_equiv_alternating_of_image_eq q hqker I H2bar
      (componentImage I hI) s hs5 eH2
  exact ⟨hlayer.symm,
    isAlternatingQuasisimple_of_centerQuotient_equiv I s hs5 hquotient
      (inferInstance : IsQuasisimple I)⟩

end GLS3.Chapter5
/- END Theory.OddPrimeComponentClassification -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_9_b -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5

/-- Proposition 5.2.9(a): a component or `p`-component of the fixed subgroup
is the layer and belongs to the alternating quasisimple family. -/
public theorem proposition_5_2_9_a
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hKAlt : IsInAlt K) (p : Nat) (hp : p.Prime)
    (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K)
    (hI : IsComponentOf I (automorphismFixedSubgroup x) ∨
      IsPComponentOf p I (automorphismFixedSubgroup x)) :
    I = componentLayer (automorphismFixedSubgroup x) ∧
      IsAlternatingQuasisimple I := by
  rw [isInAlt_iff_exists_center_quotient] at hKAlt
  obtain ⟨n, _Z, hn, _hZ, ⟨e⟩⟩ := hKAlt
  have hIcomponent : IsComponentOf I (automorphismFixedSubgroup x) :=
    hI.elim id (isComponentOf_of_isPComponentOf p I
      (automorphismFixedSubgroup x))
  by_cases hp2 : p = 2
  · have hx2 : orderOf x = 2 := hx.trans hp2
    exact involution_component_eq_layer_and_isAlternating
      n hn e x hx2 I hIcomponent
  · exact oddPrime_component_eq_layer_and_isAlternating
      n p hn hp hp2 e x hx I hIcomponent


/-- A perfect central extension of `A₅` has kernel of order dividing two. -/
public theorem center_card_dvd_two_of_centerQuotient_equiv_degree_five
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hquotient : Nonempty
      (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 5))) :
    Nat.card (Subgroup.center G) ∣ 2 := by
  obtain ⟨e⟩ := hquotient
  let c : Covering G (alternatingGroup (Fin 5)) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
    surjective := e.surjective.comp
      (QuotientGroup.mk'_surjective (Subgroup.center G))
  }
  have hker : c.toMonoidHom.ker = Subgroup.center G := by
    rw [show c.toMonoidHom = e.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center G)) by rfl,
      MonoidHom.ker_comp_of_injective
        (QuotientGroup.mk' (Subgroup.center G)) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hdvd := Covering.coveringKernel_card_dvd_of_universal
    (SchurPresentation.schurAlternatingCovering 0)
    (SchurPresentation.theorem_5_2_3_b_universality 0 (by norm_num) (by norm_num))
    c
  rw [SchurPresentation.natCard_ker_schurAlternatingCovering 0] at hdvd
  rw [← hker]
  simpa [c] using hdvd

/-- A perfect central extension of `A₅` has a two-group center. -/
public theorem isPGroup_two_of_centerQuotient_equiv_degree_five
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hquotient : Nonempty
      (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 5))) :
    IsPGroup 2 (Subgroup.center G) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp
      (center_card_dvd_two_of_centerQuotient_equiv_degree_five hquotient) with
    hcard | hcard
  · apply IsPGroup.of_card (n := 0)
    simpa using hcard
  · apply IsPGroup.of_card (n := 1)
    simpa using hcard




/-- A nontrivial permutation of order two on at most seven points with at
least five fixed points is a transposition on seven points. -/
public theorem involution_fixedPoints_card_ge_five_implies_seven_and_five
    {n : Nat} (hn : n ≤ 7) (σ : Equiv.Perm (Fin n))
    (hσ : orderOf σ = 2) (hs : 5 ≤ Fintype.card (Function.fixedPoints σ)) :
    n = 7 ∧ Fintype.card (Function.fixedPoints σ) = 5 := by
  have hσprime : (orderOf σ).Prime := by rw [hσ]; exact Nat.prime_two
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order hσprime
  have hsum_ge : 2 ≤ σ.cycleType.sum := by
    rw [hk]
    simp
    nlinarith
  have hs' : 5 ≤ n - σ.cycleType.sum := by
    rw [Equiv.Perm.card_fixedPoints σ] at hs
    simpa using hs
  have hsum_le : σ.cycleType.sum ≤ n := by
    simpa using Equiv.Perm.sum_cycleType_le σ
  have hsum_eq : σ.cycleType.sum = 2 := by omega
  have hn7 : n = 7 := by omega
  refine ⟨hn7, ?_⟩
  rw [Equiv.Perm.card_fixedPoints σ]
  rw [Fintype.card_fin]
  omega




/-- A permutation of odd prime order on at most seven points fixes fewer than
five points. -/
public theorem prime_order_permutation_fixedPoints_card_lt_five
    {n : Nat} (hn : n ≤ 7) (σ : Equiv.Perm (Fin n))
    (hσ : (orderOf σ).Prime) (hσ2 : orderOf σ ≠ 2) :
    Fintype.card (Function.fixedPoints σ) < 5 := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order hσ
  have hσ3 : 3 ≤ orderOf σ := by
    have hge2 : 2 ≤ orderOf σ := Nat.Prime.two_le hσ
    omega
  have hsum_ge : 3 ≤ σ.cycleType.sum := by
    rw [hk]
    simp
    nlinarith [hσ3]
  have hsum_le : σ.cycleType.sum ≤ n := by
    simpa using Equiv.Perm.sum_cycleType_le σ
  rw [Equiv.Perm.card_fixedPoints σ]
  simp only [Fintype.card_fin]
  omega


/-- In an exceptional alternating degree, an involutory automorphism with a
fixed-subgroup component forces the degree-seven, degree-five fixed-point
factor. -/
public theorem involution_component_degree_five_of_exceptional
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = 2)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x))
    (hnExceptional : n = 6 ∨ n = 7) :
    ∃ (s : Nat) (H2bar : Subgroup (alternatingGroup (Fin n)))
      (eH2 : H2bar ≃* alternatingGroup (Fin s)),
      I.map (alternatingQuotientHom e) = H2bar ∧
      5 ≤ s ∧ s = 5 ∧ n = 7 ∧
      ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
  obtain ⟨beta, hcompat⟩ := exists_center_quotient_action n e x
  obtain ⟨sigma, hsigma, hbeta⟩ :=
    involution_quotientAction_eq_conjNormal_of_component
      n hn e x hx beta hcompat I hI
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hIbar : IsComponentOf (I.map q)
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma)) := by
    have hIbeta : IsComponentOf (I.map q)
        (automorphismFixedSubgroup beta) :=
      component_image_isComponentOf_fixedSubgroup q hq hqker x beta
        hcompat I hI
    simpa [hbeta] using hIbeta
  let r := Fintype.card sigma.cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints sigma)
  obtain ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1, hRnormal,
      hdisjoint, hcommute, hmodule, hindex, _hR, _hL, hH2, _ht2,
      htH1, htH2, _hsmall, _hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n sigma hsigma
  have hIbarLe : I.map q ≤ H2bar :=
    isComponentOf_le_involution_alternatingFactor
      Rbar Lbar H1bar H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) tbar r hdecomp hH1 hRnormal hdisjoint hcommute
      hmodule hindex htH1 htH2 hIbar
  have hH2le : H2bar ≤ automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 :
      H1bar ≤ Subgroup.centralizer
        (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal : (H2bar.subgroupOf (automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  obtain ⟨himage, hs5⟩ := isComponentOf_eq_alternatingFactor_of_le
    s H2bar
      (automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) sigma))
      (I.map q) hH2le hH2normal ⟨hH2.choose⟩ hIbar hIbarLe
  have hn7 : n = 7 := by
    have hnn : n ≤ 7 := by
      rcases hnExceptional with hn6 | hn7
      · omega
      · omega
    exact (involution_fixedPoints_card_ge_five_implies_seven_and_five
      hnn sigma hsigma hs5).1
  have hs_eq : s = 5 := by
    have h := involution_fixedPoints_card_ge_five_implies_seven_and_five
      (by omega) sigma hsigma hs5
    simpa [s] using h.2
  refine ⟨s, H2bar, hH2.choose, ?_, hs5, hs_eq, hn7, hH2.choose_spec⟩
  simpa [q] using himage


/-- In an exceptional alternating degree, an odd-prime automorphism cannot
have a fixed-subgroup component: the fixed-point factor has degree below five. -/
public theorem oddPrime_component_exceptional_impossible
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x))
    (hnExceptional : n = 6 ∨ n = 7) : False := by
  obtain ⟨y, _hy, hxy, hybarOrder, Rbar, Lbar, H1bar, H2bar, tbar,
      hdecomp, hH1, hRnormal, hdisjoint, hcommute, hfaithful,
      hR, _hL, hH2, _ht, hsmall, hlarge⟩ :=
    exists_oddPrime_fixedQuotient_structure n p hn hp hp2 e x hx
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  let ybar : alternatingGroup (Fin n) :=
    e (QuotientGroup.mk' (Subgroup.center K) y)
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  have hqy : q y = ybar := rfl
  have hcompat : ∀ k : K, q (x k) = MulAut.conj ybar (q k) := by
    intro k
    rw [hxy]
    change q (y * k * y⁻¹) = ybar * q k * ybar⁻¹
    rw [map_mul, map_mul, map_inv, hqy]
  subst H1bar
  let r := Fintype.card (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints (ybar : Equiv.Perm (Fin n)))
  have hybarNe : ybar ≠ 1 := by
    intro hybar
    have hsource : e (QuotientGroup.mk' (Subgroup.center K) y) = 1 := hybar
    have hpone : p = 1 := hybarOrder.symm.trans (by rw [hsource, orderOf_one])
    exact hp.ne_one hpone
  have hcycles : (ybar : Equiv.Perm (Fin n)).cycleFactorsFinset.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hybarNe (Subtype.ext
      (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp hempty))
  have hrpos : 0 < r :=
    Fintype.card_pos_iff.mpr ⟨⟨hcycles.choose, hcycles.choose_spec⟩⟩
  have hIbar : IsComponentOf (I.map q)
      (automorphismFixedSubgroup (MulAut.conj ybar)) :=
    component_image_isComponentOf_fixedSubgroup q hq hqker x
      (MulAut.conj ybar) hcompat I hI
  obtain ⟨htH1, htH2⟩ := primeCentralizer_zpowers_le_normalizer_factors
    r s (Rbar ⊔ Lbar) H2bar tbar hrpos hsmall hlarge
  let : IsMulCommutative Rbar := IsMulCommutative.of_comm fun a b => by
    obtain ⟨eR⟩ := hR
    apply eR.injective
    simpa only [map_mul] using mul_comm (eR a) (eR b)
  let : Group.IsSolvable Rbar :=
    alternatingPrimeCentralizer_rotationFactor_isSolvable p r Rbar hR
  have hIbarLe : I.map q ≤ H2bar :=
    isComponentOf_le_oddPrime_alternatingFactor Rbar Lbar H2bar
      (automorphismFixedSubgroup (MulAut.conj ybar)) (I.map q) tbar
      hdecomp hRnormal hfaithful hdisjoint hcommute htH1 htH2 hIbar
  have hH2le : H2bar ≤ automorphismFixedSubgroup (MulAut.conj ybar) := by
    rw [hdecomp]
    exact le_sup_right.trans le_sup_left
  have hH1centralizesH2 :
      Rbar ⊔ Lbar ≤ Subgroup.centralizer (H2bar : Set (alternatingGroup (Fin n))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommute ⟨z, hz⟩ ⟨h, hh⟩).symm.eq
  have hH2normal :
      (H2bar.subgroupOf (automorphismFixedSubgroup (MulAut.conj ybar))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH2le, hdecomp]
    exact sup_le
      (sup_le
        (hH1centralizesH2.trans
          (Subgroup.centralizer_le_normalizer
            (H2bar : Set (alternatingGroup (Fin n)))))
        Subgroup.le_normalizer)
      htH2
  let J : Subgroup H2bar := (I.map q).subgroupOf H2bar
  have hJsubnormal : J.IsSubnormal :=
    subnormal_subgroupOf_of_normal_subgroupOf (I.map q) H2bar
      (automorphismFixedSubgroup (MulAut.conj ybar))
      hIbarLe hH2le hH2normal hIbar.2.1
  let : IsQuasisimple (I.map q) := hIbar.2.2
  let : IsQuasisimple J := isQuasisimple_subgroupOf (I.map q) H2bar hIbarLe
  obtain ⟨eH2, _heH2support⟩ := hH2
  let Jalt : Subgroup (alternatingGroup (Fin s)) := J.map eH2.toMonoidHom
  have hJaltSubnormal : Jalt.IsSubnormal := hJsubnormal.map eH2.surjective
  have hJne : J ≠ ⊥ := by
    intro hbot
    have himageBot : I.map q = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hzJ : (⟨z, hIbarLe hz⟩ : H2bar) ∈ J := hz
      rw [hbot] at hzJ
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hzJ)
    exact component_image_ne_bot_of_ker_le_center q
      (automorphismFixedSubgroup x) I hI hqker himageBot
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr hJne
  let eJ : J ≃* Jalt := eH2.subgroupMap J
  let : Nontrivial Jalt := eJ.injective.nontrivial
  let : IsQuasisimple Jalt :=
    isQuasisimple_of_surjective_of_ker_le_center eJ.toMonoidHom eJ.surjective
      (by rw [eJ.toMonoidHom.ker_eq_bot_iff.mpr eJ.injective]; exact bot_le)
  obtain ⟨_hJaltTop, hs5⟩ :=
    quasisimple_subnormal_alternating_eq_top s Jalt hJaltSubnormal
  have hlt : s < 5 := by
    have hnn : n ≤ 7 := by
      rcases hnExceptional with hn6 | hn7
      · omega
      · omega
    exact prime_order_permutation_fixedPoints_card_lt_five hnn
      (ybar : Equiv.Perm (Fin n))
      (by rw [Subgroup.orderOf_coe ybar, hybarOrder]; exact hp)
      (by rw [Subgroup.orderOf_coe ybar, hybarOrder]; exact hp2)
  omega

private theorem __ch5_proposition_5_2_9_b_order_two_mem_pCoreSubgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (z : G) (hz : z ∈ H) (hzcenter : z ∈ Subgroup.center G)
    (hop : orderOf z = 2) :
    z ∈ pCoreSubgroup 2 H := by
  let P : Subgroup G := Subgroup.zpowers z
  have hPle : P ≤ H := Subgroup.zpowers_le_of_mem hz
  have hPcenter : P ≤ Subgroup.center G := Subgroup.zpowers_le_of_mem hzcenter
  have hPnormal : P.Normal := by
    constructor
    intro g hn n
    have hcomm : Commute n g := Subgroup.mem_center_iff.mp (hPcenter hn) n
    rw [hcomm.eq, mul_inv_cancel_right]
    exact hn
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPgroup : IsPGroup 2 P := by
    apply IsPGroup.of_card (n := 1)
    simp [P, Nat.card_zpowers, hop]
  have hPleCore := le_pCoreSubgroup 2 H P hPle hPnormal hPgroup
  exact hPleCore (Subgroup.mem_zpowers z)

private theorem __ch5_proposition_5_2_9_b_isPGroup_three_of_subgroup_disjoint_twoCore
    {K : Type*} [Group K] [Finite K]
    (X : Subgroup K) (hXle : X ≤ Subgroup.center K)
    (hXdisj : Disjoint X (pCoreSubgroup 2 (Subgroup.center K)))
    (hcenter : Nat.card (Subgroup.center K) = 6) :
    IsPGroup 3 X := by
  set zc : Nat := Nat.card X
  have hzdvd : zc ∣ 6 := by
    dsimp [zc]
    exact (Subgroup.card_dvd_of_le hXle).trans (by rw [hcenter])
  have hzpos : 0 < zc := by simp [zc]
  have hzle : zc ≤ 6 := Nat.le_of_dvd (by norm_num) hzdvd
  have hnoTwo : ¬ 2 ∣ zc := by
    intro h2
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z1, hzord⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
    let z : K := z1.1
    have hzX : z ∈ X := z1.2
    have hzord' : orderOf z = 2 := by
      simpa [z] using (Subgroup.orderOf_coe z1).trans hzord
    have hzord : orderOf z = 2 := hzord'
    have hzcenterK : z ∈ Subgroup.center K := hXle hzX
    have hzp : z ∈ pCoreSubgroup 2 (Subgroup.center K) :=
      __ch5_proposition_5_2_9_b_order_two_mem_pCoreSubgroup (Subgroup.center K) z hzcenterK hzcenterK hzord
    have hx : z = 1 := (Subgroup.disjoint_def.mp hXdisj) hzX hzp
    rw [hx, orderOf_one] at hzord
    norm_num at hzord
  have hcases : zc = 1 ∨ zc = 3 := by
    interval_cases zc
    · exact Or.inl rfl
    · exfalso; exact hnoTwo (by norm_num)
    · exact Or.inr rfl
    · exfalso; exact hnoTwo (by norm_num)
    · exfalso; norm_num at hzdvd
    · exfalso; exact hnoTwo (by norm_num)
  rcases hcases with h1 | h3
  · apply IsPGroup.of_card (n := 0)
    simpa [zc] using h1
  · apply IsPGroup.of_card (n := 1)
    simpa [zc] using h3

public theorem exceptionalThreePrimary_pCore_two_le_center_image
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hnExceptional : n = 6 ∨ n = 7)
    (hthree : 3 ∣ Nat.card (Subgroup.center K))
    (p : Nat) (hp : p.Prime) (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K) (hI : IsComponentOf I (automorphismFixedSubgroup x)) :
    pCoreSubgroup 2 (Subgroup.center K) ≤ (Subgroup.center I).map I.subtype := by
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  let : IsQuasisimple I := hI.2.2
  have hKAlt : IsInAlt K :=
    isInAlt_iff_exists_center_quotient.mpr
      ⟨n, Subgroup.center K, hn, rfl, ⟨e⟩⟩
  have hdeg :
      ∃ (s : Nat) (H2bar : Subgroup (alternatingGroup (Fin n)))
        (eH2 : H2bar ≃* alternatingGroup (Fin s)),
      I.map q = H2bar ∧ 5 ≤ s ∧ s = 5 ∧ n = 7 ∧
        ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
    by_cases hp2 : p = 2
    · simpa [q] using involution_component_degree_five_of_exceptional
        n hn e x (by simpa [hp2] using hx) I hI hnExceptional
    · exfalso
      exact oddPrime_component_exceptional_impossible n p hn hp hp2 e x hx I
        hI hnExceptional
  obtain ⟨s, H2bar, eH2, himage, hs, hseq, hn7, hsup⟩ := hdeg
  have hseq5 : s = 5 := hseq
  have hIle : I ≤ H2bar.comap q := by
    intro i hi
    change q i ∈ H2bar
    rw [← himage]
    exact Subgroup.mem_map_of_mem q hi
  have hIlift : I = (_root_.commutator (H2bar.comap q)).map
    (H2bar.comap q).subtype :=
    perfect_lift_eq_commutator_comap q hqker H2bar I hIle himage
      (inferInstance : Group.IsPerfect I).commutator_eq_top
  have hcenterEq5 : Nonempty (I ⧸ Subgroup.center I ≃* alternatingGroup (Fin 5)) :=
    component_centerQuotient_equiv_alternating_of_image_eq q hqker I H2bar himage
      5 (by omega) (hseq5 ▸ eH2)
  have hZdvd2 : Nat.card (Subgroup.center I) ∣ 2 :=
    center_card_dvd_two_of_centerQuotient_equiv_degree_five hcenterEq5
  set zcc : Nat := Nat.card (Subgroup.center K)
  have hcenterDvd : zcc ∣ 6 := by
    simpa [zcc] using exceptional_alternating_center_card_dvd_six n e hnExceptional
  have hzpos : 0 < zcc := by simp [zcc]
  have hzle6 : zcc ≤ 6 := Nat.le_of_dvd (by norm_num) hcenterDvd
  have hzc3 : 3 ∣ zcc := by simpa [zcc] using hthree
  have hcard36 : zcc = 3 ∨ zcc = 6 := by
    interval_cases zcc
    · exfalso; norm_num at hzc3
    · exfalso; norm_num at hzc3
    · exact Or.inl rfl
    · exfalso; norm_num at hzc3
    · exfalso; norm_num at hzc3
    · exact Or.inr rfl
  rcases hcard36 with hc3 | hc6
  · have hPbot : pCoreSubgroup 2 (Subgroup.center K) = ⊥ := by
      have hPdvd2 : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) ∣ 2 :=
        pCore_two_card_dvd_two_of_isInAlt hKAlt
      have hPdvd3 : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) ∣ 3 := by
        have hle := pCoreSubgroup_le 2 (Subgroup.center K)
        have hcenter3 : Nat.card (Subgroup.center K) = 3 := by simpa [zcc] using hc3
        exact (Subgroup.card_dvd_of_le hle).trans (by rw [hcenter3])
      have hcpos : 0 < Nat.card (pCoreSubgroup 2 (Subgroup.center K)) := Nat.card_pos
      have hcle2 : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) hPdvd2
      set c2 : Nat := Nat.card (pCoreSubgroup 2 (Subgroup.center K))
      have hcpos2 : 0 < c2 := by simp [c2]
      have hcle2' : c2 ≤ 2 := by simpa [c2] using hcle2
      have hc1 : c2 = 1 := by
        interval_cases c2
        · rfl
        · exfalso; norm_num at hPdvd3
      exact Subgroup.card_eq_one.mp (by simpa [c2] using hc1)
    rw [hPbot]
    exact bot_le
  · have htwo : 2 ∣ Nat.card (Subgroup.center K) := by
      have hcenter6 : Nat.card (Subgroup.center K) = 6 := by simpa [zcc] using hc6
      rw [hcenter6]
      norm_num
    obtain ⟨X, hXn, fbar, hXcenter, hfbarSurj, hfbarCenter, hfbarKerCard,
        hfactor, hdisjoint⟩ :=
      exists_exceptional_two_kernel_cover n hn e hnExceptional htwo
    let : X.Normal := hXn
    have hXp : IsPGroup 3 X := by
      exact __ch5_proposition_5_2_9_b_isPGroup_three_of_subgroup_disjoint_twoCore X hXcenter hdisjoint hc6
    let π : K →* (K ⧸ X) := QuotientGroup.mk' X
    let qn := n - 5
    have hqn : qn + 5 = n := Nat.sub_add_cancel hn
    let : IsQuasisimple (alternatingGroup (Fin n)) := by
      rw [← hqn]
      exact SchurPresentation.alternatingGroup_isQuasisimple qn
    have hcenterAlt : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
      apply alternatingGroup.center_eq_bot
      simpa using (show 4 ≤ n by omega)
    let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    have hkerCenter : fbar.ker = Subgroup.center (K ⧸ X) :=
      SchurPresentation.ker_eq_center_of_surjective_of_center_eq_bot
        fbar hfbarSurj hfbarCenter hcenterAlt
    let : IsQuasisimple (K ⧸ X) := {
      toIsPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective X)
      simple := by
        let ebar : (K ⧸ X) ⧸ Subgroup.center (K ⧸ X) ≃*
            alternatingGroup (Fin n) :=
          (QuotientGroup.quotientMulEquivOfEq hkerCenter.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective fbar hfbarSurj)
        exact (MulEquiv.isSimpleGroup_congr ebar).mpr
          (inferInstance : IsSimpleGroup (alternatingGroup (Fin n)))
    }
    let cX : Covering (K ⧸ X) (alternatingGroup (Fin n)) := {
      toMonoidHom := fbar
      surjective := hfbarSurj }
    have hroot : ∀ u : H2bar, (eH2 u).1.support.card = 4 → u.1.1.support.card = 4 := by
      intro u hu
      simpa [hsup u] using hu
    have hcenterXle : Subgroup.center (K ⧸ X) ≤
        (_root_.commutator (H2bar.comap fbar)).map
          (H2bar.comap fbar).subtype :=
      center_le_derived_alternating_preimage_of_double_cover
        n hn s hs cX hfbarKerCard H2bar eH2 hroot
    have hpiZmap : (Subgroup.center K).map π = Subgroup.center (K ⧸ X) := by
      exact center_map_eq_of_central_normal X hXcenter
    intro z hz
    have hzcenter : z ∈ Subgroup.center K := pCoreSubgroup_le 2 (Subgroup.center K) hz
    have hpi_z' : π z ∈ Subgroup.center (K ⧸ X) := by
      rw [← hpiZmap]
      exact ⟨z, pCoreSubgroup_le 2 (Subgroup.center K) hz, rfl⟩
    have hpi_der : π z ∈
        (_root_.commutator (H2bar.comap fbar)).map
          (H2bar.comap fbar).subtype := hcenterXle hpi_z'
    have hm_comm : I.map π =
        (_root_.commutator (H2bar.comap fbar)).map
          (H2bar.comap fbar).subtype := by
      rw [hIlift]
      have hf1 : (H2bar.comap q).map π = H2bar.comap fbar := by
        ext z0
        constructor
        · rintro ⟨g, hg, hgz⟩
          rw [← hgz]
          change fbar (π g) ∈ H2bar
          have hqg : q g ∈ H2bar := hg
          have hqf : fbar (π g) = q g := by
            exact congrArg (fun φ : K →* alternatingGroup (Fin n) => φ g) hfactor
          rw [hqf]
          exact hqg
        · intro hg
          obtain ⟨g, hgπ⟩ := QuotientGroup.mk'_surjective X (z0 : K ⧸ X)
          refine ⟨g, ?_, hgπ⟩
          change q g ∈ H2bar
          have hg_fbar : fbar z0 ∈ H2bar := hg
          rw [← hgπ] at hg_fbar
          have hqf : q g = fbar (π g) := by
            exact (congrArg (fun φ : K →* alternatingGroup (Fin n) => φ g) hfactor).symm
          rw [hqf]
          exact hg_fbar
      calc
        ((_root_.commutator (H2bar.comap q)).map (H2bar.comap q).subtype).map π
            = (_root_.commutator (H2bar.comap q)).map
                (π.comp (H2bar.comap q).subtype) := by
                ext z0
                constructor
                · rintro ⟨g, hg, hgz⟩
                  rcases Subgroup.mem_map.mp hg with ⟨c, hc, hgc⟩
                  refine ⟨c, hc, ?_⟩
                  rw [← hgc] at hgz
                  simpa [← hgc] using hgz
                · rintro ⟨c, hc, hcz⟩
                  refine ⟨(H2bar.comap q).subtype c, ⟨c, hc, rfl⟩, ?_⟩
                  exact hcz
        _ = ⁅Subgroup.map (π.comp (H2bar.comap q).subtype) (⊤ : Subgroup
            (↥(H2bar.comap q))), Subgroup.map (π.comp (H2bar.comap q).subtype)
            (⊤ : Subgroup (↥(H2bar.comap q)))⁆ := by
            rw [show Subgroup.map (π.comp (H2bar.comap q).subtype)
                  (_root_.commutator (H2bar.comap q)) =
                  Subgroup.map (π.comp (H2bar.comap q).subtype)
                    ⁅(⊤ : Subgroup (↥(H2bar.comap q))),
                      (⊤ : Subgroup (↥(H2bar.comap q)))⁆ by rfl]
            rw [Subgroup.map_commutator (⊤ : Subgroup (↥(H2bar.comap q)))
                (⊤ : Subgroup (↥(H2bar.comap q)))
                (π.comp (H2bar.comap q).subtype)]
        _ = ⁅(H2bar.comap q).map π, (H2bar.comap q).map π⁆ := by
            have hTop : Subgroup.map (π.comp (H2bar.comap q).subtype)
                (⊤ : Subgroup (↥(H2bar.comap q))) =
                (H2bar.comap q).map π := by
              ext z0
              constructor
              · rintro ⟨e, _, hz⟩
                exact ⟨e.1, e.2, hz⟩
              · rintro ⟨e, he, hz⟩
                exact ⟨⟨e, he⟩, trivial, hz⟩
            rw [hTop]
        _ = ⁅H2bar.comap fbar, H2bar.comap fbar⁆ := by
            rw [hf1]
        _ = (_root_.commutator (H2bar.comap fbar)).map
            (H2bar.comap fbar).subtype := by
            exact (Subgroup.map_subtype_commutator (H2bar.comap fbar)).symm
    obtain ⟨d, hd, hd_eq⟩ := Subgroup.mem_map.mp (by
      rw [hm_comm]
      exact hpi_der)
    have hdzX : z * d⁻¹ ∈ X := by
      have hπd : π z = π d := hd_eq.symm
      have : π (z * d⁻¹) = 1 := by
        rw [map_mul, map_inv, hπd, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (z * d⁻¹)).mp (by simpa [π] using this)
    have hdzinv : d⁻¹ * z ∈ X := by
      have hz_center : Commute z d := by
        exact (Subgroup.mem_center_iff.mp hzcenter d).symm
      rw [← hz_center.inv_right.eq]
      exact hdzX
    let a : K := d⁻¹ * z
    have haX : a ∈ X := hdzinv
    have hz_eq : z = d * a := by simp [a]
    have ha_d_eq : d = z * a⁻¹ := by
      rw [hz_eq]
      simp [mul_assoc]
    have hd_center : d ∈ Subgroup.center K := by
      apply hqker
      rw [MonoidHom.mem_ker]
      have hzq : q z = 1 := by
        have hzker : z ∈ q.ker := by
          rw [alternatingQuotientHom_ker e]
          exact hzcenter
        exact (MonoidHom.mem_ker).mp hzker
      have haq : q a = 1 := by
        have hale : a ∈ Subgroup.center K := hXcenter haX
        have haker : a ∈ q.ker := by
          rw [alternatingQuotientHom_ker e]
          exact hale
        exact (MonoidHom.mem_ker).mp haker
      rw [ha_d_eq, map_mul, map_inv, hzq, haq]
      simp
    have hd_of_I : d ∈ I := by
      exact hd
    have hd_center_I : (⟨d, hd_of_I⟩ : I) ∈ Subgroup.center I := by
      rw [Subgroup.mem_center_iff]
      intro i
      apply Subtype.ext
      apply Subgroup.mem_center_iff.mp hd_center i.1
    have hd_ord_dvd : orderOf d ∣ Nat.card (Subgroup.center I) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center I) hd_center_I
      rwa [← Subgroup.orderOf_coe ⟨d, hd_of_I⟩] at h
    have hd_ord_le : orderOf d ∣ 2 := hd_ord_dvd.trans hZdvd2
    have ha_ne : a = 1 := by
      by_contra ha1
      have hord_a : ∃ k : Nat, orderOf a = 3 ^ k := by
        let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        rcases (IsPGroup.iff_orderOf.mp hXp ⟨a, haX⟩) with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        exact (Subgroup.orderOf_coe ⟨a, haX⟩).trans hk
      obtain ⟨k, hk⟩ := hord_a
      have hk_ge : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        rw [this, pow_zero] at hk
        exact ha1 (orderOf_eq_one_iff.mp hk)
      have h3_dvd_a : 3 ∣ orderOf a := by
        rw [hk]
        exact dvd_pow_self 3 (by omega)
      have hcop_z_a : (orderOf z).Coprime (orderOf a) := by
        have hz2 : IsPGroup 2 (pCoreSubgroup 2 (Subgroup.center K)) :=
          pCoreSubgroup_isPGroup 2 (Subgroup.center K)
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hzcop3 : (orderOf z).Coprime 3 :=
          by
            have h := hz2.orderOf_coprime (n := 3) (by norm_num) ⟨z, hz⟩
            rw [← Subgroup.orderOf_coe ⟨z, hz⟩] at h
            exact h
        have : Nat.Coprime (orderOf z) (orderOf a) := by
          -- both are powers: z is a 2-power (coprime to 3), a is a 3-power
          rw [hk]
          exact hzcop3.pow_right k
        simpa using this
      have hcomm_za : Commute z a⁻¹ := by
        exact (Subgroup.mem_center_iff.mp hzcenter a⁻¹).symm
      have hord_d : orderOf d = orderOf z * orderOf a := by
        rw [ha_d_eq]
        have ht := hcomm_za.orderOf_mul_eq_mul_orderOf_of_coprime
          (by simpa using hcop_z_a)
        rw [ht]
        rw [orderOf_inv]
      have h3_dvd_d : 3 ∣ orderOf d := by
        rw [hord_d]
        exact dvd_mul_of_dvd_right h3_dvd_a (orderOf z)
      have hd_ord_eq : orderOf d = 1 ∨ orderOf d = 2 := by
        exact (Nat.dvd_prime Nat.prime_two).mp hd_ord_le
      rcases hd_ord_eq with h1 | h2
      · rw [h1] at h3_dvd_d
        norm_num at h3_dvd_d
      · rw [h2] at h3_dvd_d
        norm_num at h3_dvd_d
    have hz_i : z ∈ I := by
      rw [hz_eq, ha_ne]
      simpa using hd_of_I
    rw [Subgroup.mem_map]
    refine ⟨⟨z, hz_i⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcenter y.1



private theorem __ch5_proposition_5_2_9_b_isPGroup_two_of_card_dvd_two
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G ∣ 2) :
    IsPGroup 2 G := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hcard with hcard | hcard
  · apply IsPGroup.of_card (n := 0)
    simpa using hcard
  · apply IsPGroup.of_card (n := 1)
    simpa using hcard

public theorem proposition_5_2_9_b
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hKAlt : IsInAlt K) (p : Nat) (hp : p.Prime)
    (x : MulAut K) (hx : orderOf x = p)
    (I : Subgroup K)
    (hI : IsComponentOf I (automorphismFixedSubgroup x) ∨
      IsPComponentOf p I (automorphismFixedSubgroup x)) :
    (Subgroup.center I).map I.subtype =
      pCoreSubgroup 2 (Subgroup.center K) := by
  have hKAlt' := hKAlt
  rw [isInAlt_iff_exists_center_quotient] at hKAlt
  obtain ⟨n, _Z, hn, _hZ, ⟨e⟩⟩ := hKAlt
  have hIcomponent : IsComponentOf I (automorphismFixedSubgroup x) :=
    hI.elim id (isComponentOf_of_isPComponentOf p I
      (automorphismFixedSubgroup x))
  let q : K →* alternatingGroup (Fin n) := alternatingQuotientHom e
  have hq : Function.Surjective q := alternatingQuotientHom_surjective e
  have hqker : q.ker ≤ Subgroup.center K := by
    rw [alternatingQuotientHom_ker e]
  let : IsQuasisimple I := hIcomponent.2.2
  obtain ⟨H2bar, himage, s, hs, eH2, heH2support⟩ :
      ∃ H2bar : Subgroup (alternatingGroup (Fin n)),
        I.map q = H2bar ∧ ∃ s : Nat, 5 ≤ s ∧
          ∃ eH2 : H2bar ≃* alternatingGroup (Fin s),
            ∀ u : H2bar,
              (eH2 u).1.support.card = u.1.1.support.card := by
    by_cases hp2 : p = 2
    · simpa [q] using
        involution_component_image_eq_alternatingFactor_with_support
          n hn e x (by simpa [hp2] using hx) I hIcomponent
    · simpa [q] using
        oddPrime_component_image_eq_alternatingFactor n p hn hp hp2 e x hx I
          hIcomponent
  have hcenterLe : (Subgroup.center I).map I.subtype ≤
      Subgroup.center K :=
    center_map_le_center_of_image_eq_centerless q hqker I H2bar himage s hs eH2
  have hcenterEq_of_card_dvd_two
      (hcard : Nat.card (Subgroup.center K) ∣ 2) :
      (Subgroup.center I).map I.subtype =
        pCoreSubgroup 2 (Subgroup.center K) := by
    have hcenterI2 : IsPGroup 2 (Subgroup.center I) := by
      have hmapDvd : Nat.card ((Subgroup.center I).map I.subtype) ∣ 2 :=
        (Subgroup.card_dvd_of_le hcenterLe).trans hcard
      have hmapCard : Nat.card ((Subgroup.center I).map I.subtype) =
          Nat.card (Subgroup.center I) := by
        exact Subgroup.card_map_of_injective I.subtype_injective
      apply __ch5_proposition_5_2_9_b_isPGroup_two_of_card_dvd_two
      rwa [hmapCard] at hmapDvd
    apply center_map_eq_pCoreSubgroup_of_two_primary I hcenterLe hcenterI2
    by_cases hPone : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) = 1
    · rw [Subgroup.card_eq_one.mp hPone]
      exact bot_le
    · have hPtwo : Nat.card (pCoreSubgroup 2 (Subgroup.center K)) = 2 := by
        have hPdvd := pCore_two_card_dvd_two_of_isInAlt hKAlt'
        exact (Nat.dvd_prime Nat.prime_two).mp hPdvd |>.resolve_left hPone
      have hcenterP : IsPGroup 2 (Subgroup.center K) :=
        __ch5_proposition_5_2_9_b_isPGroup_two_of_card_dvd_two hcard
      have htwoDvd : 2 ∣ Nat.card (Subgroup.center K) := by
        have hPle := pCoreSubgroup_le 2 (Subgroup.center K)
        have hdiv := Subgroup.card_dvd_of_le hPle
        simpa [hPtwo] using hdiv
      have hcenterTwo : Nat.card (Subgroup.center K) = 2 :=
        two_primary_alternating_center_card_eq_two n hn e hcenterP htwoDvd
      let qn := n - 5
      have hqn : qn + 5 = n := Nat.sub_add_cancel hn
      let : IsQuasisimple (alternatingGroup (Fin n)) := by
        rw [← hqn]
        exact SchurPresentation.alternatingGroup_isQuasisimple qn
      let c : Covering K (alternatingGroup (Fin n)) := {
        toMonoidHom := q
        surjective := hq }
      have hkerCard : Nat.card c.toMonoidHom.ker = 2 := by
        change Nat.card q.ker = 2
        rw [alternatingQuotientHom_ker e, hcenterTwo]
      have hroot : ∀ u : H2bar,
          (eH2 u).1.support.card = 4 → u.1.1.support.card = 4 := by
        intro u hu
        simpa [heH2support u] using hu
      have hIle : I ≤ H2bar.comap q := by
        intro i hi
        change q i ∈ H2bar
        rw [← himage]
        exact Subgroup.mem_map_of_mem q hi
      have hIlift : I = (_root_.commutator (H2bar.comap q)).map
          (H2bar.comap q).subtype :=
        perfect_lift_eq_commutator_comap q hqker H2bar I hIle himage
          (inferInstance : Group.IsPerfect I).commutator_eq_top
      have hcenterD : Subgroup.center K ≤
          (_root_.commutator (H2bar.comap q)).map
            (H2bar.comap q).subtype :=
        center_le_derived_alternating_preimage_of_double_cover
          n hn s hs c hkerCard H2bar eH2 hroot
      intro z hz
      have hzCenter : z ∈ Subgroup.center K :=
        pCoreSubgroup_le 2 (Subgroup.center K) hz
      have hzI : z ∈ I := by
        rw [hIlift]
        exact hcenterD hzCenter
      rw [Subgroup.mem_map]
      refine ⟨⟨z, hzI⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzCenter y.1
  by_cases hnExceptional : n = 6 ∨ n = 7
  · by_cases hthree : 3 ∣ Nat.card (Subgroup.center K)
    · -- exceptional three-primary core: transfer through the quotient-by-3-core cover
      have hdeg5 :
          ∃ (s5 : Nat) (H2bar5 : Subgroup (alternatingGroup (Fin n)))
            (eH25 : H2bar5 ≃* alternatingGroup (Fin s5)),
            I.map q = H2bar5 ∧ 5 ≤ s5 ∧ s5 = 5 ∧ n = 7 ∧
              ∀ u : H2bar5,
                (eH25 u).1.support.card = u.1.1.support.card := by
        by_cases hp2 : p = 2
        · simpa [q] using involution_component_degree_five_of_exceptional
            n hn e x (by simpa [hp2] using hx) I hIcomponent hnExceptional
        · exfalso
          exact oddPrime_component_exceptional_impossible n p hn hp hp2 e x hx
            I hIcomponent hnExceptional
      obtain ⟨s5, H2bar5, eH25, himage5, hs5, hseq5, hn7, hsup5⟩ := hdeg5
      have hcenterEq5 : Nonempty (I ⧸ Subgroup.center I ≃*
          alternatingGroup (Fin 5)) :=
        component_centerQuotient_equiv_alternating_of_image_eq q hqker I H2bar5
          himage5 5 (by omega) (hseq5 ▸ eH25)
      have hcenterI2 : IsPGroup 2 (Subgroup.center I) :=
        isPGroup_two_of_centerQuotient_equiv_degree_five hcenterEq5
      have hrev : pCoreSubgroup 2 (Subgroup.center K) ≤
          (Subgroup.center I).map I.subtype :=
        exceptionalThreePrimary_pCore_two_le_center_image n hn e hnExceptional
          hthree p hp x hx I hIcomponent
      exact center_map_eq_pCoreSubgroup_of_two_primary I hcenterLe hcenterI2 hrev
    · have hcard : Nat.card (Subgroup.center K) ∣ 2 := by
        have h6 := exceptional_alternating_center_card_dvd_six n e hnExceptional
        let zc : Nat := Nat.card (Subgroup.center K)
        have hzpos : 0 < zc := by simp [zc]
        have hzle6 : zc ≤ 6 := by
          simpa [zc] using Nat.le_of_dvd (by norm_num) h6
        have hzc6 : zc ∣ 6 := by simpa [zc] using h6
        have hzc3 : ¬ 3 ∣ zc := by simpa [zc] using hthree
        have hcard' : zc ∣ 2 := by
          interval_cases hz : zc
          · norm_num
          · norm_num
          · exfalso
            norm_num at hzc3
          · exfalso
            norm_num at hzc6
          · exfalso
            norm_num at hzc6
          · exfalso
            norm_num at hzc3
        exact by simpa [zc] using hcard'
      exact hcenterEq_of_card_dvd_two hcard
  · have hcard : Nat.card (Subgroup.center K) ∣ 2 :=
      alternating_center_card_dvd_two_of_nonexceptional n hn
        (fun h => hnExceptional (Or.inl h))
        (fun h => hnExceptional (Or.inr h)) e
    exact hcenterEq_of_card_dvd_two hcard

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.proposition_5_2_9_b -/

