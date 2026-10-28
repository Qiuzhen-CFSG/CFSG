module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.Representation.BinaryOffender.SmallMovedInvolutions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
/-!
# The hyperplane branch of the B.5.13 dual numerical bound

The first factor in B.5.6(5) is SL₃(2), with a three-dimensional moved
space in the actual dual module. Its trivial two-core makes the action on
that moved space faithful. An involution displaces the full dual module
into its proper fixed subspace there, of dimension at most two.
Contragredience preserves an individual element's displacement rank, giving
the required quadratic ratio bound on the original representation.

This consumes the literal `HyperplaneCase`; it needs no extra splitting or
coordinate marking. Source: Aschbacher–Smith B.5.13, printed p.110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V]

/-- The hyperplane alternative gives the bound using only its original
faithfulness and trivial-two-core hypotheses. -/
theorem quadraticRatio_le_two_of_hyperplane (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ.dual) (hc : pCore 2 D = ⊥)
    (c : HyperplaneCase ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let reverse : InternalProduct c.second c.first :=
    ⟨MulEquiv.prodComm.trans c.product.equiv, fun b a => by
      have he : c.product.equiv ((a,1) * (1,b)) =
          c.product.equiv ((1,b) * (a,1)) := by simp
      rw [map_mul, map_mul] at he
      change c.product.equiv (a,b) = (b : D) * (a : D)
      rw [c.product.apply_eq]
      simpa only [c.product.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using he⟩
  let : c.first.Normal := reverse.second_normal
  let U := (MovedSection.ofNormal ρ.dual c.first).space
  have hcard : Nat.card c.first = 168 := by
    rw [Nat.card_congr c.firstEquiv.toEquiv,
      Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv,
      ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 3).toEquiv,
      Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := c.first) 2
    (show 2 ∣ Nat.card c.first by rw [hcard]; decide)
  have hb := fixedCodim_involution_le_two_of_small_moved ρ.dual hf c.first
    (reverse.second_twoCore hc) U rfl (by exact c.firstDimension.le.trans (by decide)) t ht
  have htD : orderOf (t : D) = 2 :=
    (orderOf_injective c.first.subtype c.first.subtype_injective t).trans ht
  obtain ⟨he,hr,hq,_⟩ := involution_actor_rank_and_fixedCodim ρ (t : D) htD
  rw [fixedCodim_zpowers_dual] at hb
  apply (quadraticRatio_le_two_iff ρ).mpr
  exact ⟨zpowers (t : D),he,hq,by omega⟩
/-- The actual B.5.3 classification consumer for the hyperplane branch. -/
theorem quadraticRatio_le_two_of_hyperplane_source
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : HyperplaneCase ρ.dual) :
    quadraticRatio ρ ≤ 2 :=
  quadraticRatio_le_two_of_hyperplane ρ h.faithful h.twoCore c

end CFSG.Quasithin.ChapterB.SourceB513
