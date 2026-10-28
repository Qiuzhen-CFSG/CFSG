module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual
public import BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Residual commutators in an elementary central layer

Let `R = O²(G)` in a finite group. If `Q` and `U` are normal, `Z` is
an elementary abelian 2-subgroup, `[Q,R] ≤ Z`, and `[Z,R] ≤ U`, then
`[Q,R] ≤ U`. No containment between `Q`, `U`, and `Z` is required.
This is the graph-independent transfer used in the distance-two argument
of Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.2), p. 14,
within the proof of Theorem 2 of Stellmacher's N-group paper (1997).

Modulo `U`, every residual commutator lies in an elementary layer fixed by
`R`. The commutator identity therefore shows that every square in `R`
centralizes the image of `Q`. Intersect the inverse image of that centralizer
with `R`, obtaining a normal subgroup `C`. Both `R/C` and `G/R` are 2-groups,
so `G/C` is a 2-group. Residual minimality forces `R ≤ C`, giving the result.

The imported source-neutral residual module supplies only the identification
of the index-based ambient residual with Huppert's quotient-based residual;
its dependency closure contains no numbered Section 3 results.
-/

open scoped commutatorElement
open Subgroup BenderSuzuki.External
namespace Stellmacher

private theorem hktResidual_commutator_le_of_central_layer
    {G : Type*} [Group G] [Finite G] (Q U Z : Subgroup G)
    [Q.Normal] [U.Normal] [IsElementaryAbelian 2 Z]
    (hQ : ⁅Q, hktPResidual 2 G⁆ ≤ Z)
    (hZ : ⁅Z, hktPResidual 2 G⁆ ≤ U) : ⁅Q, hktPResidual 2 G⁆ ≤ U := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := hktPResidual 2 G
  let _ : R.Normal := hktPResidual_normal
  let q := QuotientGroup.mk' U
  let Qbar := Q.map q
  let C := (centralizer (Qbar : Set (G ⧸ U))).comap q ⊓ R
  have hQbar : Qbar.Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective U)
  let _ : Qbar.Normal := hQbar
  have hC : C.Normal := inferInstance
  let _ : C.Normal := hC
  have hsq (r : R) : (r : G) ^ 2 ∈ C := by
    refine ⟨?_, R.pow_mem r.property 2⟩
    change q ((r : G) ^ 2) ∈ centralizer (Qbar : Set (G ⧸ U))
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨a, ha, rfl⟩ := hw
    have hc : ⁅(r : G), a⁆ ∈ Z := by
      rw [commutator_comm] at hQ
      exact hQ (commutator_mem_commutator r.property ha)
    have hrc : ⁅(r : G), ⁅(r : G), a⁆⁆ ∈ U := by
      rw [commutator_comm] at hZ
      exact hZ (commutator_mem_commutator r.property hc)
    have hfix :
        q (r : G) * q ⁅(r : G), a⁆ * (q (r : G))⁻¹ = q ⁅(r : G), a⁆ := by
      have hh : ⁅q (r : G), q ⁅(r : G), a⁆⁆ = 1 := by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr hrc
      have hh' := commutatorElement_eq_one_iff_mul_comm.mp hh
      rw [hh']
      simp [mul_assoc]
    have hpow : ⁅(r : G), a⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
    have hh : ⁅q ((r : G) ^ 2), q a⁆ = 1 := by
      rw [map_pow, pow_two, commutatorElement_mul_left_eq_conj_mul,
        ← map_commutatorElement, hfix, ← pow_two, ← map_pow, hpow, map_one]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  let qC := QuotientGroup.mk' C
  let Rbar := R.map qC
  have hRbar : Rbar.Normal :=
    Subgroup.Normal.map inferInstance qC (QuotientGroup.mk'_surjective C)
  let _ : Rbar.Normal := hRbar
  have hRbarTwo : IsPGroup 2 Rbar := by
    intro x
    obtain ⟨r, hr, hxr⟩ := x.property
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (x : G ⧸ C) ^ (2 ^ 1) = 1
    rw [pow_one, ← hxr, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq ⟨r, hr⟩)
  have hquotRbar : IsPGroup 2 ((G ⧸ C) ⧸ Rbar) := by
    have hquotR : IsPGroup 2 (G ⧸ R) := hktPResidual_quotient_isPGroup
    let e : ((G ⧸ C) ⧸ Rbar) ≃* G ⧸ R :=
      (QuotientGroup.quotientQuotientEquivQuotient C R inf_le_right).trans
        (QuotientGroup.quotientMulEquivOfEq (by rfl))
    exact hquotR.of_equiv e.symm
  have hquotC : IsPGroup 2 (G ⧸ C) :=
    hkt_isPGroup_of_normal_quotient Rbar hRbarTwo hquotRbar
  have hRC : R ≤ C := hktPResidual_le C hC hquotC
  rw [commutator_le]
  intro a ha r hr
  have hc := (hRC hr).1
  change q r ∈ centralizer (Qbar : Set (G ⧸ U)) at hc
  have hh := mem_centralizer_iff.mp hc (q a) (mem_map_of_mem q ha)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅a, r⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hh

/-- A residual commutator contained in an elementary layer already lies in any
normal subgroup modulo which the residual centralizes that layer. -/
public theorem residual_commutator_le_of_central_layer
    {G : Type*} [Group G] [Finite G] (Q U Z : Subgroup G)
    [Q.Normal] [U.Normal] [IsElementaryAbelian 2 Z]
    (hQ : ⁅Q, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ Z)
    (hZ : ⁅Z, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ U) :
    ⁅Q, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ U := by
  rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hQ hZ ⊢
  exact hktResidual_commutator_le_of_central_layer Q U Z hQ hZ
end Stellmacher
