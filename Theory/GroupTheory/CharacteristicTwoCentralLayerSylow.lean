module

public import Theory.PGroupCore
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.Tactic.Group

/-!
# A central commutator layer identifies the Sylow two-core

Let N be finite of characteristic two, meaning C_N(O₂(N)) ≤ O₂(N).
Suppose a normal subgroup Z lies in both O₂(N) and the center of N. If
the commutators of a supplied Sylow two-subgroup Q lie in Z, then Q=O₂(N).
The theorem retains the supplied Sylow and central layer. It does not require
Z to be characteristic in O₂(N), or assume any quotient action.

Put R=O₂(N) and let K be the full subgroup centralizing R modulo Z,
represented by the commutator preimage. Normality of R and Z makes K normal,
and R≤Q with [Q,Q]≤Z gives Q≤K. Centrality of Z makes
k ↦ (r ↦ [r,k]) a homomorphism from K to the function group R→Z. Its kernel
centralizes R, so characteristic two places that kernel in R. Both kernel
and function group are two-groups. Thus K is a normal two-group and lies in
R, proving Q≤K≤R≤Q.

This source-neutral argument supplies O₂(C_H(Zmiddle))=Qmiddle before
Stellmacher (10.1)(a3), identity (7), printed p.61 of
`refs/files/stellmacher-n-group.pdf`. The ambient normalizer adapter supplies
the hypotheses separately.
-/

namespace Subgroup
open scoped commutatorElement

/-- A Sylow two-subgroup whose commutators lie in a central core layer is the two-core
when the ambient group has characteristic two. -/
public theorem sylow_two_eq_pCore_of_commutator_le_central_layer
    {N : Type*} [Group N] [Finite N]
    (Q : Sylow 2 N) (Z : Subgroup N) [Z.Normal]
    (hZcore : Z ≤ pCore 2 N) (hZcentral : Z ≤ center N)
    (hchar : centralizer (pCore 2 N : Set N) ≤ pCore 2 N)
    (hcomm : ⁅(Q : Subgroup N), (Q : Subgroup N)⁆ ≤ Z) :
    (Q : Subgroup N) = pCore 2 N := by
  let R := pCore 2 N
  let K := commutatorPreimage ⊤ R Z
  have hRQ : R ≤ Q := pCore_isPGroup.le_sylow_of_normal Q
  have hKR : ⁅K, R⁆ ≤ Z :=
    commutator_commutatorPreimage_le ⊤ R Z le_normalizer_of_normal
  have hRK : ⁅R, K⁆ ≤ Z := by rwa [commutator_comm]
  have hQK : (Q : Subgroup N) ≤ K :=
    le_commutatorPreimage le_top ((commutator_mono le_rfl hRQ).trans hcomm)
  have hnormalizer : (⊤ : Subgroup N) ≤ normalizer (K : Set N) :=
    commutatorPreimage_normalized ⊤ R Z ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
  let _ : K.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hnormalizer)
  have hvalue (k : K) (r : R) : ⁅(r : N), (k : N)⁆ ∈ Z :=
    hRK (commutator_mem_commutator r.property k.property)
  let displacement : K →* (R → Z) := {
    toFun := fun k r => ⟨⁅(r : N), (k : N)⁆, hvalue k r⟩
    map_one' := by funext r; exact Subtype.ext (by simp)
    map_mul' := by
      intro k l
      funext r
      apply Subtype.ext
      change ⁅(r : N), (k : N) * (l : N)⁆ =
        ⁅(r : N), (k : N)⁆ * ⁅(r : N), (l : N)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_center_iff.mp (hZcentral (hvalue l r)) (k : N)
      calc
        _ = ⁅(r : N), (k : N)⁆ * ((k : N) * ⁅(r : N), (l : N)⁆) * (k : N)⁻¹ := by group
        _ = _ := by rw [hc]; group }
  have hkernel : displacement.ker ≤ R.subgroupOf K := by
    intro k hk
    apply hchar
    rw [mem_centralizer_iff]
    intro r hr
    have hh := congrArg (fun f : R → Z => (f ⟨r, hr⟩ : N))
      (MonoidHom.mem_ker.mp hk)
    change ⁅r, (k : N)⁆ = 1 at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hh
  have hkernelTwo : IsPGroup 2 displacement.ker :=
    pCore_isPGroup.comap_subtype.to_le hkernel
  have hZtwo : IsPGroup 2 Z := pCore_isPGroup.to_le hZcore
  have hfunctions : IsPGroup 2 (R → Z) := by
    obtain ⟨n, hn⟩ := hZtwo.exists_card_dvd_pow
    intro f
    refine ⟨n, ?_⟩
    funext r
    exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard (f r)).trans hn)
  have hKtwo : IsPGroup 2 K := by
    have hpre := (hfunctions.to_subgroup ⊤).comap_of_ker_isPGroup displacement hkernelTwo
    rw [comap_top] at hpre
    exact hpre.of_equiv topEquiv
  exact le_antisymm (hQK.trans (le_sSup ⟨inferInstance, hKtwo⟩)) hRQ

end Subgroup
