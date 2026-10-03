module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Fixed-point splitting over a central two-layer

Let a finite group E have no nontrivial two-group quotient and an odd
quotient over a normal two-subgroup U. Suppose E normalizes a
two-subgroup B, [B,E] lies in V≤B, and [B,U] lies in an E-central layer
Z≤B. Then B is the join of V and C_B(E). No subgroup is assumed normal
in the ambient group; the no-two-quotient hypothesis is intrinsic to E.

The two-group B is solvable. An odd Schur-Zassenhaus complement R to U
acts coprimely on B, giving
B=[B,R] C_B(R). The central layer lies in C_B(R), so the U-commutator
bound makes this fixed subgroup E-invariant. R acts trivially on it;
therefore its E-action image is an image of U and is a two-group. The
no-two-quotient hypothesis kills this action, identifying C_B(R) with
C_B(E). The remaining commutator factor lies in V.

This gives the fixed-component step in Stellmacher (10.1)(16), Journal
of Algebra 190 (1997), printed p.64, uniformly for either odd residual
prime. Its source-facing application supplies residual perfection and
the central-layer bound from separate theorems. The general version also
supplies the final source-(20) centralizer reduction on printed p.65, where
B need not be abelian. The original abelian API remains a wrapper.
-/

namespace Subgroup
open scoped IsMulCommutative commutatorElement
public theorem eq_sup_centralizer_of_no_two_quotient_central_layer_of_isPGroup
    {G : Type*} [Group G] [Finite G]
    (E U B V Z : Subgroup G)
    (hUE : U≤E) (hU : IsPGroup 2 U) (hB : IsPGroup 2 B)
    [hN : (U.subgroupOf E).Normal]
    (hodd : Odd (Nat.card (E ⧸ U.subgroupOf E)))
    (hperfect : ∀ N : Subgroup E, ∀ hN : N.Normal,
      let _ := hN
      IsPGroup 2 (E ⧸ N) → N=⊤)
    (hEB : E≤normalizer (B:Set G)) (hVB : V≤B)
    (hZB : Z≤B) (hZC : Z≤centralizer (E:Set G))
    (hBE : ⁅B,E⁆≤V) (hBU : ⁅B,U⁆≤Z) :
    B=V⊔(B⊓centralizer (E:Set G)) := by
  let U0:=U.subgroupOf E
  have hU0 : IsPGroup 2 U0 := hU.of_equiv (subgroupOfEquivOfLe hUE).symm
  have hUodd : Odd U0.index := hodd
  have hcop : Nat.Coprime (Nat.card U0) U0.index := by
    obtain ⟨n,hn⟩:=hU0.exists_card_eq
    rw [hn]
    exact hUodd.coprime_two_left.pow_left n
  obtain ⟨R0,hR0⟩:=exists_right_complement'_of_coprime hcop
  let R:=R0.map E.subtype
  have hRE : R≤E := map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [card_map_of_injective E.subtype_injective,←hR0.symm.index_eq_card]
    exact hUodd
  have hEgen : U⊔R=E := by
    have hh:=congrArg (map E.subtype) hR0.sup_eq_top
    rw [map_sup,map_subgroupOf_eq_of_le hUE,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  let C:=B⊓centralizer (R:Set G)
  have hZC0 : Z≤C := le_inf hZB (hZC.trans (centralizer_le hRE))
  have hUC : U≤normalizer (C:Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_left le_rfl).trans hBU).trans hZC0)
  have hRC : R≤normalizer (C:Set G) :=
    (le_centralizer_iff.mp (show C≤centralizer (R:Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hEC : E≤normalizer (C:Set G) := by rw [←hEgen]; exact sup_le hUC hRC
  let action : E→*MulAut C := C.normalizerMonoidHom.comp (inclusion hEC)
  have hRker : R0≤action.ker := by
    intro r hr
    apply MonoidHom.mem_ker.mpr
    ext c
    change (r:G)*(c:G)*(r:G)⁻¹=(c:G)
    have hc: (r:G)*(c:G)=(c:G)*(r:G) :=
      mem_centralizer_iff.mp c.property.2 r (mem_map_of_mem E.subtype hr)
    rw [hc,mul_inv_cancel_right]
  have hRimage : R0.map action=⊥ := by
    rw [map_eq_bot_iff]
    exact hRker
  have hrange : action.range=U0.map action := by
    rw [MonoidHom.range_eq_map,←hR0.sup_eq_top,map_sup,hRimage,sup_bot_eq]
  have htwo : IsPGroup 2 action.range := by
    rw [hrange]
    exact hU0.map action
  have hquot : IsPGroup 2 (E⧸action.ker) :=
    htwo.of_equiv (QuotientGroup.quotientKerEquivRange action).symm
  have hker := hperfect action.ker inferInstance hquot
  have hCCE : C≤centralizer (E:Set G) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro e he
    have hh : action ⟨e,he⟩=1 := by
      apply MonoidHom.mem_ker.mp
      rw [hker]
      trivial
    have hf := congrArg (fun f:MulAut C=>(f ⟨c,hc⟩:G)) hh
    change e*c*e⁻¹=c at hf
    exact mul_inv_eq_iff_eq_mul.mp hf
  have hcopB : Nat.Coprime (Nat.card R) (Nat.card B) := by
    obtain ⟨n,hn⟩:=hB.exists_card_eq
    rw [hn]
    exact hRodd.coprime_two_right.pow_right n
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime B R
    (hRE.trans hEB) (@IsNilpotent.to_isSolvable B inferInstance hB.isNilpotent) hcopB
  apply le_antisymm
  · exact hsplit.le.trans (sup_le
      (((commutator_mono le_rfl hRE).trans hBE).trans le_sup_left)
      ((le_inf inf_le_left hCCE).trans le_sup_right))
  · exact sup_le hVB inf_le_left
public theorem eq_sup_centralizer_of_no_two_quotient_central_layer
    {G : Type*} [Group G] [Finite G]
    (E U B V Z : Subgroup G) [IsMulCommutative B]
    (hUE : U≤E) (hU : IsPGroup 2 U) (hB : IsPGroup 2 B)
    [hN : (U.subgroupOf E).Normal]
    (hodd : Odd (Nat.card (E ⧸ U.subgroupOf E)))
    (hperfect : ∀ N : Subgroup E, ∀ hN : N.Normal,
      let _ := hN
      IsPGroup 2 (E ⧸ N) → N=⊤)
    (hEB : E≤normalizer (B:Set G)) (hVB : V≤B)
    (hZB : Z≤B) (hZC : Z≤centralizer (E:Set G))
    (hBE : ⁅B,E⁆≤V) (hBU : ⁅B,U⁆≤Z) :
    B=V⊔(B⊓centralizer (E:Set G)) := by
  exact eq_sup_centralizer_of_no_two_quotient_central_layer_of_isPGroup
    E U B V Z hUE hU hB hodd hperfect hEB hVB hZB hZC hBE hBU
end Subgroup
