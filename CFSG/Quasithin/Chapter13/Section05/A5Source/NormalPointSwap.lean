module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSplit
public import Theory.GroupTheory.QuaternionCentralProductResidualSwap

/-!
# The original module involution and the exchanged residual factors

The elementary source module makes every displacement of its actors singular
in the quaternion square form. An actor outside O2(H) therefore exchanges the
two intrinsic quaternion factors and their actual SL2(3) residual extensions.
For the chosen involution its fixed core is an elementary eight. The original
seed V3 is contained in it and has the same order, so V is recovered as
C_{O2(H)}(v)⟨v⟩.

In the ordinary source branch M=L, the final theorem retains one witness v
for the residual complement, both exchange identities, the central line V1
and this module marking. Together with NormalPointSplit's intrinsic Borel
N_H(V), this supplies the source side of the marked point comparison.
The concrete unitary matrix endpoint and the two amalgam commuting squares
remain separate obligations.

Source: Aschbacher--Smith 13.5.15(8), 13.5.17 and F.9.5(6), printed
pp.920--922 and319; the intrinsic residual factors use14.2.21, p.988.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

omit hn in
private theorem normal_module_singular_actor (q : QuaternionCentralProductData (pCore 2 H))
    (v : H) (hv : (v : G) ∈ V) :
    BinaryFourPlus.SingularDisplacements (q.quotientWreathAction (MulAut.conjNormal v)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hnV : ¬ V ≤ Source.QH H := fun hle => hU (hf.UH_elementary_of_V_le_QH hle).toIsMulCommutative
  apply q.wreath_singular_displacement
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change (((v : G)*((x : H) : G)*(v : G)⁻¹)*((x : H) : G)⁻¹)^2=1
  have hx : ((x : H) : G) ∈ Source.QH H := mem_map_of_mem H.subtype x.property
  have hc : ⁅((x : H) : G),(v : G)⁆ ∈ V₃ :=
    hf.core_module_commutator_le_seed d.third_index hnV (commutator_mem_commutator hx hv)
  rw [show ((v : G)*((x : H) : G)*(v : G)⁻¹)*((x : H) : G)⁻¹ = ⁅(v : G),((x : H) : G)⁆ from rfl,
    ←commutatorElement_inv]
  exact elemPow_eq_one_of_isElementaryAbelian _ (d.third_le (V₃.inv_mem hc))

/-- The selected module involution exchanges the actual SL2(3) factors,
while their common center is still the source line V1. -/
theorem normal_point_swapped_residual :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧ v ∉ pResidual 2 H ∧
      ∃ q : QuaternionCentralProductData (pCore 2 H),
        (center (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype) = V₁ ∧
        ∃ c : QuaternionResidualCentralProduct (pCore 2 H) q,
          c.left.map (MulAut.conj v).toMonoidHom = c.right ∧
          c.right.map (MulAut.conj v).toMonoidHom = c.left ∧
          pResidual 2 H ⊔ zpowers v = pResidual 2 H ⊔ V.subgroupOf H := by
  obtain ⟨v,hv,hv2,hvr,hj,_,_⟩ := normal_point_split_subgroup d hA312 hH hU hn
  obtain ⟨q,hz,⟨c⟩⟩ := normal_point_residual_factors d hA312 hH hU hn
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←d.characteristic_H H (le_sup_right.trans hH.1.2) hH.2.1]
    exact centralizer_generalizedFitting_le H
  have hvq : v ∉ pCore 2 H := fun hvq => hvr
    ((normal_point_residual_geometry d hA312 hH hU hn).2.1 hvq)
  have hswap := c.swap_factors_of_singular_actor v
    (normal_module_singular_actor d hA312 hH hU q v hv) hself hvq
  exact ⟨v,hv,hv2,hvr,q,hz,c,hswap.1,hswap.2,hj⟩

/-- The original module is recovered from the chosen involution and the
intrinsic point core, so this marking survives a core-preserving recognition. -/
theorem normal_point_module_from_involution (v : H) (hv : (v : G) ∈ V)
    (hv2 : v^2=1) (hvr : v ∉ pResidual 2 H) :
    V.subgroupOf H = (pCore 2 H ⊓ centralizer ({v} : Set H)) ⊔ zpowers v := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨q,_,⟨c⟩⟩ := normal_point_residual_factors d hA312 hH hU hn
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←d.characteristic_H H (le_sup_right.trans hH.1.2) hH.2.1]
    exact centralizer_generalizedFitting_le H
  have hvq : v ∉ pCore 2 H := fun hvq => hvr
    ((normal_point_residual_geometry d hA312 hH hU hn).2.1 hvq)
  have hcard := q.fixed_core_card_of_singular_involution (pCore 2 H) v hv2
    (normal_module_singular_actor d hA312 hH hU q v hv) hself hvq
  have hseed : V₃.subgroupOf H ≤ pCore 2 H := by
    intro x hx
    have hc : (x : G) ∈ Source.QH H := hf.UH_le_QH (le_conjugateSpanBy _ _ hx)
    exact (show (Source.QH H).subgroupOf H = pCore 2 H from
      comap_map_eq_self_of_injective H.subtype_injective _) ▸ hc
  have hfixed : V₃.subgroupOf H = pCore 2 H ⊓ centralizer ({v} : Set H) := by
    apply eq_of_le_of_card_ge
    · refine le_inf hseed ?_
      intro x hx
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact congrArg (fun y : V => (y : G)) (mul_comm (⟨x,d.third_le hx⟩ : V) ⟨v,hv⟩)
    · rw [hcard,Nat.card_congr (subgroupOfEquivOfLe (d.third_le.trans hf.V_le_H)).toEquiv,
        d.third_card]
  have hV := sup_zpowers_eq_of_relIndex_prime d.third_le Nat.prime_two d.third_index hv
    (show (v : G) ∉ V₃ from fun hh => hvq (hseed hh))
  rw [←hfixed]
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,
    map_subgroupOf_eq_of_le (d.third_le.trans hf.V_le_H),
    map_subgroupOf_eq_of_le hf.V_le_H]
  exact hV.symm

/-- One source witness simultaneously splits the whole ordinary point group
and exchanges the two recognized residual factors. -/
theorem normal_ordinary_point_swapped_decomposition
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧
      (pResidual 2 H).IsComplement' (zpowers v) ∧
      ∃ q : QuaternionCentralProductData (pCore 2 H),
        (center (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype) = V₁ ∧
        ∃ c : QuaternionResidualCentralProduct (pCore 2 H) q,
          c.left.map (MulAut.conj v).toMonoidHom = c.right ∧
          c.right.map (MulAut.conj v).toMonoidHom = c.left ∧
          V.subgroupOf H = (pCore 2 H ⊓ centralizer ({v} : Set H)) ⊔ zpowers v := by
  obtain ⟨v,hv,hv2,hvr,q,hz,c,hl,hr,hj⟩ := normal_point_swapped_residual d hA312 hH hU hn
  have hc : Nat.card H=576 := by
    rcases normal_local_orders d hA312 hH hU hn with h | h
    · exact h.1
    · have hh := h.2.2
      rw [hordinary,normal_local_card d hA312 hH hU hn] at hh
      contradiction
  obtain ⟨_,_,_,_,_,_,hcJ⟩ := normal_point_split_subgroup d hA312 hH hU hn
  have htop : pResidual 2 H ⊔ zpowers v = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,hj,hcJ,hc]
  have ho : orderOf v=2 := orderOf_eq_prime hv2 (fun he => hvr (he ▸ (pResidual 2 H).one_mem))
  have hd := (pResidual 2 H).disjoint_zpowers_of_prime_order_not_mem v ho hvr
  have hcomp : (pResidual 2 H).IsComplement' (zpowers v) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [←Subgroup.normal_mul,htop]
    rfl
  exact ⟨v,hv,hv2,hcomp,q,hz,c,hl,hr,
    normal_point_module_from_involution d hA312 hH hU hn v hv hv2 hvr⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
