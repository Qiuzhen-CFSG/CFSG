module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.LocalNormalizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CoreIntersection
public import Theory.GroupTheory.CommutingFactorSwapNorm
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap
/-!
# Reflections lifted into the original cubic normalizer

For the original root pair, Tx=T∩N_G(X) has order eight and satisfies
T=Q Tx. It normalizes both original elementary-sixteen planes. A plane
involution outside Q interchanges the quaternion factors, so its core coset
has no nontrivial central norm. Frattini therefore supplies an involution
in the SAME core coset inside Tx. No reflection or dihedral model is assumed.

Source: Aschbacher, Sporadic Groups,45.3(5), printed p.243.
-/
@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

noncomputable def cubicSylow (X:Subgroup G) : Subgroup G := P.T⊓normalizer (X:Set G)

theorem T_eq_core_sup_cubicSylow (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) : P.T=core z⊔P.cubicSylow X := by
  apply le_antisymm
  · intro t ht
    have htH:=P.T_le_centralizer ht
    have hp : t∈(core z:Set G)*((centralizer z⊓normalizer (X:Set G):Subgroup G):Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (core z)
        (centralizer z⊓normalizer (X:Set G))
        (inf_le_left.trans CentralizerHypothesis.centralizer_normalizes_core)]
      exact h.centralizer_eq_core_sup_cubic_normalizer X hX hXH ▸ htH
    obtain ⟨q,hq,n,hn,rfl⟩:=hp
    have hnT:n∈P.T := by
      simpa only [inv_mul_cancel_left] using P.T.mul_mem
        (P.T.inv_mem (mem_sup_right hq)) ht
    exact (core z⊔P.cubicSylow X).mul_mem (mem_sup_left hq) (mem_sup_right ⟨hnT,hn.2⟩)
  · exact sup_le le_sup_right inf_le_left

theorem cubicSylow_inf_core (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) : core z⊓P.cubicSylow X=zpowers z := by
  change core z⊓(P.T⊓normalizer (X:Set G))=_
  rw [←inf_assoc,inf_eq_left.mpr (show core z≤P.T from le_sup_right),
    h.core_cubic_normalizer_intersection X hX hXH]

theorem cubicSylow_card (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) : Nat.card (P.cubicSylow X)=8 := by
  have hn:P.cubicSylow X≤normalizer (core z:Set G) :=
    inf_le_left.trans (P.T_le_centralizer.trans CentralizerHypothesis.centralizer_normalizes_core)
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes (core z) (P.cubicSylow X) hn
  rw [P.cubicSylow_inf_core h X hX hXH,←P.T_eq_core_sup_cubicSylow h X hX hXH,
    P.T_card h,h.toCentralizerHypothesis.core_card,Nat.card_zpowers,h.involution] at hc
  omega

theorem cubicSylow_normalizes_plane (h:IsType z) (X V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    P.cubicSylow X≤normalizer (V:Set G) :=
  inf_le_left.trans ((P.T_le_N h).trans (P.plane_normalized_by_N h V hV))

theorem square_eq_one_of_plane_core_coset (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (r:G) (hr:r∈V) (hrQ:r∉core z) (q:G) (hq:q∈core z)
    (hsq:(r*q)^2∈zpowers z) : (r*q)^2=1 := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  let := hV.2.1
  have hs:=quaternion_factors_swapped_of_fixed_elementary_eight d.leftCore d.rightCore
    (V⊓core z) hB hC hi hc (by rw [d.core_span h.involution]; exact h.toCentralizerHypothesis.core_card)
    (by rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]; exact h.toCentralizerHypothesis.line_le_core)
    (by rw [d.core_span h.involution]; exact inf_le_right)
    (P.plane_inf_core_card h V hV) (fun u hu=>elemPow_eq_one_of_isElementaryAbelian u hu.1) r
    (by rw [d.core_span h.involution]; exact CentralizerHypothesis.centralizer_normalizes_core (P.T_le_centralizer (hV.1 hr)))
    (by rwa [d.core_span h.involution])
    (fun u hu=>congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨r,hr⟩:V) ⟨u,hu.1⟩))
  exact square_eq_one_of_swap_coset d.leftCore d.rightCore hi hc r
    (elemPow_eq_one_of_isElementaryAbelian r hr) hs.1 q
    (by rwa [d.core_span h.involution]) (by rwa [d.core_intersection h.involution])

theorem cubic_reflection_in_plane_coset (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (r:G) (hr:r∈V) (hrQ:r∉core z) :
    ∃n∈P.cubicSylow X,n^2=1 ∧ n∉core z ∧ r⁻¹*n∈core z := by
  let N:=centralizer z⊓normalizer (X:Set G)
  have hNQ:N≤normalizer (core z:Set G) :=
    inf_le_left.trans CentralizerHypothesis.centralizer_normalizes_core
  have hp:r∈(N:Set G)*(core z:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right N (core z) hNQ,sup_comm,
      ←h.centralizer_eq_core_sup_cubic_normalizer X hX hXH]
    exact P.T_le_centralizer (hV.1 hr)
  obtain ⟨n,hn,q,hq,he⟩:=hp
  change n*q=r at he
  have hnform:n=r*q⁻¹ := by rw [←he]; group
  have hnT:n∈P.T := by
    rw [hnform]
    exact P.T.mul_mem (hV.1 hr) (P.T.inv_mem (mem_sup_right hq))
  let := hV.2.1
  have hr2:r^2=1 := elemPow_eq_one_of_isElementaryAbelian r hr
  have hrn:r∈normalizer (core z:Set G) :=
    CentralizerHypothesis.centralizer_normalizes_core (P.T_le_centralizer (hV.1 hr))
  have hnQ:n^2∈core z := by
    have heq:n^2=(r*q⁻¹*r⁻¹)*q⁻¹ := by
      rw [hnform]
      have hri:r⁻¹=r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hr2)
      simp only [pow_two,hri]
      group
    rw [heq]
    exact (core z).mul_mem ((mem_normalizer_iff.mp hrn _).mp ((core z).inv_mem hq)) ((core z).inv_mem hq)
  have hnZ:n^2∈zpowers z := (h.core_cubic_normalizer_intersection X hX hXH) ▸
    (show n^2∈core z⊓normalizer (X:Set G) from ⟨hnQ,pow_mem hn.2 2⟩)
  refine ⟨n,⟨hnT,hn.2⟩,?_,?_,?_⟩
  · rw [hnform] at hnZ ⊢
    exact P.square_eq_one_of_plane_core_coset h V hV r hr hrQ q⁻¹ ((core z).inv_mem hq) hnZ
  · intro hnQ
    exact hrQ (he ▸ (core z).mul_mem hnQ hq)
  · rw [hnform,inv_mul_cancel_left]
    exact (core z).inv_mem hq
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
