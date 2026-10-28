module
public import Theory.SpecificGroups.Rudvalis.Model.CubicElementary.Marked
public import Theory.GroupTheory.ElementaryFixedCardinality.RudvalisPattern
/-!
# Cubic centralizers exclude elementary sixteen-subgroups in Rudvalis

A commuting involution cannot belong to the first native class, whose
centralizer has order prime to three. In the other class, simultaneous
conjugation places the pair in the marked max6 involution centralizer.
Its three-part has order three, so prime-order Sylow coverage reduces the
pair to the marked cubic or its inverse. The resulting ten-two incidence
pattern contradicts Burnside's formula for an elementary sixteen-group.

Source: the native ATLAS Rudvalis action and involution fusion; the original
opposite-block cubic in Aschbacher--Smith 2.4.25, printed p.543.
-/
public section
open Subgroup
namespace Rudvalis.CubicElementary
open SylowOvergroups InvolutionCentralizers
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

private noncomputable def fixedConjEquiv {D X : Type*} [Group D] [MulAction D X]
    (x g : D) : {i : X // x • i = i} ≃
      {i : X // (MulAut.conj g x) • i = i} where
  toFun i := ⟨g • i.val, by simp only [MulAut.conj_apply,mul_smul,
    inv_smul_smul,i.property]⟩
  invFun i := ⟨g⁻¹ • i.val, by
    have hi := congrArg (fun y : X => g⁻¹ • y) i.property
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hi⟩
  left_inv i := Subtype.ext (inv_smul_smul _ _)
  right_inv i := Subtype.ext (smul_inv_smul _ _)

private noncomputable def fixedPairConjEquiv {D X : Type*} [Group D] [MulAction D X]
    (x u g : D) : {i : X // x • i = i ∧ u • i = i} ≃
      {i : X // (MulAut.conj g x) • i = i ∧ (MulAut.conj g u) • i = i} where
  toFun i := ⟨g • i.val, by constructor <;>
    simp only [MulAut.conj_apply,mul_smul,inv_smul_smul,i.property.1,i.property.2]⟩
  invFun i := ⟨g⁻¹ • i.val, by
    constructor
    · have hi := congrArg (fun y : X => g⁻¹ • y) i.property.1
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hi
    · have hi := congrArg (fun y : X => g⁻¹ • y) i.property.2
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hi⟩
  left_inv i := Subtype.ext (inv_smul_smul _ _)
  right_inv i := Subtype.ext (smul_inv_smul _ _)

private theorem cubic_sq_eq_inv : cubic^2 = cubic⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [←pow_succ] using cubic_cube

private theorem cubic_fixed_power {k : ℕ} (hk : orderOf (cubic^k) = 3)
    (i : Fin 4060) : cubic^k • i = i ↔ cubic • i = i := by
  have hp : cubic^k = cubic^(k%3) := by simpa only [cubic_order] using (pow_mod_orderOf cubic k).symm
  have hn : k%3≠0 := by
    intro he
    rw [hp,he,pow_zero,orderOf_one] at hk
    omega
  have hr : k%3=1 ∨ k%3=2 := by omega
  rcases hr with hr | hr
  · simp only [hp,hr,pow_one]
  · rw [hp,hr,cubic_sq_eq_inv,inv_smul_eq_iff]
    exact eq_comm

private theorem max6_cubic_pair_counts (x : max6) (hx : orderOf x=3) :
    Nat.card {i : Fin 4060 // (x:Model) • i=i}=10 ∧
      Nat.card {i : Fin 4060 // (x:Model) • i=i ∧ centralInvolution • i=i}=2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let c : max6 := ⟨cubic,cubic_mem⟩
  have hc : orderOf c=3 := (Subgroup.orderOf_coe c).symm.trans cubic_order
  have hnot : ¬3^2 ∣ Nat.card max6 := by rw [max6_card]; decide
  obtain ⟨k,g,hxg⟩ := exists_conjugate_pow_of_orderOf_eq_prime hnot hx hc
  have hxg' : (x:Model)=MulAut.conj (g:Model) (cubic^k) := congrArg Subtype.val hxg
  have hcp : orderOf (cubic^k)=3 := by
    have he : orderOf (MulAut.conj (g:Model) (cubic^k))=3 := by
      rw [←hxg']
      exact (Subgroup.orderOf_coe x).trans hx
    exact ((MulAut.conj (g:Model)).orderOf_eq (cubic^k)).symm.trans he
  have hgz : MulAut.conj (g:Model) centralInvolution=centralInvolution := by
    have hg : (g:Model)∈centralizer ({centralInvolution}:Set Model) :=
      (le_of_eq LowCentralizers.max6_eq_centralizer) g.property
    have hh := mem_centralizer_singleton_iff.mp hg
    change (g:Model)*centralInvolution*(g:Model)⁻¹=centralInvolution
    rw [hh,mul_assoc,mul_inv_cancel,mul_one]
  have he : {i : Fin 4060 // cubic^k • i=i} ≃ {i : Fin 4060 // cubic • i=i} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun i => cubic_fixed_power hcp i)
  have hep : {i : Fin 4060 // cubic^k • i=i ∧ centralInvolution • i=i} ≃
      {i : Fin 4060 // cubic • i=i ∧ centralInvolution • i=i} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun i => and_congr_left (fun _ => cubic_fixed_power hcp i))
  constructor
  · rw [hxg',←Nat.card_congr (fixedConjEquiv (X:=Fin 4060) (cubic^k) (g:Model)),
      Nat.card_congr he,cubic_fixed_card]
  · rw [hxg',←hgz,←Nat.card_congr (fixedPairConjEquiv (X:=Fin 4060) (cubic^k) centralInvolution (g:Model)),
      Nat.card_congr hep,pair_fixed_card]

/-- Every actual commuting cubic–involution pair has the marked incidence counts. -/
theorem commuting_pair_counts (x u : Model) (hx : orderOf x=3)
    (hu : orderOf u=2) (h : Commute x u) :
    Nat.card {i : Fin 4060 // x • i=i}=10 ∧
      Nat.card {i : Fin 4060 // x • i=i ∧ u • i=i}=2 := by
  rcases involution_isConj_a_or_b_sq u hu with hua | hub
  · let v : Centralizer u := ⟨x,mem_centralizer_singleton_iff.mpr h.eq⟩
    have hv : orderOf v=3 := (Subgroup.orderOf_coe v).symm.trans hx
    have hd : 3 ∣ Nat.card (Centralizer a) := by
      rw [←Nat.card_congr (centralizerEquivOfIsConj hua).toEquiv,←hv]
      exact _root_.orderOf_dvd_natCard v
    exact (second_centralizer_not_three hd).elim
  · have hz : IsConj centralInvolution (b^2) :=
      isConj_iff.mpr ⟨LowCentralizers.squareConjugator,LowCentralizers.squareConjugator_alignment⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp (hub.trans hz.symm)
    let x' : Model := MulAut.conj g x
    have hxu : Commute x' centralInvolution := by
      rw [←hg]
      exact h.map (MulAut.conj g).toMonoidHom
    have hxm : x'∈max6 := by
      rw [LowCentralizers.max6_eq_centralizer]
      exact mem_centralizer_singleton_iff.mpr hxu.eq
    have hx' : orderOf (⟨x',hxm⟩:max6)=3 := by
      exact (Subgroup.orderOf_coe (⟨x',hxm⟩:max6)).symm.trans
        (((MulAut.conj g).orderOf_eq x).trans hx)
    obtain ⟨hcf,hcpf⟩ := max6_cubic_pair_counts ⟨x',hxm⟩ hx'
    constructor
    · exact (Nat.card_congr (fixedConjEquiv (X:=Fin 4060) x g)).trans hcf
    · change Nat.card {i : Fin 4060 // MulAut.conj g x • i=i ∧
        centralInvolution • i=i}=2 at hcpf
      have hg' : MulAut.conj g u=centralInvolution := hg
      have hc : Nat.card {i : Fin 4060 // MulAut.conj g x • i=i ∧
          MulAut.conj g u • i=i}=2 := by rwa [hg']
      exact (Nat.card_congr (fixedPairConjEquiv (X:=Fin 4060) x u g)).trans hc

/-- A cubic cannot centralize an elementary subgroup of order sixteen in the native carrier. -/
theorem not_centralizes_elementary_sixteen (U : Subgroup Model)
    [IsElementaryAbelian 2 U] (hU : Nat.card U=16) (x : Model)
    (hx : orderOf x=3) (hC : U≤centralizer ({x}:Set Model)) : False := by
  have hnon : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial U := hnon
  obtain ⟨u,hu⟩ := exists_ne (1:U)
  have hu2 : orderOf (u:Model)=2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u.val u.property)
      (fun he => hu (Subtype.ext he))
  have hc : Commute x (u:Model) :=
    (mem_centralizer_singleton_iff.mp (hC u.property)).symm
  exact Theory.GroupTheory.elementary_sixteen_ten_two_fixed_pattern_false U hU x hx hC
    (commuting_pair_counts x u hx hu2 hc).1
    (fun v hv hcv => (commuting_pair_counts x v hx hv hcv).2)
end Rudvalis.CubicElementary
