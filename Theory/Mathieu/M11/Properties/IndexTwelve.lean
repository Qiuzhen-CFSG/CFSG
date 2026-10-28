module

public import Theory.Mathieu.M11.Properties.PrimeNormalizers
public import Theory.Mathieu.M11.Properties.IndexTwelve.Certificate
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The index-twelve overgroup of the M11 eleven-normalizer

For the native Mathieu group, put `c = AB` and take the involution `s` given
by the word in `M11IndexTwelveCertificate.involutionWord`. We construct
`H = ⟨c, s⟩`. A checked word places the native order-five normalizer complement
in H. The conjugate of c by s does not commute with c, so the Sylow-eleven
normalizer is proper in H. Sylow's congruence gives its index at least twelve,
hence |H| ≥ 660. The eleven-block collection preserved by H has twelve
explicit M11-translates, giving |M11:H| ≥ 12 and hence |H| ≤ 660.
Finally a checked word expresses s in c and its H-conjugate, proving that
P normally generates H, without any simplicity or PSL₂(11) recognition.

This supplies the subgroup input for the M11 binary induced-module argument
of James, J. Algebra 27 (1973), 57–111, used in Aschbacher–Smith, Quasithin,
K.4 (printed p.457/PDF p.468). The exported witness retains the actual
normalizer, relative subgroup, and normal closure conventions.
-/

open scoped Pointwise
namespace Sporadic.Mathieu

/-- The concrete order-660 overgroup of the chosen eleven-normalizer. -/
@[expose] public noncomputable def m11IndexTwelveSubgroup : Subgroup M11 :=
  Subgroup.closure {m11Sylow11Generator,
    M11IndexTwelveCertificate.involutionWord m11GeneratorAInM11 m11GeneratorBInM11}

namespace M11IndexTwelve
open M11IndexTwelveCertificate

private noncomputable abbrev s : M11 :=
  involutionWord m11GeneratorAInM11 m11GeneratorBInM11
private noncomputable abbrev c := m11Sylow11Generator
private noncomputable abbrev H := m11IndexTwelveSubgroup

private theorem c_mem : c ∈ H := Subgroup.subset_closure (by simp)
private theorem s_mem : s ∈ H := Subgroup.subset_closure (by simp)
private theorem P_eq_zpowers : m11Sylow11Subgroup = Subgroup.zpowers c := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr m11Sylow11Generator_mem_subgroup)
  rw [m11Sylow11Subgroup_card, Nat.card_zpowers, m11Sylow11Generator_order]

private theorem P_le : m11Sylow11Subgroup ≤ H := by
  rw [P_eq_zpowers]
  exact Subgroup.zpowers_le.mpr c_mem

private theorem s_perm : (s : Equiv.Perm (Fin 11)) = sPerm :=
  involutionWord_eq

private theorem s_word : s = c ^ 2 * (s⁻¹ * c * s) * (c ^ 2)⁻¹ * ((s⁻¹ * c * s) ^ 2)⁻¹ * c := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, s_perm]
  exact normal_generation_word

private theorem d_word : m11Sylow11Complement =
    c * s * c⁻¹ * s * c * s⁻¹ * (c ^ 2)⁻¹ * s⁻¹ * c⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, s_perm]
  exact complement_word

private theorem d_mem : m11Sylow11Complement ∈ H := by
  rw [d_word]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.mul_mem (H.mul_mem (H.mul_mem c_mem s_mem) (H.inv_mem c_mem)) s_mem)
      c_mem) (H.inv_mem s_mem)) (H.inv_mem (H.pow_mem c_mem 2)))
      (H.inv_mem s_mem)) (H.inv_mem c_mem)

private theorem N_le : m11Sylow11Normalizer ≤ H := by
  let K := m11Sylow11Normalizer ⊓ H
  have hc : c ∈ K :=
    ⟨Subgroup.le_normalizer m11Sylow11Generator_mem_subgroup, c_mem⟩
  have hd : m11Sylow11Complement ∈ K :=
    ⟨m11Sylow11Complement_normalizes (Subgroup.mem_zpowers _), d_mem⟩
  have h11 : 11 ∣ Nat.card K := by
    have ho : orderOf (⟨c, hc⟩ : K) = 11 := by
      rw [← Subgroup.orderOf_coe]
      exact m11Sylow11Generator_order
    simpa only [ho] using orderOf_dvd_natCard (⟨c, hc⟩ : K)
  have h5 : 5 ∣ Nat.card K := by
    have ho : orderOf (⟨m11Sylow11Complement, hd⟩ : K) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact m11Sylow11Complement_order
    simpa only [ho] using orderOf_dvd_natCard (⟨m11Sylow11Complement, hd⟩ : K)
  have h55 : 55 ∣ Nat.card K :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 11 5) h11 h5
  have heq : K = m11Sylow11Normalizer := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [m11Sylow11_normalizer_card]
    exact Nat.le_of_dvd Nat.card_pos h55
  rw [← heq]
  exact inf_le_right

set_option maxRecDepth 4096 in
private theorem s_not_N : s ∉ m11Sylow11Normalizer := by
  intro hs
  have hsc : s * c * s⁻¹ ∈ m11Sylow11Subgroup :=
    (Subgroup.mem_normalizer_iff.mp hs c).mp m11Sylow11Generator_mem_subgroup
  rw [P_eq_zpowers] at hsc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsc
  have hc := (Commute.refl c).zpow_left k
  rw [hk] at hc
  have hp := congrArg (fun z : M11 => (z : Equiv.Perm (Fin 11)) 0) hc.eq
  change ((s : Equiv.Perm (Fin 11)) * (m11GeneratorA * m11GeneratorB) *
    (s : Equiv.Perm (Fin 11))⁻¹ * (m11GeneratorA * m11GeneratorB)) 0 =
    ((m11GeneratorA * m11GeneratorB) * ((s : Equiv.Perm (Fin 11)) *
      (m11GeneratorA * m11GeneratorB) * (s : Equiv.Perm (Fin 11))⁻¹)) 0 at hp
  rw [s_perm] at hp
  have hfalse : (5 : Fin 11) = 7 := hp
  contradiction

private noncomputable def rep : Fin 12 → M11 :=
  reps m11GeneratorAInM11 m11GeneratorBInM11

private theorem rep_perm (i : Fin 12) :
    (rep i : Equiv.Perm (Fin 11)) = reps m11GeneratorA m11GeneratorB i := by
  fin_cases i <;> rfl

private theorem rep_injective :
    Function.Injective (fun i => (rep i : Equiv.Perm (Fin 11)) • blocks) := by
  simpa only [rep_perm] using reps_blocks_injective

private theorem normal_generation :
    Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) = ⊤ := by
  let Q := Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H)
  let ch : H := ⟨c, c_mem⟩
  let sh : H := ⟨s, s_mem⟩
  have hc : ch ∈ Q := Subgroup.le_normalClosure m11Sylow11Generator_mem_subgroup
  have hconj : sh⁻¹ * ch * sh ∈ Q := by
    simpa only [inv_inv] using (inferInstance : Q.Normal).conj_mem ch hc sh⁻¹
  have hword : sh = ch ^ 2 * (sh⁻¹ * ch * sh) * (ch ^ 2)⁻¹ *
      ((sh⁻¹ * ch * sh) ^ 2)⁻¹ * ch := Subtype.ext s_word
  have hs : sh ∈ Q := by
    rw [hword]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.pow_mem hc 2) hconj)
      (Q.inv_mem (Q.pow_mem hc 2))) (Q.inv_mem (Q.pow_mem hconj 2))) hc
  have hcover : H ≤ Q.map H.subtype := by
    apply (Subgroup.closure_le _).2
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨ch, hc, rfl⟩
    · have hx' : x = s := hx
      subst x
      exact ⟨sh, hs, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, heq⟩ := hcover x.property
  have hyx : y = x := Subtype.ext heq
  exact hyx ▸ hy

private theorem relative_index_ge : 12 ≤ (m11Sylow11Normalizer.subgroupOf H).index := by
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  let S : Sylow 11 H := m11Sylow11.subtype P_le
  have hS : Subgroup.normalizer (S : Set H) = m11Sylow11Normalizer.subgroupOf H :=
    (Subgroup.subgroupOf_normalizer_eq P_le).symm
  have hmod : (m11Sylow11Normalizer.subgroupOf H).index % 11 = 1 := by
    have h := card_sylow_modEq_one 11 H
    rw [S.card_eq_index_normalizer, hS] at h
    exact h
  have hne : (m11Sylow11Normalizer.subgroupOf H).index ≠ 1 := by
    intro hi
    have ht := Subgroup.index_eq_one.mp hi
    have hs : (⟨s, s_mem⟩ : H) ∈ m11Sylow11Normalizer.subgroupOf H := by
      rw [ht]
      trivial
    exact s_not_N hs
  omega

private theorem card_ge : 660 ≤ Nat.card H := by
  have hc : Nat.card (m11Sylow11Normalizer.subgroupOf H) = 55 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le).toEquiv]
    exact m11Sylow11_normalizer_card
  have hmul := (m11Sylow11Normalizer.subgroupOf H).card_mul_index
  rw [hc] at hmul
  have hi := relative_index_ge
  omega

private theorem H_le_stabilizer : H ≤ MulAction.stabilizer M11 blocks := by
  apply (Subgroup.closure_le _).2
  intro x hx
  rcases hx with rfl | hx
  · change (m11GeneratorA * m11GeneratorB) • blocks = blocks
    exact c_blocks
  · have hx' : x = s := hx
    subst x
    change (s : Equiv.Perm (Fin 11)) • blocks = blocks
    rw [s_perm]
    exact s_blocks

private theorem index_ge : 12 ≤ H.index := by
  let f : Fin 12 → MulAction.orbit M11 blocks :=
    fun i => ⟨rep i • blocks, MulAction.mem_orbit_iff.mpr ⟨rep i, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact rep_injective (congrArg Subtype.val hij)
  have horbit : 12 ≤ Nat.card (MulAction.orbit M11 blocks) := by
    simpa using Nat.card_le_card_of_injective f hf
  have hindex : 12 ≤ (MulAction.stabilizer M11 blocks).index := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact horbit
  exact hindex.trans (Subgroup.index_antitone H_le_stabilizer)

private theorem card : Nat.card H = 660 := by
  have hlo := card_ge
  have hi := index_ge
  have hmul := H.card_mul_index
  rw [m11_order] at hmul
  nlinarith

private theorem index : H.index = 12 := by
  have hmul := H.card_mul_index
  rw [card, m11_order] at hmul
  omega

private theorem relative_index : (m11Sylow11Normalizer.subgroupOf H).index = 12 := by
  have hc : Nat.card (m11Sylow11Normalizer.subgroupOf H) = 55 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le).toEquiv]
    exact m11Sylow11_normalizer_card
  have hmul := (m11Sylow11Normalizer.subgroupOf H).card_mul_index
  rw [hc, card] at hmul
  omega

end M11IndexTwelve

/-- The chosen eleven-normalizer lies in the concrete index-twelve subgroup. -/
public theorem m11Sylow11Normalizer_le_indexTwelveSubgroup :
    m11Sylow11Normalizer ≤ m11IndexTwelveSubgroup := M11IndexTwelve.N_le

public theorem m11IndexTwelveSubgroup_card : Nat.card m11IndexTwelveSubgroup = 660 :=
  M11IndexTwelve.card

public theorem m11IndexTwelveSubgroup_index : m11IndexTwelveSubgroup.index = 12 :=
  M11IndexTwelve.index

/-- This is the relative index inside H, with the literal restricted normalizer. -/
public theorem m11Sylow11Normalizer_index_in_indexTwelveSubgroup :
    (m11Sylow11Normalizer.subgroupOf m11IndexTwelveSubgroup).index = 12 :=
  M11IndexTwelve.relative_index

/-- The selected eleven-subgroup normally generates the concrete overgroup. -/
public theorem m11Sylow11Subgroup_normalClosure_indexTwelveSubgroup :
    Subgroup.normalClosure
      (↑(m11Sylow11Subgroup.subgroupOf m11IndexTwelveSubgroup) : Set m11IndexTwelveSubgroup) = ⊤ :=
  M11IndexTwelve.normal_generation

/-- The exact subgroup witness consumed by the degree-twelve induced-module argument. -/
public theorem exists_m11Sylow11Normalizer_indexTwelve_overgroup :
    ∃ H : Subgroup M11, m11Sylow11Normalizer ≤ H ∧ H.index = 12 ∧
      (m11Sylow11Normalizer.subgroupOf H).index = 12 ∧
      Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) = ⊤ :=
  ⟨m11IndexTwelveSubgroup, m11Sylow11Normalizer_le_indexTwelveSubgroup,
    m11IndexTwelveSubgroup_index, m11Sylow11Normalizer_index_in_indexTwelveSubgroup,
    m11Sylow11Subgroup_normalClosure_indexTwelveSubgroup⟩

end Sporadic.Mathieu
