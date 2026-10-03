module

public import Stellmacher.Recognition.Parrott.SecondElementary

/-!
# The actual normalizer of Parrott's second elementary subgroup

For each witness `d` constructed by `SecondElementary`, put N=N_G(d.F)
and T=d.sylow. The intersection N∩C_G(z) is exactly T. Indeed the
normalizer inside C_G(z) is the stabilizer of the selected nonzero core
coset, whose orbit has length five. Consequently |N|=2048n for an odd
integer n between 1 and 31: n is the length of the N-orbit of z in F.
Conjugation on F has kernel F and image of order 64n. Under the N₂
hypothesis N is solvable. We also have F≤O₂(N)≤T and z∈Z(O₂(N))≤F,
using the actual inclusion maps. These statements retain the supplied F and T.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
§2, pp.675–677, the counting setup for Lemmas 5 and 6. Proper containment
and the determination n=3 require the subsequent fusion argument.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] {z : G}

/-- The supplied ambient Sylow lies in the original involution centralizer. -/
public theorem sylow_le_centralizer (d : ParrottSecondElementaryData z) :
    (d.sylow : Subgroup G) ≤ centralizer ({z} : Set G) := by
  rw [d.sylow_map]
  exact map_subtype_le _

/-- The supplied Sylow has the full two-part of the original centralizer order. -/
public theorem sylow_card [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) : Nat.card d.sylow = 2048 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card d.localSylow = 2048 := by
    rw [d.localSylow.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  change Nat.card (d.sylow : Subgroup G) = 2048
  rw [d.sylow_map, card_map_of_injective (centralizer ({z} : Set G)).subtype_injective]
  exact hc

private theorem fixed_join_map (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let DH := (commutator (pCore 2 H)).map (pCore 2 H).subtype
    (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hDH : DH.map H.subtype = E := map_map _ _ _
  have hfixed : (DH ⊓ centralizer ({d.a} : Set H)).map H.subtype =
      E ⊓ centralizer ({(d.a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDH ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDH.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  change (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfixed]
  exact d.fixed_join.symm

/-- Inside the original centralizer the normalizer of F is precisely the
chosen local Sylow subgroup. -/
public theorem normalizer_subgroupOf_centralizer [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    (normalizer (d.F : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (d.localSylow : Subgroup (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let FH := zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))
  let N := normalizer (d.F : Set G)
  have hFHmap : FH.map H.subtype = d.F := d.fixed_join_map
  have hFH : d.F.subgroupOf H = FH := by
    rw [← hFHmap]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hnorm : N.subgroupOf H = normalizer (FH : Set H) := by
    rw [subgroupOf_normalizer_eq (d.le_sylow.trans d.sylow_le_centralizer), hFH]
  obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  have hindex : (N.subgroupOf H).index = 5 := by
    rw [hnorm, elementary_involution_fixed_join_normalizer DH d.a d.a_order
      d.a_not_mem_derived, index_comap_of_surjective _ (QuotientGroup.mk'_surjective DH)]
    exact d.coset_index
  have hcard : Nat.card (N.subgroupOf H) = 2048 := by
    have hc := (N.subgroupOf H).index_mul_card
    rw [hindex, (h.card_and_solvable z).1] at hc
    omega
  have hle : (d.localSylow : Subgroup H) ≤ N.subgroupOf H := by
    intro x hx
    apply d.sylow_le_normalizer
    rw [d.sylow_map]
    exact mem_map_of_mem H.subtype hx
  apply (eq_of_le_of_card_ge hle _).symm
  have hc : Nat.card d.localSylow = Nat.card d.sylow := by
    rw [d.sylow_map, card_map_of_injective H.subtype_injective]
  rw [hcard, hc, d.sylow_card h]

/-- The supplied Sylow fixes the selected core involution modulo the derived core. -/
public theorem sylow_commutator_a_mem_derived [Finite G]
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : centralizer ({z} : Set G)) (hy : (y : G) ∈ (d.sylow : Subgroup G)) :
    ⁅d.a, y⁆ ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      (pCore 2 (centralizer ({z} : Set G))).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let FH := zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))
  have hFHmap : FH.map H.subtype = d.F := d.fixed_join_map
  have hFH : d.F.subgroupOf H = FH := by
    rw [← hFHmap]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hyN : y ∈ normalizer (FH : Set H) := by
    rw [← hFH, ← subgroupOf_normalizer_eq (d.le_sylow.trans d.sylow_le_centralizer)]
    exact d.sylow_le_normalizer hy
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  rw [elementary_involution_fixed_join_normalizer DH d.a d.a_order d.a_not_mem_derived] at hyN
  apply (QuotientGroup.eq_one_iff (N := DH) _).mp
  change QuotientGroup.mk' DH ⁅d.a, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp hyN).symm

/-- The stabilizer of z in the actual normalizer is the supplied Sylow T. -/
public theorem normalizer_inf_centralizer [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    normalizer (d.F : Set G) ⊓ centralizer ({z} : Set G) = (d.sylow : Subgroup G) := by
  rw [← subgroupOf_map_subtype, d.normalizer_subgroupOf_centralizer h, d.sylow_map]

/-- N₂ supplies solvability of the actual normalizer, since F is nontrivial. -/
public theorem normalizer_solvable [Finite G] (d : ParrottSecondElementaryData z)
    (hN : IsNTwoGroup G) : Group.IsSolvable (normalizer (d.F : Set G)) := by
  have hne : d.F ≠ ⊥ := by
    intro heq
    have hc := d.card
    rw [heq, card_bot] at hc
    omega
  let : IsElementaryAbelian 2 d.F := d.elementary
  exact hN _ ⟨d.F, hne, IsElementaryAbelian.isPGroup 2 d.F, rfl⟩

/-- The canonical action on F has exactly F as its kernel. -/
public theorem normalizer_action_ker (d : ParrottSecondElementaryData z) :
    d.F.normalizerMonoidHom.ker = d.F.subgroupOf (normalizer (d.F : Set G)) := by
  rw [normalizerMonoidHom_ker, d.centralizer_eq]

/-- The quotient N/F is identified with the actual conjugation image in Aut(F). -/
public theorem normalizer_quotient_equiv_action_range (d : ParrottSecondElementaryData z) :
    Nonempty ((normalizer (d.F : Set G) ⧸
      d.F.subgroupOf (normalizer (d.F : Set G))) ≃* d.F.normalizerMonoidHom.range) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq d.normalizer_action_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange d.F.normalizerMonoidHom)⟩

/-- F is contained in the actual two-core of its normalizer. -/
public theorem le_normalizer_core (d : ParrottSecondElementaryData z) :
    d.F ≤ (pCore 2 (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype := by
  let N := normalizer (d.F : Set G)
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hF : IsPGroup 2 (d.F.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 d.F).comap_subtype
  have hle : d.F.subgroupOf N ≤ pCore 2 N := le_sSup ⟨inferInstance, hF⟩
  have hm := map_mono hle (f := N.subtype)
  rw [map_subgroupOf_eq_of_le le_normalizer] at hm
  exact hm

/-- The ambient image of the normalizer's two-core lies in the supplied T. -/
public theorem normalizer_core_le_sylow (d : ParrottSecondElementaryData z) :
    (pCore 2 (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype ≤ (d.sylow : Subgroup G) := by
  let N := normalizer (d.F : Set G)
  have hle := pCore_isPGroup.le_sylow_of_normal (d.sylow.subtype d.sylow_le_normalizer)
  change pCore 2 N ≤ (d.sylow : Subgroup G).subgroupOf N at hle
  have hm := map_mono hle (f := N.subtype)
  rw [map_subgroupOf_eq_of_le d.sylow_le_normalizer] at hm
  exact hm

/-- Self-centralization of F puts the actual center of the normalizer
core inside F. -/
public theorem normalizer_core_center_le (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    (center K).map (N.subtype.comp K.subtype) ≤ d.F := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  change (center K).map (N.subtype.comp K.subtype) ≤ d.F
  rw [← d.centralizer_eq]
  rintro x ⟨k, hk, rfl⟩
  intro f hf
  obtain ⟨fN, hfK, rfl⟩ := d.le_normalizer_core hf
  exact congrArg (N.subtype.comp K.subtype)
    (mem_center_iff.mp hk ⟨fN, hfK⟩)

/-- The original involution is central in the actual normalizer two-core. -/
public theorem z_mem_normalizer_core_center (d : ParrottSecondElementaryData z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    z ∈ (center K).map (N.subtype.comp K.subtype) := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  obtain ⟨zN, hzK, hzN⟩ := d.le_normalizer_core d.z_mem_inf.2
  refine ⟨⟨zN, hzK⟩, ?_, hzN⟩
  apply mem_center_iff.mpr
  intro k
  apply Subtype.ext
  apply Subtype.ext
  change ((k : N) : G) * (zN : G) = (zN : G) * ((k : N) : G)
  change (zN : G) = z at hzN
  rw [hzN]
  exact mem_centralizer_singleton_iff.mp
    (d.sylow_le_centralizer (d.normalizer_core_le_sylow
      (mem_map_of_mem N.subtype k.property)))

/-- The odd part of |N| is the orbit length of z, hence lies between 1 and 31.
The image in Aut(F) has order 64 times that same integer. -/
public theorem normalizer_card [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ n : ℕ, Odd n ∧ 1 ≤ n ∧ n ≤ 31 ∧
      Nat.card (normalizer (d.F : Set G)) = 2048 * n ∧
      Nat.card d.F.normalizerMonoidHom.range = 64 * n := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normalizer (d.F : Set G)
  let T : Subgroup G := d.sylow
  let : MulDistribMulAction N d.F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer N d.F le_rfl
  let zF : d.F := ⟨z, d.z_mem_inf.2⟩
  let X := MulAction.orbit N zF
  have hz : z ≠ 1 := by
    intro hz
    have hc := h.involution
    simp [hz] at hc
  have hzF : zF ≠ 1 := fun heq => hz (congrArg Subtype.val heq)
  have hsub : MulAction.orbit N zF ⊆ ({1} : Set d.F)ᶜ := by
    intro x hx
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    change a • zF ≠ 1
    intro heq
    apply hzF
    simpa using congrArg (fun y : d.F => a⁻¹ • y) heq
  have hbound : Nat.card X ≤ 31 := by
    have hc : (({1} : Set d.F)ᶜ).ncard = 31 := by
      rw [Set.ncard_compl, d.card, Set.ncard_singleton]
    exact (Set.ncard_le_ncard hsub).trans_eq hc
  have hstab : MulAction.stabilizer N zF = T.subgroupOf N := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    change a • zF = zF ↔ (a : G) ∈ T
    rw [Subtype.ext_iff]
    change (a : G) * z * (a : G)⁻¹ = z ↔ (a : G) ∈ T
    rw [mul_inv_eq_iff_eq_mul, ← mem_centralizer_singleton_iff]
    have heq := d.normalizer_inf_centralizer h
    change N ⊓ centralizer ({z} : Set G) = T at heq
    rw [← heq]
    exact (and_iff_right a.property).symm
  have hindex : T.relIndex N = Nat.card X := by
    rw [relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hcard : Nat.card N = 2048 * T.relIndex N := by
    have hc := (T.subgroupOf N).index_mul_card
    have hTcard : Nat.card (T.subgroupOf N) = 2048 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe d.sylow_le_normalizer).toEquiv]
      exact d.sylow_card h
    rw [hTcard] at hc
    exact hc.symm.trans (Nat.mul_comm _ _)
  have hodd : Odd (T.relIndex N) := by
    apply Nat.odd_iff.mpr
    have hnot : ¬ 2 ∣ T.relIndex N := fun hd =>
      d.sylow.not_dvd_index (hd.trans (relIndex_dvd_index_of_le d.sylow_le_normalizer))
    have hmod : T.relIndex N % 2 ≠ 0 := fun heq => hnot (Nat.dvd_of_mod_eq_zero heq)
    omega
  have hpos : 1 ≤ T.relIndex N := by
    have hc := Nat.card_pos (α := N)
    rw [hcard] at hc
    omega
  have hker : Nat.card d.F.normalizerMonoidHom.ker = 32 := by
    rw [d.normalizer_action_ker,
      Nat.card_congr (subgroupOfEquivOfLe (H := d.F) le_normalizer).toEquiv, d.card]
  have himage : Nat.card d.F.normalizerMonoidHom.range = 64 * T.relIndex N := by
    have hc := d.F.normalizerMonoidHom.ker.card_mul_index
    rw [index_ker, hker, hcard] at hc
    omega
  exact ⟨T.relIndex N, hodd, hpos, hindex ▸ hbound, hcard, himage⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
