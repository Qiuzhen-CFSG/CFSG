module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.CommonPrime

/-!
# The centralizer supplement and its odd index

The common prime supplies a nontrivial Sylow subgroup of J. The index
bound promotes it to a Sylow subgroup of C_G(A), and the normalizer control
and Frattini argument give M = C_G(A)D. Since J contains a Sylow two-subgroup
of D, the quotient of M by C_G(A) has odd order.

Consequently the chosen two-subgroup S centralizes A. This follows directly
from relative normality and odd index; no identification of an odd core,
two-residual or odd-residual is used. The elementary normality of T in S
is recorded with its actual subgroup inclusion for the later quotient.

Source: GLS4, Chapter 2, Lemma 14.5 and the paragraph preceding Lemma 14.6,
`refs/KGroup/GLS4/Chapter2.tex`, approximately lines 2525–2545.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.distinguished_centralizer_relIndex_dvd (g : LocalGeometry Z M z t m) :
    (centralizer (residualGenerated M z t : Set G)).relIndex
      (centralizer (closure (Z ∩ (M : Set G)) : Set G)) ∣
        (2 ^ (2 * m + 1)) ^ 3 *
          ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) := by
  let C := centralizer (closure (Z ∩ (M : Set G)) : Set G)
  let J := centralizer (residualGenerated M z t : Set G)
  have hJC : J ≤ C := centralizer_le d.distinguished_le_residual
  have hc : Nat.card J * J.relIndex C = Nat.card C := by
    have he := (J.subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv] at he
    exact he
  apply (Nat.mul_dvd_mul_iff_left (Nat.card_pos (α := J))).mp
  rw [hc, Nat.mul_comm]
  exact d.distinguished_centralizer_card_dvd g

omit d in
public theorem LocalGeometry.borelTwoCore_le_distinguished_centralizer
    (g : LocalGeometry Z M z t m) :
    borelTwoCore M z t ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  apply le_centralizer_iff.mpr
  rw [← g.P_center]
  rintro _ ⟨a, ha, rfl⟩ x hx
  exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)

public theorem Context.point_inter_residual_normalizer :
    ((M ⊓ normalizer (residualGenerated M z t : Set G) : Subgroup G) : Set G) =
      (borelTwoCore M z t : Set G) * (residualPairStabilizer M t : Set G) := by
  apply residual_inter_normalizer_eq_twoCore_mul_pair
    (d.minimal.disconnected.involutions t d.t_mem) d.t_not_mem_M
    d.pair_le_residual_normalizer
  · exact residualGenerated_suzuki_borel_product d.minimal.disconnected d.reduction
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
      (by have := d.parameter_pos; omega) d.model
  · intro v hvL hvM hv
    obtain ⟨b, hb, he⟩ := residualGenerated_suzuki_outside_involutions_conjugate
      d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
      (by have := d.parameter_pos; omega) d.model hvL hv hvM
    exact ⟨b, hb, he.symm⟩

public theorem Context.pointStabilizer_eq_centralizer_sup_pair
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    M = centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊔ residualPairStabilizer M t := by
  let C := centralizer (closure (Z ∩ (M : Set G)) : Set G)
  let J := centralizer (residualGenerated M z t : Set G)
  let D := residualPairStabilizer M t
  let q := 2 ^ (2 * m + 1)
  change M = C ⊔ D
  obtain ⟨s, hs, hsJ, hsK⟩ := d.common_prime g hsemi
  let : Fact s.Prime := ⟨hs⟩
  have hcop : Nat.Coprime (q - 1) (q ^ 3 * (q ^ 2 - q + 1)) := by
    have hqc : Nat.Coprime (q - 1) q :=
      (Nat.coprime_self_sub_left Nat.one_le_two_pow).mpr (Nat.coprime_one_left _)
    have he : q ^ 2 - q + 1 = 1 + (q - 1) * q := by
      simp only [Nat.sub_mul, one_mul, pow_two]
      omega
    exact (hqc.pow_right 3).mul_right (by
      rw [he]
      exact (Nat.coprime_add_mul_left_right (q - 1) 1 q).mpr (Nat.coprime_one_right _))
  have hJC : J ≤ C := centralizer_le d.distinguished_le_residual
  have hsidx : ¬ s ∣ J.relIndex C := by
    intro hh
    exact hs.not_dvd_one (hcop.gcd_eq_one ▸
      Nat.dvd_gcd hsK (hh.trans (d.distinguished_centralizer_relIndex_dvd g)))
  let Q : Sylow s J := default
  let i : J →* C := inclusion hJC
  have hidx : ¬ s ∣ ((Q : Subgroup J).map i).index := by
    rw [(Q : Subgroup J).index_map_of_injective (inclusion_injective hJC), inclusion_range]
    exact hs.not_dvd_mul Q.not_dvd_index hsidx
  let R : Sylow s C := (Q.isPGroup'.map i).toSylow hidx
  let C' := C.subgroupOf M
  let : C'.Normal := d.distinguished_centralizer_normal
  let e : C ≃* C' := (subgroupOfEquivOfLe d.distinguished_centralizer_le).symm
  let R' : Sylow s C' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let QG := (Q : Subgroup J).map J.subtype
  have hmap : ((R' : Subgroup C').map C'.subtype).map M.subtype = QG := by
    change ((((Q : Subgroup J).map i).map e.toMonoidHom).map C'.subtype).map M.subtype = _
    rw [map_map, map_map, map_map]
    rfl
  have hQJ : QG ≤ J := map_subtype_le _
  have hQne : QG ≠ ⊥ := by
    intro he
    apply Q.ne_bot_of_dvd_card hsJ
    apply map_injective J.subtype_injective
    simpa only [Subgroup.map_bot] using he
  have hcontrol : M ⊓ normalizer (QG : Set G) ≤ C ⊔ D := by
    intro x hx
    have hxL : x ∈ M ⊓ normalizer (residualGenerated M z t : Set G) :=
      ⟨hx.1, g.normalizer_control QG hQJ hQne hx.2⟩
    have hprod := Set.ext_iff.mp d.point_inter_residual_normalizer x |>.mp hxL
    obtain ⟨p, hp, a, ha, rfl⟩ := hprod
    exact mul_mem_sup (g.borelTwoCore_le_distinguished_centralizer hp) ha
  have hfr := congrArg (fun H : Subgroup M => H.map M.subtype) R'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, M.range_subtype, subgroupOf_map_subtype,
    inf_of_le_left d.distinguished_centralizer_le] at hfr
  apply le_antisymm
  · apply hfr.ge.trans
    refine sup_le ?_ le_sup_left
    apply le_trans ?_ hcontrol
    refine le_inf (map_subtype_le _) ?_
    have hn := ((R' : Subgroup C').map C'.subtype).le_normalizer_map M.subtype
    rwa [hmap] at hn
  · exact sup_le d.distinguished_centralizer_le inf_le_left

public theorem Context.pointStabilizer_eq_centralizer_mul_pair
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    (M : Set G) = (centralizer (closure (Z ∩ (M : Set G)) : Set G) : Set G) *
      (residualPairStabilizer M t : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
    d.distinguished_centralizer_normal
  rw [← coe_mul_of_right_le_normalizer_left
    (centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (residualPairStabilizer M t)
    ((show residualPairStabilizer M t ≤ M from inf_le_left).trans hn)]
  exact congrArg SetLike.coe (d.pointStabilizer_eq_centralizer_sup_pair g hsemi)


public theorem Context.distinguished_centralizer_odd_index
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    Odd ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M).index := by
  let C := centralizer (closure (Z ∩ (M : Set G)) : Set G)
  let J := centralizer (residualGenerated M z t : Set G)
  let D := residualPairStabilizer M t
  have hJD : J ≤ D := d.residual_centralizer_le_pair
  have hDC : D ≤ normalizer (C : Set G) := inf_le_left.trans
    ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
      d.distinguished_centralizer_normal)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hDC
  have hsup : C ⊔ D = M := (d.pointStabilizer_eq_centralizer_sup_pair g hsemi).symm
  have hinf : C ⊓ D = J := by rw [inf_comm]; exact d.pair_inf_distinguished_centralizer g
  rw [hsup, hinf] at hprod
  have hc : Nat.card C * (C.subgroupOf M).index = Nat.card M := by
    have hh := (C.subgroupOf M).card_mul_index
    rwa [Nat.card_congr (subgroupOfEquivOfLe d.distinguished_centralizer_le).toEquiv] at hh
  have hj : Nat.card J * (J.subgroupOf D).index = Nat.card D := by
    have hh := (J.subgroupOf D).card_mul_index
    rwa [Nat.card_congr (subgroupOfEquivOfLe hJD).toEquiv] at hh
  have he : Nat.card J * (C.subgroupOf M).index = Nat.card D := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C))
    calc
      Nat.card C * (Nat.card J * (C.subgroupOf M).index) =
          Nat.card J * (Nat.card C * (C.subgroupOf M).index) := by ring
      _ = Nat.card J * Nat.card M := by rw [hc]
      _ = Nat.card C * Nat.card D := hprod.symm
  have hi : (C.subgroupOf M).index = (J.subgroupOf D).index :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J)) (he.trans hj.symm)
  change Odd (C.subgroupOf M).index
  rw [hi]
  obtain ⟨V, hV⟩ := g.U_sylow_pair
  have hVJ : (V : Subgroup D) ≤ J.subgroupOf D := by
    intro v hv
    have hvU : (v : G) ∈ g.U := hV ▸ mem_map_of_mem D.subtype hv
    rw [g.U_eq] at hvU
    exact hvU.2
  exact Nat.not_even_iff_odd.mp (fun heven =>
    V.not_dvd_index (heven.two_dvd.trans (index_dvd_of_le hVJ)))

omit d in
public theorem LocalGeometry.S_isPGroup (g : LocalGeometry Z M z t m) : IsPGroup 2 g.S := by
  obtain ⟨V, hV⟩ := g.S_sylow
  rw [← hV]
  exact V.isPGroup'.map _

omit d in
public theorem LocalGeometry.S_le_normalizer_T (g : LocalGeometry Z M z t m) :
    g.S ≤ normalizer (g.T : Set G) := by
  obtain ⟨V, hV⟩ := g.S_sylow
  rw [← hV]
  exact map_subtype_le _

omit d in
public theorem LocalGeometry.T_normal_in_S (g : LocalGeometry Z M z t m) :
    (g.T.subgroupOf g.S).Normal :=
  normal_subgroupOf_of_le_normalizer g.S_le_normalizer_T

public theorem Context.S_le_distinguished_centralizer
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    g.S ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  let C := (centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M
  let S := g.S.subgroupOf M
  let : C.Normal := d.distinguished_centralizer_normal
  have hS : IsPGroup 2 S := g.S_isPGroup.of_equiv (subgroupOfEquivOfLe g.S_le_M).symm
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime C.index (Nat.card S) := by
    rw [hk]
    exact (d.distinguished_centralizer_odd_index g hsemi).coprime_two_right.pow_right k
  have hle : S ≤ C := relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop
    (C.relIndex_dvd_index_of_normal S) (C.relIndex_dvd_card S))
  intro s hs
  exact hle (show (⟨s, g.S_le_M hs⟩ : M) ∈ S from hs)

end BenderSuzuki.ZD.SuzukiExclusion
