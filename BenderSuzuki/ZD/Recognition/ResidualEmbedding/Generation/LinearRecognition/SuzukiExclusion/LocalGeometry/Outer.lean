module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PResidual.PrimeSet
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The outer quotient and the pair-stabilizer order

The preimage of Inn(L) in N_G(L) is the relative subgroup LJ. Transport of
Suzuki inner-field coverage proves that its index divides 2*m+1. Thus the
odd-quotient residual O^{2'}(N_G(L)), and every two-subgroup of N_G(L), lie
in LJ. This is not the odd core O_{2'} or the two-quotient residual O^2.

For the pair-stabilizer bound, use N_G(L)=LD, |L∩D|=q-1 and the faithful
action of N_G(L)/J on L. The supplied embedding J → L cancels |J| from
these order identities. No regular-action conclusion is assumed here.

Source: GLS4, Chapter 2, Lemma 14.2(c,e), and Chapter 4, Lemma 3.1(b).
-/

noncomputable section
open Subgroup
namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G]

private theorem normalizer_inner_preimage (L : Subgroup G) :
    ((MulAut.innerSubgroup L).comap L.normalizerMonoidHom).map
      (normalizer (L : Set G)).subtype = L ⊔ centralizer (L : Set G) := by
  have hi : (L.subgroupOf (normalizer (L : Set G))).map L.normalizerMonoidHom =
      MulAut.innerSubgroup L := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      ext y
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x, L.le_normalizer x.property⟩, x.property, ?_⟩
      ext y
      rfl
  rw [← hi, comap_map_eq, normalizerMonoidHom_ker, Subgroup.map_sup,
    map_subgroupOf_eq_of_le L.le_normalizer,
    map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer _)]

private theorem normalizer_inner_subgroup (L : Subgroup G) :
    (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) =
      (MulAut.innerSubgroup L).comap L.normalizerMonoidHom := by
  apply map_injective (normalizer (L : Set G)).subtype_injective
  rw [normalizer_inner_preimage,
    map_subgroupOf_eq_of_le (sup_le L.le_normalizer (Subgroup.centralizer_le_normalizer _))]

variable [Finite G] {Z : Set G} {M : Subgroup G} {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.normalizer_inner_index_dvd :
    ((residualGenerated M z t ⊔ centralizer (residualGenerated M z t : Set G)).subgroupOf
      (normalizer (residualGenerated M z t : Set G))).index ∣ 2 * m + 1 := by
  rw [normalizer_inner_subgroup, index_comap]
  apply (relIndex_dvd_index_of_normal _ _).trans
  change Nat.card (MulAut.Outer (residualGenerated M z t)) ∣ _
  rw [Nat.card_congr (MulAut.outerCongr d.model).toEquiv]
  exact MatrixGroups.suzuki_outer_index_dvd m d.parameter_pos

public theorem Context.aut_card_dvd : Nat.card (MulAut (residualGenerated M z t)) ∣
    Nat.card (residualGenerated M z t) * (2 * m + 1) := by
  let L := residualGenerated M z t
  let I := MulAut.innerSubgroup L
  have hd : I.index ∣ 2 * m + 1 := by
    change Nat.card (MulAut.Outer L) ∣ _
    rw [Nat.card_congr (MulAut.outerCongr d.model).toEquiv]
    exact MatrixGroups.suzuki_outer_index_dvd m d.parameter_pos
  rw [← I.card_mul_index]
  exact Nat.mul_dvd_mul (card_range_dvd (MulAut.conj : L →* MulAut L)) hd

/-- This is O^{2'}, the residual for odd-order quotients. -/
public theorem Context.oddResidual_normalizer_le :
    (piResidual {p : Nat.Primes | p.val ≠ 2}
      (normalizer (residualGenerated M z t : Set G))).map
        (normalizer (residualGenerated M z t : Set G)).subtype ≤
      residualGenerated M z t ⊔ centralizer (residualGenerated M z t : Set G) := by
  let L := residualGenerated M z t
  let N := normalizer (L : Set G)
  let F := (L ⊔ centralizer (L : Set G)).subgroupOf N
  have hF : F = (MulAut.innerSubgroup L).comap L.normalizerMonoidHom :=
    normalizer_inner_subgroup L
  have : F.Normal := by rw [hF]; infer_instance
  have ho : Odd F.index := (show Odd (2 * m + 1) from ⟨m, by omega⟩).of_dvd_nat
    (d.normalizer_inner_index_dvd)
  have hpi : IsPiGroup {p : Nat.Primes | p.val ≠ 2} (N ⧸ F) := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp heq
    rw [heq] at hp
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hp)
  have hr : piResidual {p : Nat.Primes | p.val ≠ 2} N ≤ F :=
    sInf_le ⟨(inferInstance : F.Normal), hpi⟩
  exact (map_le_iff_le_comap).mpr hr

public theorem Context.twoSubgroup_le_inner (T : Subgroup G) (hp : IsPGroup 2 T)
    (hTN : T ≤ normalizer (residualGenerated M z t : Set G)) :
    T ≤ residualGenerated M z t ⊔ centralizer (residualGenerated M z t : Set G) := by
  let L := residualGenerated M z t
  let N := normalizer (L : Set G)
  let F := (L ⊔ centralizer (L : Set G)).subgroupOf N
  have hF : F = (MulAut.innerSubgroup L).comap L.normalizerMonoidHom :=
    normalizer_inner_subgroup L
  have : F.Normal := by rw [hF]; infer_instance
  have ho : Odd F.index := (show Odd (2 * m + 1) from ⟨m, by omega⟩).of_dvd_nat
    (d.normalizer_inner_index_dvd)
  have hp' : IsPGroup 2 (T.subgroupOf N) := hp.of_equiv (subgroupOfEquivOfLe hTN).symm
  obtain ⟨k, hk⟩ := hp'.exists_card_eq
  have hcop : Nat.Coprime F.index (Nat.card (T.subgroupOf N)) := by
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hle : T.subgroupOf N ≤ F := (relIndex_eq_one).mp
    (Nat.eq_one_of_dvd_coprimes hcop (F.relIndex_dvd_index_of_normal _)
      (relIndex_dvd_card _ _))
  intro x hx
  exact hle (show (⟨x, hTN hx⟩ : N) ∈ T.subgroupOf N from hx)

open scoped Pointwise in
public theorem Context.pair_card_dvd
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) :
    Nat.card (residualPairStabilizer M t) ∣
      (2 ^ (2 * m + 1) - 1) * Nat.card (residualGenerated M z t) * (2 * m + 1) := by
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let J := centralizer (L : Set G)
  obtain ⟨n, hn, hmodels, hAL, hDN, h1, h2, hAN, hAE, hAC, hZ, hprod, hN, hJD, hrest⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  have hsup : L ⊔ D = N := by
    apply SetLike.coe_injective
    rw [coe_mul_of_right_le_normalizer_left L D hDN]
    exact hN.symm
  have hE := (residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter_pos d.model).2
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes L D hDN
  rw [hsup, inf_comm L D, hE] at hmul
  let a := L.normalizerMonoidHom
  have hNj : Nat.card N = Nat.card J * Nat.card a.range := by
    rw [← a.ker.card_mul_index, index_ker, normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (L : Set G))).toEquiv]
  obtain ⟨k, hk⟩ := card_dvd_of_injective f hf
  have hcancel : k * Nat.card D = (2 ^ (2 * m + 1) - 1) * Nat.card a.range := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
    calc
      Nat.card J * (k * Nat.card D) = Nat.card L * Nat.card D := by
        rw [hk]
        ac_rfl
      _ = (2 ^ (2 * m + 1) - 1) * Nat.card N := hmul
      _ = Nat.card J * ((2 ^ (2 * m + 1) - 1) * Nat.card a.range) := by
        rw [hNj]
        ac_rfl
  have hd : Nat.card D ∣ (2 ^ (2 * m + 1) - 1) * Nat.card a.range := by
    rw [← hcancel]
    exact dvd_mul_left _ _
  have hda : Nat.card a.range ∣ Nat.card L * (2 * m + 1) :=
    a.range.card_subgroup_dvd_card.trans (d.aut_card_dvd)
  simpa only [Nat.mul_assoc] using hd.trans (Nat.mul_dvd_mul_left _ hda)

end BenderSuzuki.ZD.SuzukiExclusion
