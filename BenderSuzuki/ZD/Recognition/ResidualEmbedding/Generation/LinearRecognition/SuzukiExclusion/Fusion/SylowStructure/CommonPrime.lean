module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowObstruction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
public import FeitThompson.BGsection3.Remaining
/-!
# The Suzuki common-prime argument

For A = M° and J = C_G(L), the two-core of the Borel has trivial
intersection with the odd local torus. This gives D ∩ C_G(A) = J.
Relative normality of C_G(A) and the point-stabilizer order formula then
show that |C_G(A)| divides q³(q²-q+1)|J|.

The binary multiplicative order of the primitive prime excludes it from
the automorphism group of A. Thus every subgroup of M at that prime
centralizes A. If |J| and q-1 were coprime, the coprime cyclic torus action
would preserve a Sylow subgroup of C_G(A), also Sylow in M, contradicting
the established Lemma 14.4(a).

Source: GLS4, Chapter 2, (14D)–(14F) and Lemma 14.4(b),
`refs/KGroup/GLS4/Chapter2.tex`, approximately lines 2480–2525.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.distinguished_le_residual :
    closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t :=
  proper_residualGenerated_contains_distinguishedClosure d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair

public theorem Context.distinguished_elementary_card :
    IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) ∧
      Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ (2 * m + 1) :=
  residualGenerated_suzuki_distinguishedClosure d.minimal.disconnected d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.distinguished_le_residual
    (by have := d.parameter_pos; omega) d.model

public theorem Context.distinguished_centralizer_le :
    centralizer (closure (Z ∩ (M : Set G)) : Set G) ≤ M := by
  exact (Subgroup.centralizer_le_normalizer _).trans
    (distinguishedClosure_normalizer d.minimal.disconnected).le

public theorem Context.distinguished_centralizer_normal :
    ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M).Normal := by
  have hn := normal_subgroupOf_centralizer_normalizer
    (closure (Z ∩ (M : Set G)) : Set G)
  exact Eq.mp (congrArg
    (fun H : Subgroup G =>
      ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf H).Normal)
    (distinguishedClosure_normalizer d.minimal.disconnected)) hn

public theorem Context.pair_le_residual_normalizer :
    residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G) :=
  residualPairStabilizer_le_normalizer_residualGenerated d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair

public theorem Context.residual_centralizer_le_pair :
    centralizer (residualGenerated M z t : Set G) ≤ residualPairStabilizer M t :=
  centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected d.z_mem d.z_mem_M

public theorem Context.borelTwoCore_disjoint_pair :
    Disjoint (borelTwoCore M z t) (residualPairStabilizer M t) := by
  have hP : IsPGroup 2 (borelTwoCore M z t) := pCore_isPGroup.map _
  obtain ⟨_, hc⟩ := residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    (by have := d.parameter_pos; omega) d.model
  have ho : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)) := by
    rw [hc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hd : Disjoint (borelTwoCore M z t)
      (residualPairStabilizer M t ⊓ residualGenerated M z t) :=
    disjoint_of_coprime_natCard (by rw [hk]; exact ho.coprime_two_left.pow_left k)
  apply disjoint_def.mpr
  intro x hxP hxD
  exact disjoint_def.mp hd hxP ⟨hxD, (map_subtype_le _ hxP).2⟩

public theorem Context.pair_inf_distinguished_centralizer (g : LocalGeometry Z M z t m) :
    residualPairStabilizer M t ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) =
      centralizer (residualGenerated M z t : Set G) := by
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ normalizer (residualGenerated M z t : Set G) ⊓
        centralizer (closure (Z ∩ (M : Set G)) : Set G) :=
      ⟨d.pair_le_residual_normalizer hx.1, hx.2⟩
    rw [show x ∈ normalizer (residualGenerated M z t : Set G) ⊓
        centralizer (closure (Z ∩ (M : Set G)) : Set G) ↔
        x ∈ (borelTwoCore M z t : Set G) *
          (centralizer (residualGenerated M z t : Set G) : Set G) from
      Set.ext_iff.mp g.centralizer_in_normalizer x] at hxN
    obtain ⟨p, hp, j, hj, rfl⟩ := hxN
    have hpD : p ∈ residualPairStabilizer M t := by
      simpa using (residualPairStabilizer M t).mul_mem hx.1
        ((residualPairStabilizer M t).inv_mem (d.residual_centralizer_le_pair hj))
    have hp1 := disjoint_def.mp d.borelTwoCore_disjoint_pair hp hpD
    simpa [hp1] using hj
  · exact le_inf d.residual_centralizer_le_pair
      (centralizer_le (show (closure (Z ∩ (M : Set G)) : Set G) ⊆
        (residualGenerated M z t : Set G) from d.distinguished_le_residual))

public theorem Context.distinguished_centralizer_card_dvd (g : LocalGeometry Z M z t m) :
    Nat.card (centralizer (closure (Z ∩ (M : Set G)) : Set G)) ∣
      (2 ^ (2 * m + 1)) ^ 3 *
        ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) *
          Nat.card (centralizer (residualGenerated M z t : Set G)) := by
  let C := centralizer (closure (Z ∩ (M : Set G)) : Set G)
  let D := residualPairStabilizer M t
  let J := centralizer (residualGenerated M z t : Set G)
  have hDC : D ≤ normalizer (C : Set G) := by
    have hn := (normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
      d.distinguished_centralizer_normal
    exact (show D ≤ M from inf_le_left).trans hn
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hDC
  have hCJ : C ⊓ D = J := by rw [inf_comm]; exact d.pair_inf_distinguished_centralizer g
  rw [hCJ] at he
  have hdiv : Nat.card (C ⊔ D : Subgroup G) ∣ Nat.card M :=
    card_dvd_of_le (sup_le d.distinguished_centralizer_le inf_le_left)
  have hmul : Nat.card C * Nat.card D ∣ Nat.card J * Nat.card M := by
    rw [he]
    exact Nat.mul_dvd_mul_left _ hdiv
  rw [d.card_pointStabilizer] at hmul
  apply (Nat.mul_dvd_mul_iff_right (Nat.card_pos (α := D))).mp
  convert hmul using 1
  ring

omit d [Group G] [Finite G] in
private theorem prime_not_dvd_binary_aut {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] {n p : ℕ} (hc : Nat.card E = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : n < orderOf (2 : ZMod p)) :
    ¬ p ∣ Nat.card (MulAut E) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hc]
  intro hd
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.ne_one)
  have hpow : (2 : ZMod p) ^ n = (2 : ZMod p) ^ i.val := by
    have hz := (ZMod.natCast_eq_zero_iff (2 ^ n - 2 ^ i.val) p).mpr hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide) i.isLt.le)] at hz
    simpa only [Nat.cast_pow, Nat.cast_ofNat, sub_eq_zero] using hz
  have hone : (2 : ZMod p) ^ (n - i.val) = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero i.val htwo)
    rw [← pow_add, Nat.add_sub_of_le i.isLt.le, mul_one]
    exact hpow
  have hle := Nat.le_of_dvd (by omega : 0 < n - i.val) (orderOf_dvd_of_pow_eq_one hone)
  omega

public theorem Context.primitive_pSubgroup_centralizes {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hord : 2 * m + 1 < orderOf (2 : ZMod p))
    (R : Subgroup M) (hR : IsPGroup p R) :
    R.map M.subtype ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  let A := closure (Z ∩ (M : Set G))
  have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal d.reduction
    d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  obtain ⟨hA, hAc⟩ := residualGenerated_suzuki_distinguishedClosure d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper hAL
    (by have := d.parameter_pos; omega) d.model
  let : IsElementaryAbelian 2 A := hA
  have hnot : ¬ p ∣ Nat.card (MulAut A) := prime_not_dvd_binary_aut hAc hp hp2 hord
  have hMN : M ≤ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
  let i : M →* normalizer (A : Set G) := inclusion hMN
  let ρ : M →* MulAut A := A.normalizerMonoidHom.comp i
  intro x hx
  obtain ⟨r, hr, rfl⟩ := hx
  have h1 : ρ r = 1 := by
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hpow : (ρ r) ^ (p ^ k) = 1 := by
      rw [← map_pow]
      exact (congrArg ρ (congrArg Subtype.val hk)).trans (map_one ρ)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((hp.coprime_iff_not_dvd.mpr hnot).pow_left k)
      (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard _))
  have hker : i r ∈ A.normalizerMonoidHom.ker := h1
  rw [normalizerMonoidHom_ker] at hker
  exact hker


public theorem Context.torus_eq_local_pair :
    residualCommutator M t = residualPairStabilizer M t ⊓ residualGenerated M z t := by
  obtain ⟨_, hc⟩ := residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    (by have := d.parameter_pos; omega) d.model
  have ho : Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)) := by
    rw [hc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one
  exact residualCommutator_eq_local_pair (d.minimal.disconnected.involutions t d.t_mem)
    d.pair_le_residual_normalizer ho (fun _ hx =>
      residualGenerated_suzuki_pair_inverted d.minimal.disconnected d.reduction
        d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
        (by have := d.parameter_pos; omega) d.model hx)

public theorem Context.torus_cyclic : IsCyclic (residualCommutator M t) := by
  rw [d.torus_eq_local_pair]
  exact (residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
    (by have := d.parameter_pos; omega) d.model).1

public theorem Context.common_prime (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) :
    ∃ s : ℕ, s.Prime ∧
      s ∣ Nat.card (centralizer (residualGenerated M z t : Set G)) ∧
      s ∣ 2 ^ (2 * m + 1) - 1 := by
  apply Nat.Prime.not_coprime_iff_dvd.mp
  intro hcop
  let C := centralizer (closure (Z ∩ (M : Set G)) : Set G)
  let K := residualCommutator M t
  let q := 2 ^ (2 * m + 1)
  have hq : 1 ≤ q := Nat.one_le_two_pow
  have hqc : Nat.Coprime (q - 1) q :=
    (Nat.coprime_self_sub_left hq).mpr (Nat.coprime_one_left _)
  have hcc : Nat.Coprime (q - 1) (q ^ 2 - q + 1) := by
    have he : q ^ 2 - q + 1 = 1 + (q - 1) * q := by
      simp only [Nat.sub_mul, one_mul, pow_two]
      omega
    rw [he]
    exact (Nat.coprime_add_mul_left_right (q - 1) 1 q).mpr (Nat.coprime_one_right _)
  have hKC : Nat.Coprime (Nat.card K) (Nat.card C) := by
    rw [show Nat.card K = q - 1 from d.torus_card]
    exact (((hqc.pow_right 3).mul_right hcc).mul_right hcop.symm).coprime_dvd_right
      (d.distinguished_centralizer_card_dvd g)
  obtain ⟨p, hp, hnp, _, hord, _, _, hobs⟩ := d.exists_prime_not_normalizing_sylow g hsemi
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := d.parameter_pos; omega
  have horder : 2 * m + 1 < orderOf (2 : ZMod p) := by rw [hord]; omega
  have hKM : K ≤ M := by rw [show K = _ from d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left
  have hn : K ≤ normalizer (C : Set G) := hKM.trans
    ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
      d.distinguished_centralizer_normal)
  let : IsCyclic K := d.torus_cyclic
  let : MulDistribMulAction K C := conjMulDistribMulActionOfLeNormalizer K C hn
  obtain ⟨P, hPI⟩ := exists_invariant_sylow_of_solvable_operator_coprime hKC (p := p)
  let i : C →* M := inclusion d.distinguished_centralizer_le
  obtain ⟨R, hR⟩ := P.exists_comap_eq_of_injective (f := i) (inclusion_injective _)
  have hRC := d.primitive_pSubgroup_centralizes hp hp2 horder R R.isPGroup'
  have hmap : (P : Subgroup C).map i = (R : Subgroup M) := by
    apply le_antisymm
    · rw [← hR]
      exact map_comap_le _ _
    · intro r hr
      have hc : (r : G) ∈ C := hRC (mem_map_of_mem M.subtype hr)
      refine ⟨⟨r, hc⟩, ?_, rfl⟩
      rw [← hR]
      exact hr
  have hmaps : (R : Subgroup M).map M.subtype = (P : Subgroup C).map C.subtype := by
    rw [← hmap, map_map]
    rfl
  apply hobs R
  rw [hmaps]
  apply le_normalizer_iff.mpr
  intro k hk x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨(⟨k, hk⟩ : K) • y, (hPI.invariant ⟨k, hk⟩ y).mp hy, rfl⟩

end BenderSuzuki.ZD.SuzukiExclusion
