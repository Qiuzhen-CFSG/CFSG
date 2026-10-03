module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import BenderSuzuki.External.Suzuki.V.theorem_2_27
public import Theory.GroupTheory.NormalSylowCoreCentralizer

/-!
# The nontrivial odd normalizer index

Put N = N_G(P) and K = O_{2'}(N). The normal Sylow subgroup of N
centralizes K. Moreover q = |N:PK| is odd and greater than one.
For the latter assertion, PK = N would make P control element fusion.
The Frobenius normal-complement theorem would give a normal two-complement
in G, contrary to the hypotheses.

These are supporting conclusions of Proposition 2.1(i), pp. 79–80, of
Glauberman, *A Characterization of the Suzuki Groups* (1968), saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization
open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The odd core of the Sylow normalizer, viewed in the ambient group. -/
@[expose] public noncomputable def normalizerOddCore (P : Sylow 2 G) : Subgroup G :=
  (pPrimeCore 2 (normalizer (P : Set G))).map (normalizer (P : Set G)).subtype

/-- The subgroup PK, viewed inside N_G(P). -/
@[expose] public noncomputable def normalizerSylowCore (P : Sylow 2 G) :
    Subgroup (normalizer (P : Set G)) :=
  (P : Subgroup G).subgroupOf (normalizer (P : Set G)) ⊔
    pPrimeCore 2 (normalizer (P : Set G))

/-- The normalizer's odd core centralizes the Sylow subgroup. -/
public theorem normalizerOddCore_le_centralizer (P : Sylow 2 G) :
    normalizerOddCore P ≤ centralizer (P : Set G) := by
  let S := P.subtype (P : Subgroup G).le_normalizer
  have : (S : Subgroup (normalizer (P : Set G))).Normal := normal_in_normalizer
  intro k hk
  obtain ⟨a, ha, rfl⟩ := hk
  have hc := S.pPrimeCore_le_centralizer_of_normal ha
  apply mem_centralizer_iff.mpr
  intro x hx
  exact congrArg Subtype.val (mem_centralizer_iff.mp hc
    ⟨x, (P : Subgroup G).le_normalizer hx⟩ hx)

/-- The index |N_G(P):PK| is odd. -/
public theorem normalizerSylowCore_index_coprime (P : Sylow 2 G) :
    Nat.Coprime 2 (normalizerSylowCore P).index := by
  let S := P.subtype (P : Subgroup G).le_normalizer
  have hc : Nat.Coprime 2 (S : Subgroup (normalizer (P : Set G))).index :=
    Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index
  exact hc.of_dvd_right (index_dvd_of_le (show
    (S : Subgroup (normalizer (P : Set G))) ≤ normalizerSylowCore P from le_sup_left))

/-- The product PK is a proper subgroup of the Sylow normalizer. -/
public theorem Hypotheses.normalizerSylowCore_ne_top (P : Sylow 2 G)
    (h : Hypotheses P) : normalizerSylowCore P ≠ ⊤ := by
  intro he
  apply h.not_hasNormalPComplement P
  apply BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_27_v P
  intro x y hx hy hxy
  obtain ⟨n, hn, hnxy⟩ := h.fusion x hx y hy (isConj_iff.mpr hxy)
  have hnmem : (⟨n, hn⟩ : normalizer (P : Set G)) ∈ normalizerSylowCore P := by
    rw [he]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp hnmem
  have haP : (a : G) ∈ (P : Subgroup G) := ha
  have hbC : (b : G) ∈ centralizer (P : Set G) :=
    normalizerOddCore_le_centralizer P (mem_map_of_mem _ hb)
  have hbx : (b : G) * x * (b : G)⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hbC x hx).symm
  have habG : (a : G) * (b : G) = n := congrArg Subtype.val hab
  refine ⟨⟨a, haP⟩, ?_⟩
  rw [← habG, mul_inv_rev] at hnxy
  calc
    (a : G) * x * (a : G)⁻¹ = (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹ := by rw [hbx]
    _ = y := by simpa only [mul_assoc] using hnxy

/-- The integer q in Glauberman's character construction is greater than one. -/
public theorem Hypotheses.one_lt_normalizerSylowCore_index (P : Sylow 2 G)
    (h : Hypotheses P) : 1 < (normalizerSylowCore P).index := by
  exact (normalizerSylowCore P).one_lt_index_of_ne_top (h.normalizerSylowCore_ne_top P)

end Glauberman.SuzukiCharacterization
