module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Theory.GroupTheory.CentralExtensionSwap

/-!
# Split-torus primes in the G₂ universal kernel

For a finite field of order q and a prime r > 3 dividing q − 1, the actual
split torus contains a Sylow r-subgroup of G₂(q). Its two cyclic factors
have generators exchanged by the Weyl element `weylS`. In any central
extension, this exchange forces the two lifts to commute: their central
commutator has both odd order and square one. Their full preimage is
abelian, so central Sylow transfer excludes r from a perfect central kernel.

The index is computed from the checked model order. At q ≡ 1 modulo r
that index is congruent to 12; the restrictions r ≠ 2,3 are essential.
This proves the split branch without an assumed local configuration or
multiplier value. The last theorem applies to the literal canonical cover.
It holds in both characteristics and in particular for the source prime
fields of order p > 3.

Source: the covering calculation underlying Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408 (PDF pp.418–419), and GLS III §6.1. The octonion torus,
Weyl maps and order formula are attributed ATLAS ports; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. The coordinate conjugation proof follows
`LieAutomorphismExtensions/InnerFieldCoverage/FrameAlignment/WeylCorrection.lean`.
-/

public section

open Subgroup

namespace Atlas.G2.MultiplierOrdinary.OddSplitTorus
open Atlas.SplitOctonion

variable {F : Type*} [Field F]

private theorem weylS_torus (l m : Fˣ) :
    weylS * torus l m * weylS⁻¹ = torus m l := by
  have hi : (weylS : Model F)⁻¹ = weylS :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using weylS_sq (K := F))
  rw [hi]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus, torusEquiv, torusLinear, torusWeights,
      weylS, weylSEquiv, weylSLinear, weylSApply] <;> field_simp
  all_goals simp

private theorem pair_generates (P : Subgroup Fˣ) (z : P)
    (hz : ∀ u : P, u ∈ zpowers z) :
    closure ({torus z 1, torus 1 z} : Set (Model F)) =
      (P.prod P).map torusHom := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(z, 1), ⟨z.property, P.one_mem⟩, rfl⟩
    · exact ⟨(1, z), ⟨P.one_mem, z.property⟩, rfl⟩
  · rintro g ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hz ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hz ⟨b, hb⟩)
    have hi' : (z : Fˣ) ^ i = a := congrArg Subtype.val hi
    have hj' : (z : Fˣ) ^ j = b := congrArg Subtype.val hj
    have hrep : torusHom (a, b) =
        (torus (z : Fˣ) 1) ^ i * (torus 1 (z : Fˣ)) ^ j := by
      change torusHom (a, b) =
        (torusHom ((z : Fˣ), 1)) ^ i * (torusHom (1, (z : Fˣ))) ^ j
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi', hj']
    rw [hrep]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) j)

/-- The index of the literal split torus, computed from the actual G₂ order. -/
theorem splitTorus_index [Finite F] :
    (splitTorus (K := F)).index = Nat.card F ^ 6 *
      (Nat.card F ^ 5 + Nat.card F ^ 4 + Nat.card F ^ 3 +
        Nat.card F ^ 2 + Nat.card F + 1) * (Nat.card F + 1) := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hcard := (splitTorus (K := F)).card_mul_index
  rw [card_splitTorus, card_Model] at hcard
  have h6 : Nat.card F ^ 6 - 1 = (Nat.card F - 1) *
      (Nat.card F ^ 5 + Nat.card F ^ 4 + Nat.card F ^ 3 +
        Nat.card F ^ 2 + Nat.card F + 1) := by
    apply Nat.sub_eq_of_eq_add
    set a := Nat.card F - 1
    have he : Nat.card F = a + 1 := (Nat.sub_add_cancel hq).symm
    change Nat.card F ^ 6 = a * _ + 1
    rw [he]
    ring
  have h2 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    apply Nat.sub_eq_of_eq_add
    nlinarith [Nat.sub_add_cancel hq]
  have hpos : 0 < (Nat.card F - 1) ^ 2 := by
    exact pow_pos (Nat.sub_pos_of_lt (Finite.one_lt_card (α := F))) _
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hcard, h6, h2]
  ring

/-- A prime greater than three dividing the field-unit order misses the torus index. -/
theorem not_dvd_splitTorus_index [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hd : r ∣ Nat.card F - 1) :
    ¬ r ∣ (splitTorus (K := F)).index := by
  have hq : (Nat.card F : ZMod r) = 1 := by
    have hh := (CharP.cast_eq_zero_iff (ZMod r) r (Nat.card F - 1)).mpr hd
    rw [Nat.cast_sub (show 1 ≤ Nat.card F from Nat.card_pos), Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  intro hi
  rw [splitTorus_index] at hi
  have hh := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hi
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hq, one_pow] at hh
  have h12 : r ∣ 12 := (CharP.cast_eq_zero_iff (ZMod r) r 12).mp (by convert hh using 1; norm_num)
  have hp := (Fact.out : r.Prime)
  have : r = 2 ∨ r = 3 := by
    have h : r ∣ 2 ^ 2 * 3 := by norm_num at h12 ⊢; exact h12
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  omega

/-- A full Sylow subgroup in the split torus, with odd-order generators
exchanged by the actual Weyl element. -/
theorem exists_split_configuration [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hd : r ∣ Nat.card F - 1) :
    ∃ (Q : Sylow r (Model F)) (x y : Model F) (n : ℕ),
      closure ({x, y} : Set (Model F)) = (Q : Subgroup (Model F)) ∧
      n.Coprime 2 ∧ x ^ n = 1 ∧ Commute x y ∧
      weylS * x * weylS⁻¹ = y ∧ weylS * y * weylS⁻¹ = x := by
  let P : Sylow r Fˣ := Classical.choice inferInstance
  let H : Subgroup (Model F) := ((P : Subgroup Fˣ).prod (P : Subgroup Fˣ)).map torusHom
  have hHi : ¬ r ∣ H.index := by
    dsimp only [H]
    rw [Subgroup.index_map_of_injective _ torusHom_injective, Subgroup.index_prod]
    exact (Fact.out : r.Prime).not_dvd_mul
      ((Fact.out : r.Prime).not_dvd_mul P.not_dvd_index P.not_dvd_index)
      (not_dvd_splitTorus_index hr hd)
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hprod : IsPGroup r ((P : Subgroup Fˣ).prod (P : Subgroup Fˣ)) := by
    apply IsPGroup.of_card (n := k + k)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup Fˣ) (P : Subgroup Fˣ)).toEquiv,
      Nat.card_prod, hk, pow_add]
  let Q := (hprod.map torusHom).toSylow hHi
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := P)
  have hn : (Nat.card P).Coprime 2 := by
    rw [hk]
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : r.Prime)).mp h
      omega)).symm).pow_left k
  refine ⟨Q, torus z 1, torus 1 z, Nat.card P, pair_generates _ z hz, hn, ?_, ?_,
    weylS_torus _ _, weylS_torus _ _⟩
  · change torusHom ((z : Fˣ), 1) ^ Nat.card P = 1
    rw [← map_pow]
    have hzpow : (z : Fˣ) ^ Nat.card P = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := z))
    have hpair : ((z : Fˣ), (1 : Fˣ)) ^ Nat.card P = 1 :=
      Prod.ext hzpow (one_pow _)
    rw [hpair, map_one]
  · exact (Commute.all ((z : Fˣ), 1) (1, (z : Fˣ))).map torusHom

/-- The split-torus branch for every finite perfect central cover of the model. -/
theorem not_dvd_kernel_of_split [Finite F]
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model F) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F - 1) :
    ¬ r ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, n, hQ, hn, hx, hxy, hsx, hsy⟩ := exists_split_configuration hr hd
  obtain ⟨a, ha⟩ := hf x
  obtain ⟨b, hb⟩ := hf y
  have hab := CentralExtension.commute_lifts_of_swap f hf hc x y weylS
    hn hx hxy hsx hsy a b ha hb
  exact PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage f hf hc Q
    (CentralExtension.isMulCommutative_comap_of_pair_lifts f hc Q a b hab
      (by simpa only [ha, hb] using hQ))

/-- The split-torus exclusion for the literal canonical universal kernel. -/
theorem universal_not_dvd_kernel_of_split [Finite F] (hF : 2 < Nat.card F)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F - 1) :
    ¬ r ∣ Nat.card (PerfectCentralCovering.universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  exact not_dvd_kernel_of_split (PerfectCentralCovering.universalProjection (Model F))
    (PerfectCentralCovering.universalProjection_surjective _)
    (PerfectCentralCovering.universalProjection_ker_le_center _) hr hd

end Atlas.G2.MultiplierOrdinary.OddSplitTorus

end
