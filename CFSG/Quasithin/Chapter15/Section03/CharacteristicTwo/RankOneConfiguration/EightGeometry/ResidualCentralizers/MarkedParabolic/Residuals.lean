module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Basic
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Comparing the two residuals of a four-block preimage

Squaring a permutation preserving the unordered four-plus-four partition
preserves each block. Each restriction is in S₄, so the original permutation
has forty-eighth power one. With a two-group kernel, every element upstairs
therefore has order divisible by no primes other than two and three.
The quotient by its three-elements is a two-group, while all three-elements
lie in the two-residual. These two inclusions prove the residual equality;
the residuals are not identified by definition.

The final theorem needs only containment of the marked image in the concrete
four-block stabilizer. Constructing that marking remains a separate geometric
step in 15.3.32(4).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.32(4), printed p.1133.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G H : Type*} [Group G] [Group H]

private theorem residual_eq_of_two_three_orders (h : ∀ g : G, ∃ n m : ℕ, g ^ (2 ^ n * 3 ^ m) = 1) :
    primePowerGenerated 3 G = pResidual 2 G := by
  apply le_antisymm
  · rw [primePowerGenerated_le_iff]
    intro g n hn
    apply mem_pResidual_of_orderOf_coprime
    exact ((show Nat.Coprime 2 3 from by decide).pow_right n).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hn)
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (primePowerGenerated 3 G) x
    obtain ⟨n, m, hg⟩ := h g
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply mem_primePowerGenerated_of_pow (n := m)
    rwa [← pow_mul]

private theorem residual_eq_of_two_kernel (f : G →* H) (hk : IsPGroup 2 f.ker)
    (h : ∀ g : G, ∃ n m : ℕ, f g ^ (2 ^ n * 3 ^ m) = 1) :
    primePowerGenerated 3 G = pResidual 2 G := by
  apply residual_eq_of_two_three_orders
  intro g
  obtain ⟨n, m, hm⟩ := h g
  have hmem : g ^ (2 ^ n * 3 ^ m) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hm]
  obtain ⟨k, hk⟩ := hk ⟨g ^ (2 ^ n * 3 ^ m), hmem⟩
  refine ⟨n + k, m, ?_⟩
  have he : 2 ^ (n + k) * 3 ^ m = (2 ^ n * 3 ^ m) * 2 ^ k := by
    rw [pow_add]
    ac_rfl
  rw [he, pow_mul]
  exact congrArg Subtype.val hk

open Subgroup Equiv
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem square_block (g : S8) (hg : g ∈ fourStabilizer) (i : Fin 8) :
    (g (g i)).val / 4 = i.val / 4 := by
  have h := hg (g i) i
  change (g (g i)).val / 4 = (g i).val / 4 ↔ (g i).val / 4 = i.val / 4 at h
  have hi := i.isLt
  have hgi := (g i).isLt
  have hggi := (g (g i)).isLt
  omega

private theorem fourStabilizer_pow (g : S8) (hg : g ∈ fourStabilizer) : g ^ 48 = 1 := by
  apply Equiv.ext
  intro i
  let B := {j : Fin 8 // j.val / 4 = i.val / 4}
  have hb : Fintype.card B = 4 := by
    change Fintype.card {j : Fin 8 // j.val / 4 = i.val / 4} = 4
    fin_cases i <;> decide
  have hs : ∀ j : Fin 8, ((g ^ 2) j).val / 4 = i.val / 4 ↔ j.val / 4 = i.val / 4 := by
    intro j
    simp only [pow_two, Perm.mul_apply, square_block g hg]
  let e : Perm B := (g ^ 2).subtypePerm hs
  have he : e ^ 24 = 1 := by
    have : e ^ Nat.card (Perm B) = 1 := pow_card_eq_one'
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, hb,
      show Nat.factorial 4 = 24 from rfl] using this
  change ((g ^ 2).subtypePerm hs) ^ 24 = 1 at he
  rw [Perm.subtypePerm_pow] at he
  have hx := congrArg (fun p : Perm B => (p ⟨i, rfl⟩).val) he
  change ((g ^ 2) ^ 24) i = i at hx
  rw [← pow_mul] at hx
  exact hx

/-- A two-group kernel and the concrete four-block image identify O^{3′} with O². -/
theorem residual_eq_of_fourBlock_image (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8)) (K : Subgroup G) (hKI : K ≤ I)
    (hK : (d.starImage I K).map e.toMonoidHom ≤
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer) :
    RankOne.threeResidualIn K = (pResidual 2 K).map K.subtype := by
  let f : K →* Equiv.Perm (Fin 8) :=
    e.toMonoidHom.comp ((d.starMap I).comp (inclusion hKI))
  have hk : f.ker = ((d.starMap I).ker).comap (inclusion hKI) := by
    ext k
    change e (d.starMap I (inclusion hKI k)) = 1 ↔ d.starMap I (inclusion hKI k) = 1
    exact e.map_eq_one_iff
  have htwo : IsPGroup 2 f.ker := by
    rw [hk]
    exact (star_kernel_isTwo d c P hP hC).comap_of_injective _ (inclusion_injective hKI)
  have himage (k : K) : f k ∈
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
    apply hK
    exact mem_map_of_mem _ (mem_map_of_mem _
      (show (⟨k, hKI k.property⟩ : I) ∈ K.subgroupOf I from k.property))
  have hres := residual_eq_of_two_kernel f htwo (fun k =>
    ⟨4, 1, show f k ^ (2 ^ 4 * 3 ^ 1) = 1 from fourStabilizer_pow (f k) (himage k)⟩)
  change (primePowerGenerated 3 K).map K.subtype = _
  rw [hres]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic

end
