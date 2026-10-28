module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.MixedFrattini
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.Fusion
public import Theory.SpecificGroups.PSL2.PrimeOuterFixed

/-!
# The mixed outer/inner action case of 2.5.21

Represent the nontrivial inner action on Kˣ by an involution u. Conjugacy of
PSL₂ involutions supplies an element l of Kˣ sending u to the original t.
Replace tᵍ by its l-conjugate, keeping the original t, x, K and Kˣ fixed.
The action on K is unchanged, while the action on Kˣ is now conjugation by
t. Prime-field PGL₂ coverage constructs the outer fixed subgroup's odd
dihedral model. The checked mixed Frattini calculation then gives the
contradiction. Neither alignment nor the outer fixed model is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.5.21, printed p.567. The alignment makes explicit the conjugacy choice
needed before the source's marked Frattini assertion.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

/-- The genuine mixed case: an outer action on K and nontrivial inner action
on Kˣ are impossible for a conjugate of the original marked involution.
The odd-dihedral centralizer and the alignment of the inner action with t
are constructed, rather than supplied as additional model premises. -/
theorem false_of_mixed_actions (d : Incoming κ G p) (g : G)
    (hiK : g⁻¹ * d.t * g ∈ normalizer (d.K : Set G))
    (hiL : g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G))
    (hout : d.K.normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiK⟩ ∉
      (MulAut.conj : d.K →* MulAut d.K).range)
    (hin : (conjugate d.K d.x).normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiL⟩ ∈
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range)
    (hnontriv : g⁻¹ * d.t * g ∉ centralizer (conjugate d.K d.x : Set G)) : False := by
  let L := conjugate d.K d.x
  let i := g⁻¹ * d.t * g
  let eL : L ≃* PSL(2, ZMod p) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
  have hLc : center L = ⊥ := by
    apply bot_unique
    intro c hc
    have hh : eL c ∈ center PSL(2, ZMod p) := (centerCongr eL ⟨c, hc⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot, mem_bot] at hh
    exact eL.injective (hh.trans eL.map_one.symm)
  have hisq : i ^ 2 = 1 := by
    have ht : d.t ^ 2 = 1 := by rw [← d.t_order]; exact pow_orderOf_eq_one d.t
    simpa only [map_pow, MulAut.conj_apply, inv_inv, map_one] using congrArg (MulAut.conj g⁻¹) ht
  obtain ⟨u, hu⟩ := hin
  have hu2 : u ^ 2 = 1 := by
    apply conj_injective_of_center_eq_bot hLc
    rw [map_pow, hu, ← map_pow,
      show (⟨i, hiL⟩ : normalizer (L : Set G)) ^ 2 = 1 from Subtype.ext hisq,
      map_one, map_one]
  have hune : u ≠ 1 := by
    intro hone
    have hi1 : L.normalizerMonoidHom ⟨i, hiL⟩ = 1 := by rw [← hu, hone, map_one]
    have hker : (⟨i, hiL⟩ : normalizer (L : Set G)) ∈ L.normalizerMonoidHom.ker := hi1
    rw [normalizerMonoidHom_ker] at hker
    exact hnontriv hker
  have huo : orderOf (u : G) = 2 := by
    rw [orderOf_coe]
    exact orderOf_eq_prime_iff.mpr ⟨hu2, hune⟩
  obtain ⟨l, hl, hlt⟩ := involutions_conjugate_in_factor L eL u.property d.mark_mem huo d.t_order
  let h := g * l⁻¹
  let j := h⁻¹ * d.t * h
  have hji : j = l * i * l⁻¹ := by dsimp [j, h, i]; group
  have hlCK : l ∈ centralizer (d.K : Set G) := by
    intro k hk
    exact (commutator_eq_bot_iff_le_centralizer.mp d.commuting hk l hl).symm
  have hlNK : l ∈ normalizer (d.K : Set G) := Subgroup.centralizer_le_normalizer _ hlCK
  have hlNL : l ∈ normalizer (L : Set G) := L.le_normalizer hl
  have hjK : j ∈ normalizer (d.K : Set G) := by
    rw [hji]
    exact mul_mem (mul_mem hlNK hiK) (inv_mem hlNK)
  have hjL : j ∈ normalizer (L : Set G) := by
    rw [hji]
    exact mul_mem (mul_mem hlNL hiL) (inv_mem hlNL)
  have hKact : d.K.normalizerMonoidHom ⟨j, hjK⟩ =
      d.K.normalizerMonoidHom ⟨i, hiK⟩ := by
    have hl1 : d.K.normalizerMonoidHom ⟨l, hlNK⟩ = 1 := by
      change (⟨l, hlNK⟩ : normalizer (d.K : Set G)) ∈ d.K.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hlCK
    have he : (⟨j, hjK⟩ : normalizer (d.K : Set G)) =
        ⟨l, hlNK⟩ * ⟨i, hiK⟩ * ⟨l, hlNK⟩⁻¹ := Subtype.ext hji
    rw [he, map_mul, map_mul, map_inv, hl1, one_mul, inv_one, mul_one]
  have hLact : L.normalizerMonoidHom ⟨j, hjL⟩ =
      MulAut.conj (⟨d.t, d.mark_mem⟩ : L) := by
    have hlact : L.normalizerMonoidHom ⟨l, hlNL⟩ = MulAut.conj (⟨l, hl⟩ : L) := by
      ext a
      rfl
    have he : (⟨j, hjL⟩ : normalizer (L : Set G)) =
        ⟨l, hlNL⟩ * ⟨i, hiL⟩ * ⟨l, hlNL⟩⁻¹ := Subtype.ext hji
    rw [he, map_mul, map_mul, map_inv, ← hu, hlact, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subtype.ext hlt)
  have hjout : d.K.normalizerMonoidHom ⟨j, hjK⟩ ∉
      (MulAut.conj : d.K →* MulAut d.K).range := by rwa [hKact]
  have hjsq : j ^ 2 = 1 := by
    rw [hji]
    simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj l) hisq
  obtain ⟨n, hn, hlarge, ⟨e⟩⟩ := Theory.PSL2.prime_outer_relative_centralizer_dihedral
    (by have := d.prime_ge; omega) d.K d.model j hjK hjsq hjout
  have hjnc : j ∉ centralizer (d.K : Set G) := by
    intro hjc
    have ha1 : d.K.normalizerMonoidHom ⟨j, hjK⟩ = 1 := by
      change (⟨j, hjK⟩ : normalizer (d.K : Set G)) ∈ d.K.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hjc
    exact hjout (ha1 ▸ (MonoidHom.range _).one_mem)
  exact d.false_of_mixed_aligned_inner_action h hn (by omega) e hjL hLact hjnc

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
