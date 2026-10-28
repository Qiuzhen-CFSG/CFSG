module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Covered
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.AlignFactors
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# Inner representatives for two-actions on covered Suzuki roots

Odd outer index makes a two-power automorphism inner. Its conjugator has
two-power order because the Suzuki group is centerless, and preservation
of the root Sylow puts that conjugator in the root group. Faithful descent
through a perfect central cover then supplies a representative in the
literal covered root subgroup. Genuine involution lifting preserves the
square-one condition, including for nontrivial covers of Sz(8).

Source: the paired Suzuki step of Aschbacher–Smith 13.6.6, printed p.927,
and the lifting clause I.2.2(4), pp.409–411. Automorphism coverage and odd
outer index are supplied by the proved Suzuki OuterIndex development.
-/

public section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair.KernelAction

private theorem model_center (m : ℕ) (hm : 0 < m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  let := (External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_comm (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := h ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm))).elim

private theorem model_pow (m : ℕ) (hm : 0 < m) (q : SuzukiMatrixGroup m)
    (n : ℕ) (hp : (MulAut.conj q) ^ n = 1) : q ^ n = 1 := by
  have hz : q ^ n ∈ center (SuzukiMatrixGroup m) := by
    rw [mem_center_iff]
    intro y
    have he : MulAut.conj (q ^ n) = 1 := by rw [map_pow, hp]
    have hh := DFunLike.congr_fun he y
    change q ^ n * y * (q ^ n)⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  simpa only [model_center m hm, mem_bot] using hz

private theorem root_inner (m : ℕ) (hm : 0 < m)
    (a : MulAut (SuzukiMatrixGroup m)) (n : ℕ) (hp : a ^ (2 ^ n) = 1)
    (hu : ∀ q ∈ SuzukiRootSubgroup m, a q ∈ SuzukiRootSubgroup m) :
    ∃ q ∈ SuzukiRootSubgroup m, a = MulAut.conj q := by
  let I := (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range
  have hodd : Odd (Nat.card (MulAut (SuzukiMatrixGroup m) ⧸ I)) :=
    suzuki_odd_outer_index m hm
  have he : QuotientGroup.mk' I a = 1 :=
    (hodd.coprime_two_right.pow_right n).pow_left_bijective.injective (by
      rw [← map_pow, hp, map_one, one_pow])
  obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff a).mp he
  have hqp : q ^ (2 ^ n) = 1 := model_pow m hm q _ (hq ▸ hp)
  have hqu : q ∈ normalizer (SuzukiRootSubgroup m : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, hz, rfl⟩
      rw [hq]
      exact hu z hz
    · exact (card_map_of_injective (MulAut.conj q).injective).ge
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  have hc : IsPGroup 2 (zpowers q) := IsPGroup.of_card_dvd_pow (by
    simpa only [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hqp)
  have hmem : q ∈ zpowers q ⊓ normalizer (S : Set _) := ⟨mem_zpowers q, by
    change q ∈ normalizer (↑(S : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
    rwa [hS]⟩
  rw [hc.inf_normalizer_sylow S, hS] at hmem
  exact ⟨q, hmem.2, hq.symm⟩

/-- A two-actor preserving a covered root group is induced by an element of that group.
Square-one actors can be represented by genuine square-one lifts. -/
theorem cover_actor {G : Type*} [Group G] (R K : Subgroup G)
    (hR : IsPGroup 2 R) (m : ℕ) (hm : 0 < m)
    (f : PerfectCentralCovering.Cover K (SuzukiMatrixGroup m))
    (hk : f.toMonoidHom.ker = center K)
    (hpre : (SuzukiRootSubgroup m).comap f.toMonoidHom = R.subgroupOf K)
    (hlift : ∀ q : SuzukiMatrixGroup m, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ f.toMonoidHom k = q)
    (x : G) (hx : x ∈ R) (hn : x ∈ normalizer (K : Set G)) :
    ∃ k : K, (k : G) ∈ R ∧ K.normalizerMonoidHom ⟨x, hn⟩ = MulAut.conj k ∧
      (x ^ 2 = 1 → k ^ 2 = 1) := by
  classical
  let a := K.normalizerMonoidHom ⟨x, hn⟩
  let b := f.autMap hk a
  obtain ⟨n, hnR⟩ := hR.exists_pow_pow_eq_one ⟨x, hx⟩
  have hxn : x ^ (2 ^ n) = 1 := congrArg Subtype.val hnR
  have han : a ^ (2 ^ n) = 1 := by
    change (K.normalizerMonoidHom ⟨x, hn⟩) ^ (2 ^ n) = 1
    rw [← map_pow, show (⟨x, hn⟩ : normalizer (K : Set G)) ^ (2 ^ n) = 1 from
      Subtype.ext hxn, map_one]
  have hbn : b ^ (2 ^ n) = 1 := by
    change (f.autMap hk a) ^ (2 ^ n) = 1
    rw [← map_pow, han, map_one]
  have hbu : ∀ q ∈ SuzukiRootSubgroup m, b q ∈ SuzukiRootSubgroup m := by
    intro q hq
    obtain ⟨k, rfl⟩ := f.surjective q
    have hkr : (k : G) ∈ R := by
      change k ∈ R.subgroupOf K
      rw [← hpre]
      exact hq
    rw [show b (f.toMonoidHom k) = f.toMonoidHom (a k) from f.autMap_apply hk a k]
    change a k ∈ (SuzukiRootSubgroup m).comap f.toMonoidHom
    rw [hpre]
    exact R.mul_mem (R.mul_mem hx hkr) (R.inv_mem hx)
  obtain ⟨q, hq, hbq⟩ := root_inner m hm b n hbn hbu
  have hl : ∃ k : K, f.toMonoidHom k = q ∧ (x ^ 2 = 1 → k ^ 2 = 1) := by
    by_cases hx2 : x ^ 2 = 1
    · have ha2 : a ^ 2 = 1 := by
        change (K.normalizerMonoidHom ⟨x, hn⟩) ^ 2 = 1
        rw [← map_pow, show (⟨x, hn⟩ : normalizer (K : Set G)) ^ 2 = 1 from
          Subtype.ext hx2, map_one]
      have hq2 : q ^ 2 = 1 := model_pow m hm q 2 (by
        rw [← hbq]
        change (f.autMap hk a) ^ 2 = 1
        rw [← map_pow, ha2, map_one])
      obtain ⟨k, hk2, hfk⟩ := hlift q hq2
      exact ⟨k, hfk, fun _ => hk2⟩
    · obtain ⟨k, hfk⟩ := f.surjective q
      exact ⟨k, hfk, fun h => (hx2 h).elim⟩
  obtain ⟨k, hfk, hk2⟩ := hl
  refine ⟨k, ?_, ?_, hk2⟩
  · change k ∈ R.subgroupOf K
    rw [← hpre]
    change f.toMonoidHom k ∈ SuzukiRootSubgroup m
    rwa [hfk]
  · apply f.autMap_injective hk
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := f.surjective y
    change b (f.toMonoidHom z) = f.autMap hk (MulAut.conj k) (f.toMonoidHom z)
    rw [hbq, f.autMap_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, hfk]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair.KernelAction
