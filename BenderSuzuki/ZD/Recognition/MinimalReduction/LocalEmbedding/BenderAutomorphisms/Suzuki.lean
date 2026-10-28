module

public import BenderSuzuki.SE.Models
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupAction.AutomorphismOddOuter
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Involutory Suzuki automorphisms and their fixed four-groups

Let `B = Sz(2^(2m+1))`, with `m ≥ 1`. Every element whose square is one
lies in a conjugate of the standard root group. Two independent central root
elements give an elementary four in its centralizer. Since `B` is centerless,
an inner automorphism whose square is one is induced by such an element.

The full outer automorphism group has odd order, so every automorphism whose
square is one is inner. Combining these facts proves that every such
automorphism fixes an elementary four, including the identity automorphism.
The outer-index theorem applies to arbitrary automorphisms through the proved
inner-field decomposition; no automorphism-classification premise remains.

Source: GLS, Volume 4, Chapter 4, Lemmas 3.1(b), 3.4(b,c), and the application
in Chapter 2, Proposition 4.4. Root coordinates come from Huppert--Blackburn III, XI.3.1;
the additive field embeds by `c ↦ SuzukiRootGL m 0 c`.
-/

namespace BenderSuzuki.ZD
open _root_.BenderSuzuki.MatrixGroups PFAppendixIII PFchapter1section1

private theorem root_centralizer_four (m : ℕ) (hm : 1 ≤ m)
    (x : SuzukiMatrixGroup m) (hx : x ∈ SuzukiRootSubgroup m) :
    TwoRankAtLeastTwo (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ z, pi z = z ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def _ 2 (m + 1)
  obtain ⟨_, _, _, _, _, _, _, _, hmul, _⟩ :=
    External.huppert_blackburn_XI_3_1 m (by omega) pi
      (External.binaryGaloisField_tits_formula_sq m pi hpi)
  let z (c : K) : SuzukiMatrixGroup m :=
    ⟨SuzukiRootGL m 0 c, Subgroup.subset_closure (Or.inl ⟨0, c, rfl⟩)⟩
  have hz0 : z 0 = 1 := Subtype.ext (External.suzukiRootGL_zero_zero m)
  have hzm (c d : K) : z (c + d) = z c * z d := by
    apply Subtype.ext
    change SuzukiRootGL m 0 (c + d) = SuzukiRootGL m 0 c * SuzukiRootGL m 0 d
    rw [hmul]
    simp
  have hzc (c : K) : z c ∈ Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m)) := by
    obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m x).mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change SuzukiRootGL m 0 c * x.val = x.val * SuzukiRootGL m 0 c
    rw [hab, hmul, hmul]
    simp [add_comm]
  let f : Multiplicative K →*
      Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m)) :=
    { toFun := fun c => ⟨z c.toAdd, hzc c.toAdd⟩
      map_one' := Subtype.ext hz0
      map_mul' := fun c d => Subtype.ext (hzm c.toAdd d.toAdd) }
  have hf : Function.Injective f := by
    intro c d h
    have heq : SuzukiRootGL m 0 c.toAdd = SuzukiRootGL m 0 d.toAdd :=
      congrArg (fun u => u.val.val) h
    have h02 := congrArg
      (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 2) heq
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h02
  have hsq (c : Multiplicative K) : c ^ 2 = 1 := by
    rw [pow_two]
    change Multiplicative.ofAdd (c.toAdd + c.toAdd) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  have hp : IsPGroup 2 (Multiplicative K) := by
    intro c
    exact ⟨1, by simpa using hsq c⟩
  have hcard : 2 ^ 2 ≤ Nat.card (Multiplicative K) := by
    change 2 ^ 2 ≤ Nat.card K
    rw [show Nat.card K = 2 ^ (2 * m + 1) from
      GaloisField.card 2 (2 * m + 1) (by omega)]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  obtain ⟨E, hE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hp hcard
  have hrank : TwoRankAtLeastTwo (Multiplicative K) := by
    refine ⟨E, by simpa using hE, ?_⟩
    intro c
    exact Subtype.ext (hsq c.val)
  exact hrank.map_of_injective f hf

/-- Every element squaring to one in the nondegenerate Suzuki group centralizes a four. -/
public theorem suzuki_centralizer_twoRank_of_sq_eq_one (m : ℕ) (hm : 1 ≤ m)
    (b : SuzukiMatrixGroup m) (hb : b ^ 2 = 1) :
    TwoRankAtLeastTwo (Subgroup.centralizer ({b} : Set (SuzukiMatrixGroup m))) := by
  have hp : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P Q
  have hbQ := hQ (Subgroup.mem_zpowers b)
  rw [← hg] at hbQ
  obtain ⟨x, hx, hxb⟩ := hbQ
  rw [hP] at hx
  have hrank := root_centralizer_four m hm x hx
  rw [← MulAut.fixedSubgroup_conj] at hrank ⊢
  have ht := hrank.map_of_injective
    (MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)).toMonoidHom
    (MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)).injective
  change MulAut.conj g x = b at hxb
  rw [MulAut.congr_conj, hxb] at ht
  exact ht

/-- Centerlessness lifts the square-one condition from an inner automorphism. -/
public theorem suzuki_conj_sq_eq_one (m : ℕ) (hm : 1 ≤ m)
    (b : SuzukiMatrixGroup m) (hb : (MulAut.conj b) ^ 2 = 1) : b ^ 2 = 1 := by
  have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  have hcenter : Subgroup.center (SuzukiMatrixGroup m) = ⊥ := by
    rcases (inferInstance : (Subgroup.center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hmodel.not_commutative (fun x y => by
        have hx : x ∈ Subgroup.center (SuzukiMatrixGroup m) := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.mp hx y).symm))
  have hmem : b ^ 2 ∈ Subgroup.center (SuzukiMatrixGroup m) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hc : MulAut.conj (b ^ 2) = 1 := by rw [map_pow]; exact hb
    have hx := DFunLike.congr_fun hc x
    change b ^ 2 * x * (b ^ 2)⁻¹ = x at hx
    exact ((mul_inv_eq_iff_eq_mul).mp hx).symm
  simpa [hcenter] using hmem

/-- The actual fixed subgroup of an inner square-one Suzuki automorphism contains a four. -/
public theorem suzuki_fixedSubgroup_twoRank_of_inner (m : ℕ) (hm : 1 ≤ m)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : a ^ 2 = 1)
    (hinner : ∃ b, a = MulAut.conj b) : TwoRankAtLeastTwo a.fixedSubgroup := by
  obtain ⟨b, rfl⟩ := hinner
  rw [MulAut.fixedSubgroup_conj]
  exact suzuki_centralizer_twoRank_of_sq_eq_one m hm b (suzuki_conj_sq_eq_one m hm b ha)

/-- The identity case needs no automorphism-classification input. -/
public theorem suzuki_identity_fixedSubgroup_twoRank (m : ℕ) (hm : 1 ≤ m) :
    TwoRankAtLeastTwo (1 : MulAut (SuzukiMatrixGroup m)).fixedSubgroup := by
  exact suzuki_fixedSubgroup_twoRank_of_inner m hm 1 (one_pow 2)
    ⟨1, (map_one MulAut.conj).symm⟩

/-- Conditional assembly through the full outer index. -/
public theorem suzuki_involutoryAut_inner_and_twoRank_of_odd_outer_index
    (m : ℕ) (hm : 1 ≤ m)
    (hodd : Odd (MulAut.conj : SuzukiMatrixGroup m →*
      MulAut (SuzukiMatrixGroup m)).range.index)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : a ^ 2 = 1) :
    ∃ b : SuzukiMatrixGroup m, a = MulAut.conj b ∧
      TwoRankAtLeastTwo a.fixedSubgroup := by
  obtain ⟨b, hb⟩ := MulAut.inner_of_sq_eq_one_of_odd_index hodd a ha
  exact ⟨b, hb, suzuki_fixedSubgroup_twoRank_of_inner m hm a ha ⟨b, hb⟩⟩

/-- The Suzuki case of GLS IV, Chapter 4, Lemma 3.4(b,c): every automorphism
whose square is one is inner and its actual fixed subgroup contains an
elementary four. This includes the identity automorphism, excludes the no-four
case, and implies innerness without a normal-Sylow assumption. -/
public theorem suzuki_involutoryAut_inner_and_twoRank (m : ℕ) (hm : 1 ≤ m)
    (a : MulAut (SuzukiMatrixGroup m)) (ha : a ^ 2 = 1) :
    ∃ b : SuzukiMatrixGroup m, a = MulAut.conj b ∧
      TwoRankAtLeastTwo a.fixedSubgroup :=
  suzuki_involutoryAut_inner_and_twoRank_of_odd_outer_index m hm
    (suzuki_odd_outer_index m hm) a ha

end BenderSuzuki.ZD
