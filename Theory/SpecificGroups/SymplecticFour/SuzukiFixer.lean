module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The full automorphism fixer of a Suzuki subgroup in odd-degree symplectic four-space

An involution centralizer in Sp₄(F) lies in an actual point or plane
parabolic. If |F| = 2^(2m+1), neither parabolic has order divisible by five:
its successive factors are field units, SL₂(F), and a two-group. Consequently
an inner involutory automorphism cannot fix a subgroup of order divisible
by five pointwise.

Assuming diagram-preserving semilinear coverage, the order of Out(Sp₄(F))
divides 2(2m+1). The kernel of the full fixer map to this outer group has odd
order by the preceding calculation and Cauchy's theorem. Thus four cannot
divide the full fixer order. Every positive-parameter Suzuki group has order
divisible by five, so this applies to every actual embedding, including Sz(8).
No conjugacy classification of Suzuki embeddings is required.

The semilinear coverage premise remains explicit. The source application is
the Sp₄–Suzuki exclusion in Aschbacher–Smith, *The Classification of Quasithin
Groups*, 16.3.5, printed pp.1178–1179, using 16.1.4(7) and 16.1.7(3d),
printed pp.1171–1173 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SuzukiFixer
open DiagramAutomorphisms InvolutionTypes
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem binary_odd_mod_five (m : ℕ) :
    2 ^ (2 * m + 1) % 5 = 2 ∨ 2 ^ (2 * m + 1) % 5 = 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> norm_num [h]

private theorem not_dvd_card_of_hom {G H : Type*} [Group G] [Group H]
    (f : G →* H) {p : ℕ} (hp : p.Prime)
    (hH : ¬ p ∣ Nat.card H) (hker : ¬ p ∣ Nat.card f.ker) :
    ¬ p ∣ Nat.card G := by
  intro h
  rw [← f.ker.card_mul_index, index_ker] at h
  rcases hp.dvd_mul.mp h with h | h
  · exact hker h
  · exact hH (h.trans f.range.card_subgroup_dvd_card)

private theorem plane_five_free (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    ¬ 5 ∣ Nat.card (planeParabolic (F := F)) := by
  let := Fintype.ofFinite F
  have hq := binary_odd_mod_five m
  rw [← hF] at hq
  have hsq : Nat.card F ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  have hle : Nat.card F ≤ Nat.card F ^ 2 := by
    have : 0 < Nat.card F := Nat.card_pos
    nlinarith
  have hu : ¬ 5 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.dvd_iff_mod_eq_zero]
    omega
  have hgl : ¬ 5 ∣ Nat.card (GL (Fin 2) F) := by
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      ← Nat.card_eq_fintype_card]
    intro hd
    rcases (by decide : Nat.Prime 5).dvd_mul.mp hd with hd | hd
    · have := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
    · have := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
  have hsl : ¬ 5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    fun hd => hgl (hd.trans (card_dvd_of_injective _ Matrix.SpecialLinearGroup.toGL_injective))
  have hrad : ¬ 5 ∣ Nat.card (Plane.quotientMap (F := F)).ker := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F))).exists_card_eq
    change ¬ 5 ∣ Nat.card (Plane.radical (F := F))
    rw [hn]
    exact fun hd => (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd)
  have hlocal : ¬ 5 ∣ Nat.card (planeLocal (F := F)) :=
    not_dvd_card_of_hom Plane.quotientMap (by decide) hsl hrad
  apply not_dvd_card_of_hom (determinantCharacter (plane F)) (by decide) hu
  have hk : Nat.card (determinantCharacter (plane F)).ker =
      Nat.card (planeLocal (F := F)) :=
    (card_map_of_injective (stabilizer (plane F)).subtype_injective).symm
  rwa [hk]

theorem parabolic_five_free (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1))
    (P : Subgroup (Sp F)) (hP : IsParabolic P) : ¬ 5 ∣ Nat.card P := by
  obtain ⟨g, h | h⟩ := hP
  · rw [h, card_map_of_injective (MulAut.conj g).injective,
      card_pointParabolic_eq_card_planeParabolic]
    exact plane_five_free m hF
  · rw [h, card_map_of_injective (MulAut.conj g).injective]
    exact plane_five_free m hF

theorem involution_centralizer_five_free (m : ℕ)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (g : Sp F) (hg : orderOf g = 2) :
    ¬ 5 ∣ Nat.card (centralizer ({g} : Set (Sp F))) := by
  obtain ⟨P, hP, _, _, hC⟩ := InvolutionCentralizers.involution_centralizer_parabolic g hg
  exact fun hd => parabolic_five_free m hF P hP (hd.trans (card_dvd_of_le hC))

/-- The full automorphism fixer of any subgroup with order divisible by five
has no subgroup of order four, conditional on semilinear coverage. -/
theorem four_not_dvd_fixer (m : ℕ) (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m + 1))
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup (Sp F)) (hL : 5 ∣ Nat.card L) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (Sp F)) (L : Set (Sp F))) := by
  let K := fixingSubgroup (MulAut (Sp F)) (L : Set (Sp F))
  let f : K →* MulAut.Outer (Sp F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp K.subtype
  have hk : ¬ 2 ∣ Nat.card f.ker := by
    intro hd
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hd
    have ha' : orderOf (a.val.val : MulAut (Sp F)) = 2 := by
      exact (orderOf_injective K.subtype K.subtype_injective a.val).trans
        ((orderOf_injective f.ker.subtype f.ker.subtype_injective a).trans ha)
    have hi : a.val.val ∈ MulAut.innerSubgroup (Sp F) :=
      (QuotientGroup.eq_one_iff _).mp a.property
    obtain ⟨g, hg⟩ := hi
    have hg2 : orderOf g = 2 := by
      rw [← MulAut.conj_orderOf_of_center_eq_bot EvenProjective.center_eq_bot g, hg]
      exact ha'
    have hLC : L ≤ centralizer ({g} : Set (Sp F)) := by
      intro x hx
      have hf : a.val.val x = x := a.val.property ⟨x, hx⟩
      rw [← hg, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hf
      exact mem_centralizer_singleton_iff.mpr hf.symm
    exact involution_centralizer_five_free m hF g hg2
      (hL.trans (card_dvd_of_le hLC))
  have hcop : Nat.Coprime 4 (Nat.card f.ker) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hk).pow_left 2
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < 2 * m + 1)
  intro hd
  change 4 ∣ Nat.card K at hd
  rw [← f.ker.card_mul_index, index_ker] at hd
  have hout := (hcop.dvd_of_dvd_mul_left hd).trans f.range.card_subgroup_dvd_card
  have hbad := hout.trans (card_outer_dvd_two_mul hF hlarge hclass)
  omega

/-- Five divides every positive-parameter Suzuki carrier, including Sz(8). -/
theorem five_dvd_suzuki (m : ℕ) (hm : 1 ≤ m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
  have hsq : (2 ^ (2 * m + 1)) ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases binary_odd_mod_five m with h | h <;> rw [h]
  have hd : 5 ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hsq]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _

/-- This is the full fixer of the actual embedded subgroup, with no
assumption that the embedding is in standard matrix coordinates. -/
theorem four_not_dvd_suzuki_fixer (m : ℕ) (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m + 1))
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup (Sp F))
    (hL : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (Sp F)) (L : Set (Sp F))) := by
  obtain ⟨e⟩ := hL
  apply four_not_dvd_fixer m hm hF hclass L
  rw [Nat.card_congr e.toEquiv]
  exact five_dvd_suzuki m hm

end Theory.SpecificGroups.SymplecticFour.SuzukiFixer
