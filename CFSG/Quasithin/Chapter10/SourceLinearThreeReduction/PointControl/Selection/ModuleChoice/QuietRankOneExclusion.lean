module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietRankOneCartan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorExclusion

/-!
# Excluding the original quiet rank-one tensor

The tensor constructs an original H-star Hall subgroup that is cyclic of
order and exponent 2^n-1, with n at least three. The completed central Hall
theorem applies to this same subgroup and its actual source context. Its
three-group alternative contradicts reduction modulo eight; its signed-torus
alternative contradicts Mersenne divisibility. No new model, field-action or
point-control premise is used. Thus the original full module has nonzero
component-fixed vectors, before invoking crossed movement or point selection.

Source: Aschbacher--Smith 9.2.7, printed pp.731--732, and the quiet exclusion
used in 10.1.1, p.741, refs/quasithin.pdf. The central Hall proof used here
constructs the original H-models independently of point selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

private theorem mersenne_not_three_power {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    2^n-1 ≠ 3^k := by
  intro he
  have hd : 8 ∣ 2^n := by
    simpa using pow_dvd_pow (2 : ℕ) hn
  have hmod : ∀ j : ℕ, 3^j % 8 = 1 ∨ 3^j % 8 = 3 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ,Nat.mul_mod]
      rcases ih with ih | ih <;> simp [ih]
  have hp : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  have he' : 2^n = 3^k+1 := by omega
  have hh := Nat.mod_eq_zero_of_dvd hd
  rw [he',Nat.add_mod] at hh
  rcases hmod k with h | h <;> omega

/-- The genuine quiet tensor contradicts the original Hall subgroup theorem. -/
theorem quiet_rankOne_tensor_false
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (htn : t ∉ normalizer (L : Set G))
    (hm : QuietRankOneSeedMarking D e ht) (hlocal : D.moduleSubgroup = D.seed) : False := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (source_maximalOutside_of_many D hmany)
  obtain ⟨_,_,B,c,_,_,hcard,hexp⟩ :=
    quiet_rankOne_hstar_cyclic_cartan D hmany hmin hnon hna hJ hn htn hm hlocal hH
  rcases original_hall_conclusion D c with hthree | ⟨k,hk⟩
  · obtain ⟨k,hk⟩ := hthree.exists_card_eq
    exact mersenne_not_three_power hn k (hcard.symm.trans hk)
  · rw [hexp] at hk
    have he := Nat.eq_two_of_two_pow_sub_one_dvd_two_pow_add_one (by omega : 2 ≤ n) hk
    omega

/-- Quiet rank-one support is nonzero in the unchanged full module. -/
theorem quiet_rankOne_component_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    D.fullModule ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hfix
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hnon
  obtain ⟨hm,hlocal,_,_⟩ := quiet_rankOne_marking_and_local_equality_of_no_component_fixed
    D hmany hnon hJ n hn e hfix ht htn
  exact quiet_rankOne_tensor_false D hmany hmin hnon hna hJ hn htn hm hlocal


end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
