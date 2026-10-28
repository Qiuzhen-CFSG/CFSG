module

public import Theory.Representation.HexacodeAction.NoTransvections
public import Theory.Representation.HexacodeAction.FullWeightVectorStabilizer
public import Theory.Representation.HexacodeAction.ProjectiveLineNormalizer

/-!
# A large fixed subspace contains a full-weight word

An odd actor fixes at most three binary dimensions: its fixed space is
 disjoint from its cubic scalar image. An even actor fixing four dimensions
 lies in the elementary pointwise stabilizer of its scalar hyperplane.
 Every even involution is conjugate to one in an actual full-weight vector
 stabilizer A5, so its fixed four-space contains a full-weight word.

Source: Aschbacher–Smith, 12.7.10(2), using K.1.3 and B.4.5.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode

private theorem image_ne_one {x : HexEvenAutomorphisms}
    (hx : x ^ 2 = 1) (hne : x ≠ 1) : hexEvenCoordinate x ≠ 1 := by
  intro he
  apply hne
  exact hexEvenCoordinate.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (le_of_eq even_kernel_eq_center) (by rw [hexEven_kernel_card]; decide)
    (he.trans (map_one _).symm) hx (one_pow _)

private theorem involution_conjugate {x y : HexEvenAutomorphisms}
    (hx : x ^ 2 = 1) (hne : x ≠ 1) (hy : y ^ 2 = 1) (hyne : y ≠ 1) :
    IsConj x y := by
  have ho (y : HexEvenAutomorphisms) (hy : y ^ 2 = 1) (hyne : y ≠ 1) :
      orderOf (hexEvenCoordinate y) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hy, map_one]) (image_ne_one hy hyne)
  have hxct := alternatingGroup.involution_cycleType_of_degree_le_six (by decide)
    (hexEvenCoordinate x) (ho x hx hne)
  have htct := alternatingGroup.involution_cycleType_of_degree_le_six (by decide)
    (hexEvenCoordinate y) (ho y hy hyne)
  have hc : IsConj (hexEvenCoordinate x) (hexEvenCoordinate y) := by
    apply alternatingGroup.isConj_of
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hxct.trans htct.symm))
    rw [← Equiv.Perm.sum_cycleType, hxct]
    decide
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  obtain ⟨g, rfl⟩ := hexEvenCoordinate_surjective c
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  apply hexEvenCoordinate.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (le_of_eq even_kernel_eq_center) (by rw [hexEven_kernel_card]; decide) _ _ hy
  · simpa only [map_mul, map_inv] using hc
  · rw [conj_pow, hx, mul_one, mul_inv_cancel]

/-- Odd actors cannot fix more than half the binary hexacode. -/
theorem odd_fixedSpace_finrank_le_three (g : HexAutomorphisms)
    (hg : hexSign g = -1) :
    Module.finrank Bit (fixedSpace action (zpowers g)) ≤ 3 := by
  let W := fixedSpace action (zpowers g)
  have hd : Disjoint W (W.map (action hexZ)) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hv.2
    have hwf := (mem_fixedSpace_zpowers_iff action g w).mp hw
    have hvf := (mem_fixedSpace_zpowers_iff action g (action hexZ w)).mp hv.1
    rw [scalar_eq_omega_smul] at hvf
    have hz := ThompsonOffenders.eq_zero_of_odd_fixes_scalar g hg w hwf hvf
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  have hh := Submodule.finrank_add_finrank_le_of_disjoint hd
  have he : Module.finrank Bit (W.map (action hexZ)) = Module.finrank Bit W :=
    (hexAction hexZ).finrank_map_eq W
  rw [hexacode_finrank] at hh
  change Module.finrank Bit W + Module.finrank Bit (W.map (action hexZ)) ≤ 6 at hh
  rw [he] at hh
  change Module.finrank Bit W ≤ 3
  omega

/-- Every even involution fixes a word in the actual full-weight orbit. -/
theorem involution_fixes_full_weight (x : HexEvenAutomorphisms)
    (hx : x ^ 2 = 1) (hxne : x ≠ 1) :
    ∃ v : hexacode, evenAction x v = v ∧ hammingNorm v.val = 6 := by
  have hv : fullWeightWord ≠ 0 := by decide
  have hw : hammingNorm fullWeightWord.val = 6 := by decide
  have heven : 2 ∣ (Set.range fun g : HexEvenAutomorphisms =>
      evenAction g fullWeightWord).ncard := by
    rw [evenAction_orbit_card fullWeightWord hv]
    norm_num [hw]
  have hP := evenAction_full_weight_point_of_even_orbit fullWeightWord hv heven
  have hc := fullWeightVectorStabilizer_card fullWeightWord hv hP
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := fullWeightVectorStabilizer fullWeightWord) 2 (by rw [hc]; decide)
  have hy2 : y.val ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one y
    rw [hy] at hh
    exact congrArg Subtype.val hh
  have hyne : y.val ≠ 1 := by
    intro he
    have : y = 1 := Subtype.ext he
    simp [this] at hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_conjugate hy2 hyne hx hxne)
  refine ⟨evenAction g fullWeightWord, ?_, (evenAction_weight g _).trans hw⟩
  rw [← hg]
  change evenAction (g * y.val * g⁻¹) (evenAction g fullWeightWord) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right,
    map_mul, Module.End.mul_apply, y.property]

/-- The literal full group cannot fix a binary four-space without fixing
 a full-weight word in that same space. -/
theorem full_weight_mem_of_large_fixed_subspace (g : HexAutomorphisms) (hg : g ≠ 1)
    (W : Submodule Bit hexacode) (hd : 4 ≤ Module.finrank Bit W)
    (hfix : ∀ w ∈ W, action g w = w) :
    ∃ w ∈ W, hammingNorm (w : HexWord) = 6 := by
  have hWF : W ≤ fixedSpace action (zpowers g) := by
    intro w hw
    exact (mem_fixedSpace_zpowers_iff action g w).mpr (hfix w hw)
  have he : hexSign g = 1 := by
    rcases Int.units_eq_one_or (hexSign g) with h | h
    · exact h
    · have hh := (Submodule.finrank_mono hWF).trans (odd_fixedSpace_finrank_le_three g h)
      omega
  let x : HexEvenAutomorphisms := ⟨g, he⟩
  have hx : x ≠ 1 := fun h => hg (congrArg Subtype.val h)
  have hz : zpowers x ≠ ⊥ := by
    intro h
    exact hx (mem_bot.mp (h ▸ mem_zpowers x))
  have hsame : fixedSpace evenAction (zpowers x) = fixedSpace action (zpowers g) := by
    change fixedSpace (action.comp hexSign.ker.subtype) _ = _
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    rfl
  have hdF : Module.finrank Bit (fixedSpace evenAction (zpowers x)) = 4 := by
    have hlo := Submodule.finrank_mono hWF
    have hsum := fixedCodim_add_finrank evenAction (zpowers x)
    have hcd := ThompsonOffenders.fixedCodim_ge_two (zpowers x) hz
    rw [hexacode_finrank] at hsum
    change fixedCodim evenAction (zpowers x) +
      Module.finrank Bit (fixedSpace evenAction (zpowers x)) = 6 at hsum
    rw [← hsame] at hlo
    omega
  have hs := ThompsonOffenders.fixedSpace_scalar_stable (zpowers x)
  let I := subspaceKernel evenAction (fixedSpace evenAction (zpowers x)) ⊤
  let : IsElementaryAbelian 2 I := ThompsonOffenders.planeKernel_elementary _ hs hdF
  have hxI : x ∈ I := ⟨mem_top x, fun v hv =>
    (mem_fixedSpace_zpowers_iff evenAction x v).mp hv⟩
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxI
  obtain ⟨w, hw, hweight⟩ := involution_fixes_full_weight x hx2 hx
  have hWeq : W = fixedSpace evenAction (zpowers x) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact hWF.trans_eq hsame.symm
    · have hh := Submodule.finrank_mono hWF
      rw [← hsame, hdF] at hh
      omega
  refine ⟨w, ?_, hweight⟩
  rw [hWeq]
  exact (mem_fixedSpace_zpowers_iff evenAction x w).mpr hw

end Representation.Hexacode
