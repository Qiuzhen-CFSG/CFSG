module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpModels
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree

/-!
# The original alternating-six residual excludes the rank-two Lie rows

Retain the actual residual F inside K and its original moved two-subgroup U.
The restriction of the central quotient to F has solvable kernel, and its
nontrivial two-core image is normalized by the residual image. Every large
linear-Levi row is excluded because A₆ has a two-element of order four.
The Ree row is excluded by three-divisibility. The derived binary symplectic endpoint is embedded in the full symplectic
local geometry. The Tits endpoint is excluded by the actual nonidentity
two-subgroup normalizer, whose order is not divisible by fifteen. No rank bound or additional model callback
is needed in this residual exclusion.
Source: Aschbacher–Smith C.2.8 and C.3.5, printed pp.147–150, applied to the
original doubled A₆ reciprocal component in 12.2.7, printed p.797.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Equiv
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterA.Section02 ClassificationModels
open Chapter4.Section04.NormalizedRankOneOddControl

private def sixQuarterTurn : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5, by simp [Perm.sign_mul]⟩

private theorem six_not_two_exponent :
    ¬ ∀ P : Subgroup (alternatingGroup (Fin 6)), IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro h
  have hp : IsPGroup 2 (zpowers sixQuarterTurn) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_pow (p := 2) (n := 1)
      (by decide +kernel : sixQuarterTurn ^ 2 ^ 1 ≠ 1)
      (by decide +kernel : sixQuarterTurn ^ 2 ^ (1 + 1) = 1))
  have hs : sixQuarterTurn ^ 2 = 1 := congrArg Subtype.val
    (h (zpowers sixQuarterTurn) hp ⟨sixQuarterTurn, mem_zpowers _⟩)
  exact (by decide +kernel : sixQuarterTurn ^ 2 ≠ 1) hs

/-- The literal alternating-six residual and its moved two-subgroup exclude
all relative-rank-two rows in the ordinary Theorem C component catalogue. -/
theorem no_CrankTwo_of_six_residual_module
    {G : Type*} [Group G] [Finite G]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (π : F →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {n : ℕ} (hm : IsTheoremCRankTwoModel (K ⧸ center K) n) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.IsPerfect.ofSurjective hπ
  have hS := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
  have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hd : 360 ∣ Nat.card (K ⧸ center K) := by
    let r := residualQuotientMap hFK (MulEquiv.refl (K ⧸ center K))
    let := residualQuotientMap_kernel_solvable hFK (MulEquiv.refl (K ⧸ center K))
    simpa only [hc] using SimpleSection.card_dvd_of_solvable_representation hS π hπ r
  cases hm with
  | linear hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcard,he] at hd
      norm_num at hd
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_linear_three_local hS six_not_two_exponent π hπ hn2 hcard _ hp hpne r hnorm
  | symplectic hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := E)).symm
    let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm a
    exact no_symplectic_four_local hS six_not_two_exponent π hπ _ hp hpne r hnorm
  | g2 hn hm =>
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hbig : 2 < Nat.card E := by
      rw [hcard]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_g2_local hS six_not_two_exponent π hπ hbig _ hp hpne r hnorm
  | triality hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_triality_local hS six_not_two_exponent π hπ n (show 0 < n from hn) _ hp hpne r hnorm
  | ree_f4 m hm _ he =>
    obtain ⟨e⟩ := he
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_ree_local_of_three_dvd hS six_not_two_exponent (by rw [hc]; decide)
      π hπ hm _ hp hpne r hnorm
  | symplectic_derived _ he =>
    obtain ⟨e⟩ := he
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    let P := (pCore 2 F).map r
    let a := (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv
      (F := ZMod 2)).symm
    let j := a.toMonoidHom.comp (commutator (ClassicalGroup.PSp 2 (ZMod 2))).subtype
    have hj : Function.Injective j := a.injective.comp (Subgroup.subtype_injective _)
    let t := j.comp r
    let : Group.IsSolvable t.ker := by
      change Group.IsSolvable (j.comp r).ker
      rw [MonoidHom.ker_comp_of_injective _ _ hj]
      infer_instance
    have hn : t.range ≤ normalizer (P.map j : Set _) := by
      rw [MonoidHom.range_comp]
      exact (map_mono hnorm).trans (P.le_normalizer_map j)
    exact no_symplectic_four_local hS six_not_two_exponent π hπ (P.map j)
      (hp.map j) (fun he => hpne ((map_eq_bot_iff_of_injective P hj).mp he)) t hn
  | g2_derived _ he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | tits _ he =>
    obtain ⟨e⟩ := he
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    let P := (pCore 2 F).map r
    let k := r.codRestrict (normalizer (P : Set Tits.ParrottGroup))
      (fun x => hnorm ⟨x,rfl⟩)
    let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show k.ker ≤ r.ker from fun _ hx => congrArg Subtype.val hx))
      (inclusion_injective _)
    have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
    apply Tits.normalizer_fifteen_free P hpne hp
    exact (show 15 ∣ Nat.card (alternatingGroup (Fin 6)) by rw [hc]; decide).trans hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
