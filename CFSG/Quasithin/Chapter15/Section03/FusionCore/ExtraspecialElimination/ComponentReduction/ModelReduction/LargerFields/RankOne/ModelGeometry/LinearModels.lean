module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.NormalizerData
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic.RankOne
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups

/-!
# Normalizer data for the two linear models

The standard Sylow normalizers are the upper triangular subgroups. Their
commutators lie in the unitriangular subgroup, and their orders are prime
to three in odd field degree. In even degree, the cube roots of unity
embed diagonally, with one independent parameter in SL₂ and two in SL₃.
In SL₃ this retains the scalar cube roots, including over F₄.

The intrinsic solvable-overgroup results and Sylow conjugacy give all four
facts for an arbitrary supplied Sylow. The SL₃ argument uses the proved
special-linear Borel containment directly, before projectivization.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry

private theorem data_of_standard {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (B : Subgroup G) (hB : normalizer (P : Set G) = B)
    (n r : ℕ)
    (hsol : ∀ H : Subgroup G, Group.IsSolvable H → (P : Subgroup G) ≤ H → H ≤ B)
    (hcomm : ⁅B, B⁆ ≤ P)
    (hodd : Odd n → ¬ 3 ∣ Nat.card B)
    (hrank : Even n → r ≤ primeRank 3 (theta B)) : NormalizerData G n r := by
  have align (S : Sylow 2 G) : ∃ e : G ≃* G,
      (S : Subgroup G).map e.toMonoidHom = P ∧
      (normalizer (S : Set G)).map e.toMonoidHom = B := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
    let e := MulAut.conj g
    have hS : (S : Subgroup G).map e.toMonoidHom = P := congrArg Sylow.toSubgroup hg
    refine ⟨e, hS, ?_⟩
    change (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom = B
    rw [map_equiv_normalizer_eq (S : Subgroup G) e, hS]
    exact hB
  constructor
  · intro S H hs hSH
    obtain ⟨e, hS, hN⟩ := align S
    let : Group.IsSolvable H := hs
    have hs' : Group.IsSolvable (H.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hN]
    exact hsol _ hs' (hS ▸ map_mono hSH)
  · intro S
    obtain ⟨e, hS, hN⟩ := align S
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rwa [map_commutator, hS, hN]
  · intro hn S
    obtain ⟨e, hS, hN⟩ := align S
    have hc : Nat.card (normalizer (S : Set G)) = Nat.card B := by
      rw [← hN, card_map_of_injective e.injective]
    rw [hc]
    exact hodd hn
  · intro hn S
    obtain ⟨e, hS, hN⟩ := align S
    have htheta : (theta (normalizer (S : Set G))).map e.toMonoidHom = theta B := by
      rw [theta_map_of_injective e.toMonoidHom e.injective, hN]
    have he := Theory.GroupTheory.primeRank_equiv 3
      ((e.subgroupMap (theta (normalizer (S : Set G)))).trans
        (MulEquiv.subgroupCongr htheta))
    rw [he]
    exact hrank hn

/-- Every exponent-three subgroup of B is contained in the actual theta(B). -/
private theorem rank_theta_of_embedding {G A : Type*} [Group G] [Finite G]
    [CommGroup A] [Finite A] (B : Subgroup G) (r : ℕ)
    (hp : ∀ a : A, a ^ 3 = 1) (hc : Nat.card A = 3 ^ r)
    (f : A →* G) (hf : Function.Injective f) (hB : ∀ a, f a ∈ B) :
    r ≤ primeRank 3 (theta B) := by
  have hm (a : A) : f a ∈ theta B := by
    by_cases h : f a = 1
    · rw [h]; exact (theta B).one_mem
    · apply Subgroup.subset_closure
      exact ⟨hB a, orderOf_eq_prime_iff.mpr ⟨by rw [← map_pow, hp, map_one], h⟩⟩
  let f' : A →* theta B := f.codRestrict _ hm
  exact primeRank_ge_of_elementary_embedding hp hc f'
    (fun a b h => hf (congrArg Subtype.val h))

private abbrev cubeRoots (F : Type*) [Field F] :=
  (powMonoidHom 3 : Fˣ →* Fˣ).ker

private theorem cubeRoots_pow (F : Type*) [Field F] (a : cubeRoots F) : a ^ 3 = 1 :=
  Subtype.ext a.property

private theorem cubeRoots_card (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) : Nat.card (cubeRoots F) = 3 := by
  rw [cubeRoots, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hF]
  exact Nat.gcd_eq_right ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn)

private def diagonalEntry (F : Type*) [Field F] : rankOneBorel F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (by
    have hd : g.val.val 0 0 * g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, (mem_rankOneBorel_iff _).mp g.property,
        mul_zero, sub_zero] using g.val.property
    exact left_ne_zero_of_mul_eq_one hd)
  map_one' := by ext; rfl
  map_mul' g h := by
    ext
    simp [mul_apply, Fin.sum_univ_two, (mem_rankOneBorel_iff _).mp h.property]

private theorem diagonalEntry_one (F : Type*) [Field F] (g : rankOneBorel F)
    (hg : diagonalEntry F g = 1) : g.val ∈ upperUnipotent F := by
  have h00 : g.val.val 0 0 = 1 := congrArg Units.val hg
  have h10 := (mem_rankOneBorel_iff _).mp g.property
  have h11 : g.val.val 1 1 = 1 := by
    simpa only [det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using g.val.property
  refine (mem_upperUnipotent F _).mpr ⟨g.val.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]

private theorem linearTwo_commutator (F : Type*) [Field F] :
    ⁅rankOneBorel F, rankOneBorel F⁆ ≤ upperUnipotent F := by
  apply commutator_le.mpr
  intro a ha b hb
  let x : rankOneBorel F := ⟨a, ha⟩
  let y : rankOneBorel F := ⟨b, hb⟩
  exact diagonalEntry_one F ⁅x,y⁆ (by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))

private theorem linearTwo_not_solvable (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F), 1, by
      intro h
      have he := congrArg (fun g : SL(2,F) => g.val 0 1) h
      simp [transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _

/-- All four normalizer facts for arbitrary Sylow two-subgroups of SL₂(F). -/
theorem linearTwo_normalizerData (F : Type*) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n) : NormalizerData SL(2,F) n 1 := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  apply data_of_standard (upperUnipotentSylow F 2) (rankOneBorel F) rfl n 1
  · intro H hs hUH
    have hH : H ≠ ⊤ := by
      intro he
      let : Group.IsSolvable H := hs
      have htop : Group.IsSolvable (⊤ : Subgroup SL(2,F)) := he ▸ hs
      let := htop
      exact linearTwo_not_solvable F hfour
        (Group.isSolvable_of_surjective (f := (topEquiv (G := SL(2,F))).toMonoidHom)
          (topEquiv (G := SL(2,F))).surjective)
    exact Theory.SpecificGroups.SymplecticFour.SolvableParabolic.proper_sylow_overgroup
      (upperUnipotentSylow F 2) H hH hUH
  · exact linearTwo_commutator F
  · intro ho
    rw [Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F).toEquiv]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_threePrime_of_odd F hF ho)
  · intro he
    let f : cubeRoots F →* SL(2,F) := (rankOneBorel F).subtype.comp
      (borelDiagonalHom.comp (cubeRoots F).subtype)
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Units.ext
      exact congrArg (fun g : SL(2,F) => g.val 0 0) h
    exact rank_theta_of_embedding (rankOneBorel F) 1 (cubeRoots_pow F)
      (by simpa using cubeRoots_card F hF he) f hf (fun a => (borelDiagonalHom a.val).property)

private theorem commutator_le_of_quotient {G T : Type*} [Group G] [CommGroup T]
    (U B : Subgroup G) [(U.subgroupOf B).Normal] (e : B ⧸ U.subgroupOf B ≃* T) :
    ⁅B, B⁆ ≤ U := by
  have hcomm : IsMulCommutative (B ⧸ U.subgroupOf B) :=
    ⟨⟨fun a b => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  have h := Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hm := map_mono (f := B.subtype) h
  rw [map_subtype_commutator, subgroupOf_map_subtype] at hm
  exact hm.trans inf_le_left

open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions

private theorem linearThree_commutator (F : Type*) [Field F] [Finite F] :
    ⁅borelSL F, borelSL F⁆ ≤ unipotentSL F := by
  let e : (borelSL F ⧸ (unipotentSL F).subgroupOf (borelSL F)) ≃* (Fˣ × Fˣ) :=
    (BorelQuotient.borelSL_complement F).symm.QuotientMulEquiv.trans
      ((subgroupOfEquivOfLe (BorelQuotient.torusSL_le_borel F)).trans
        (BorelQuotient.torusSLEquiv F).symm)
  exact commutator_le_of_quotient _ _ e

private theorem linearThree_borel_card (F : Type*) [Field F] [Finite F] :
    Nat.card (borelSL F) = Nat.card F ^ 3 * (Nat.card F - 1) ^ 2 := by
  rw [← (BorelQuotient.borelSL_complement F).card_mul_card,
    Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (BorelQuotient.torusSL_le_borel F)).toEquiv,
    card_unipotentSL, ← Nat.card_congr (BorelQuotient.torusSLEquiv F).toEquiv,
    Nat.card_prod, Nat.card_units, pow_two]

/-- The SL₃ rank-two witness retains both diagonal parameters and the scalar center. -/
theorem linearThree_normalizerData (F : Type*) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n) : NormalizerData SL(3,F) n 2 := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  apply data_of_standard (BorelQuotient.unipotentSLSylow F (by omega) hF)
    (borelSL F) (normalizer_unipotentSL F) n 2
  · intro H hs hUH
    let := hs
    exact SolvableOvergroups.solvable_le_borelSL F hfour H hUH
  · exact linearThree_commutator F
  · intro ho
    apply Nat.prime_three.coprime_iff_not_dvd.mp
    rw [linearThree_borel_card, hF]
    exact (((by decide : Nat.Coprime 3 2).pow_right n).pow_right 3).mul_right
      ((Nat.BinaryTorusParity.coprime_three_sub_one ho).pow_right 2)
  · intro he
    let f : cubeRoots F × cubeRoots F →* SL(3,F) := (torusSL F).comp
      ((cubeRoots F).subtype.prodMap (cubeRoots F).subtype)
    have hf : Function.Injective f := (BorelQuotient.torusSL_injective F).comp (by
      intro a b h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h)))
    apply rank_theta_of_embedding (borelSL F) 2 (fun a =>
      Prod.ext (cubeRoots_pow F a.1) (cubeRoots_pow F a.2)) ?_ f hf
      (fun a => BorelQuotient.torusSL_mem_borel F _)
    rw [Nat.card_prod, cubeRoots_card F hF he]
    rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
