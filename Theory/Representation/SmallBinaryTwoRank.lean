module
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.SmallBinaryPrimeNormalizer
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero

/-!
# Two-rank bounds for small normal binary actors

A fully moved normal symmetric-three actor in a binary four-space embeds its
ambient group in S₃ × S₃. A normal five-group in a binary four-space has odd
centralizer and cyclic automorphism group, so its ambient two-rank is at most
one. The plane case uses GL₂(2) ≅ S₃. These bounds concern the actual ambient
representation and do not infer rank monotonicity for arbitrary quotients.

Source application: Aschbacher–Smith 15.1.7 and 15.1.13, pp.1087 and1091.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.SmallBinaryTwoRank
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem rank_le_two_of_card_dvd_thirty_six (h : Nat.card G ∣ 36) : primeRank 2 G ≤ 2 :=
  primeRank_le_two_of_cube_not_dvd (fun hc => by norm_num at hc ⊢; exact (by decide : ¬8∣36) (hc.trans h))

omit [Finite G] in
theorem card_dvd_six_of_dimension_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2) : Nat.card G ∣ 6 := by
  let b : V ≃ₗ[ZMod 2] BinaryFourPlus.Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) V hdim).equivFun
  let a := LinearMap.GeneralLinearGroup.congrLinearEquiv b
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryFourPlus.Plane
  let f : G →* Equiv.Perm (Fin 3) := BinaryFourPlus.planeAutEquiv.toMonoidHom.comp
    (l.toMonoidHom.comp (a.toMonoidHom.comp ρ.asGroupHom))
  have hfi : Function.Injective f := by
    apply BinaryFourPlus.planeAutEquiv.injective.comp
    apply l.injective.comp
    apply a.injective.comp
    intro x y he
    exact hf (congrArg Units.val he)
  have hd := card_dvd_of_injective f hfi
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  exact h6 ▸ hd


theorem rank_le_one_of_four_not_dvd (h : ¬4 ∣ Nat.card G) : primeRank 2 G ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  let := hA
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    apply h
    have hd : 2 ^ 2 ∣ Nat.card A := hn ▸ pow_dvd_pow 2 (by omega : 2 ≤ n)
    exact hd.trans A.card_subgroup_dvd_card
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

theorem rank_le_one_of_dimension_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2) : primeRank 2 G ≤ 1 := by
  apply rank_le_one_of_four_not_dvd
  intro h4
  exact (by decide : ¬4 ∣ 6) (h4.trans (card_dvd_six_of_dimension_two ρ hf hdim))

theorem rank_le_two_of_dimension_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2) : primeRank 2 G ≤ 2 :=
  (rank_le_one_of_dimension_two ρ hf hdim).trans (by decide)

theorem rank_le_two_of_normal_symmetricThree
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2 ∨ Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* Equiv.Perm (Fin 3))
    (hfull : subspaceCommutator (ρ.comp H.subtype) ⊤ ⊤ = ⊤) :
    primeRank 2 G ≤ 2 := by
  rcases hdim with hdim | hdim
  · exact rank_le_two_of_dimension_two ρ hf hdim
  let σ := ρ.comp (H.subtype.comp j.symm.toMonoidHom)
  have hσ : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((ρ.comp H.subtype).comp j.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ j.symm.surjective]
    exact hfull
  exact rank_le_two_of_card_dvd_thirty_six
    (BinarySymmetricThreeNormalizer.card_dvd_thirty_six ρ hf hdim H j
      (BinarySymmetricThreeNormalizer.fixedFree_of_full σ hσ))

theorem rank_le_one_of_normal_five
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (P : Subgroup G) [P.Normal] (hP : Nat.card P = 5) :
    primeRank 2 G ≤ 1 := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    decide
  have hodd : Odd (Nat.card (centralizer (P : Set G))) :=
    (by decide : Odd 15).of_dvd_nat
      (card_centralizer_five_dvd_fifteen (V := Multiplicative V) P hP hV)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let f : G →* MulAut P := MulAut.conjNormal
  have hk : primeRank 2 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    simpa only [f,MulAut.conjNormal_ker_eq_centralizer] using hodd.not_two_dvd_nat
  let e : MulAut P ≃* (ZMod 5)ˣ := by
    have he := IsCyclic.mulAutMulEquiv P
    rw [hP] at he
    exact he
  let : IsCyclic (MulAut P) := isCyclic_of_injective e.toMonoidHom e.injective
  let Q : Sylow 2 (MulAut P) := Classical.choice inferInstance
  have ha : primeRank 2 (MulAut P) ≤ 1 := Q.primeRank_le_one_of_isCyclic inferInstance
  have hh := primeRank_le_ker_add (p := 2) f
  rw [hk,zero_add] at hh
  exact hh.trans ha
end Representation.SmallBinaryTwoRank
