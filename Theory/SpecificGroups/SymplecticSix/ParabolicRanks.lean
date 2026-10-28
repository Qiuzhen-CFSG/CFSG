module

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Theory.SpecificGroups.SymplecticSix.FixedRadical
public import Theory.SpecificGroups.SymplecticSix.ParabolicRanks.FixedVectors
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder.PairRecurrence
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.Data.Fintype.Perm

/-!
# Three-ranks of isotropic stabilizers in binary symplectic six-space

A three-subgroup preserving an isotropic space of dimension one or three
fixes a nonzero vector, since that space has respectively one or seven
nonzero vectors. Removing a fixed hyperbolic plane embeds it in Sp₄(2).
For an isotropic plane, the action image has three-part at most three,
and its kernel fixes two independent orthogonal vectors, so embeds in Sp₂(2).
Thus every three-subgroup of each full stabilizer has order at most nine.

This proves the three-rank input for Aschbacher–Smith, Theorem 0.1.2(2),
printed p.4, repeated as Theorem 0.1.1(2), printed p.482, in
`refs/quasithin.pdf`. It uses the actual matrix action throughout.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticSix
namespace ParabolicRanks

local notation "𝔽" => ZMod 2

private def restriction (W : Submodule 𝔽 (Vector 𝔽)) :
    stabilizer W →* (W ≃ₗ[𝔽] W) where
  toFun g := (toLinear g.val).ofSubmodules W W g.property
  map_one' := by
    ext x : 1
    apply Subtype.ext
    change (1 : Sp 𝔽) • x.val = x.val
    exact one_smul _ _
  map_mul' g h := by
    ext x : 1
    apply Subtype.ext
    change (g.val * h.val) • x.val = g.val • (h.val • x.val)
    exact mul_smul _ _ _

private def permutation (W : Submodule 𝔽 (Vector 𝔽)) :
    stabilizer W →* Equiv.Perm W where
  toFun g := (restriction W g).toEquiv
  map_one' := by
    ext x : 1
    exact congrArg (fun f : W ≃ₗ[𝔽] W => f x) ((restriction W).map_one)
  map_mul' g h := by
    ext x : 1
    exact congrArg (fun f : W ≃ₗ[𝔽] W => f x) ((restriction W).map_mul g h)

private theorem three_card_le_of_dvd {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) {m k : ℕ} (hd : Nat.card G ∣ m) (hm : ¬ 3 ^ (k + 1) ∣ m) :
    Nat.card G ≤ 3 ^ k := by
  obtain ⟨a, ha⟩ := hG.exists_card_eq
  rw [ha]
  apply Nat.pow_le_pow_right (by decide : 0 < 3)
  by_contra! h
  exact hm ((pow_dvd_pow 3 (by omega : k + 1 ≤ a)).trans (ha ▸ hd))

private theorem card_sp_four : Nat.card (Matrix.symplecticGroup (Fin 2) 𝔽) = 720 := by
  rw [SymplecticFour.AmbientOrderProof.card_sp_succ (n := 1),
    SymplecticFour.AmbientOrderProof.card_sp_succ (n := 0)]
  have hzero : Nat.card (Matrix.symplecticGroup (Fin 0) 𝔽) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  norm_num [Nat.card_zmod, hzero]

private theorem card_sp_two : Nat.card (Matrix.symplecticGroup (Fin 1) 𝔽) = 6 := by
  rw [SymplecticFour.AmbientOrderProof.card_sp_succ (n := 0)]
  have hzero : Nat.card (Matrix.symplecticGroup (Fin 0) 𝔽) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  norm_num [Nat.card_zmod, hzero]

private theorem nonzero_card (W : Submodule 𝔽 (Vector 𝔽)) :
    Nat.card {v : W // v ≠ 0} = 2 ^ Module.finrank 𝔽 W - 1 := by
  classical
  let := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card W = 2 ^ Module.finrank 𝔽 W := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝔽), Nat.card_zmod]
  rw [hc, Fintype.card_unique]

private theorem card_le_of_odd_dim (W : Submodule 𝔽 (Vector 𝔽))
    (hdim : Module.finrank 𝔽 W = 1 ∨ Module.finrank 𝔽 W = 3)
    (P : Subgroup (stabilizer W)) (hP : IsPGroup 3 P) : Nat.card P ≤ 9 := by
  let ρ : P →* Sp 𝔽 := (stabilizer W).subtype.comp P.subtype
  have hρ : Function.Injective ρ := (stabilizer W).subtype_injective.comp P.subtype_injective
  let X := {v : W // v ≠ 0}
  let : MulAction P X := {
    smul g v := ⟨restriction W g.val v.val, fun h => v.property
      ((restriction W g.val).injective (h.trans (map_zero _).symm))⟩
    one_smul v := by
      apply Subtype.ext
      change restriction W 1 v.val = v.val
      rw [map_one]; rfl
    mul_smul g h v := by
      apply Subtype.ext
      change restriction W (g.val * h.val) v.val = restriction W g.val (restriction W h.val v.val)
      rw [map_mul]; rfl }
  have hc : ¬ 3 ∣ Nat.card X := by
    change ¬ 3 ∣ Nat.card {v : W // v ≠ 0}
    rw [nonzero_card]
    rcases hdim with h | h <;> rw [h] <;> norm_num
  obtain ⟨v, hv⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card X hc
  have hv0 : v.val.val ≠ 0 := fun h => v.property (Subtype.ext h)
  have hfix (g : P) : ρ g • v.val.val = v.val.val :=
    congrArg (fun x : X => x.val.val) (hv g)
  have hd := FixedVectors.card_dvd_of_fixed_vector hP ρ hρ v.val.val hv0 hfix
  rw [card_sp_four] at hd
  exact three_card_le_of_dvd hP hd (by decide : ¬ 3 ^ (2 + 1) ∣ 720)

private theorem card_le_of_plane (W : Submodule 𝔽 (Vector 𝔽))
    (hdim : Module.finrank 𝔽 W = 2)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, form 𝔽 x y = 0)
    (P : Subgroup (stabilizer W)) (hP : IsPGroup 3 P) : Nat.card P ≤ 9 := by
  let χ : P →* Equiv.Perm W := (permutation W).comp P.subtype
  let ρ : P →* Sp 𝔽 := (stabilizer W).subtype.comp P.subtype
  have hρ : Function.Injective ρ := (stabilizer W).subtype_injective.comp P.subtype_injective
  have hW : W ≠ ⊥ := by
    intro h
    have hz := Submodule.finrank_eq_zero.mpr h
    omega
  obtain ⟨v, hvW, hv⟩ := W.ne_bot_iff.mp hW
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, w ∉ Submodule.span 𝔽 {v} := by
    by_contra! h
    have hle : W ≤ Submodule.span 𝔽 {v} := h
    have h := Submodule.finrank_mono hle
    rw [hdim, finrank_span_singleton hv] at h
    omega
  let ψ : χ.ker →* Sp 𝔽 := ρ.comp χ.ker.subtype
  have hψ : Function.Injective ψ := hρ.comp χ.ker.subtype_injective
  have hfix (x : Vector 𝔽) (hx : x ∈ W) (g : χ.ker) : ψ g • x = x := by
    have h := Equiv.congr_fun (show χ g.val = 1 from g.property) (⟨x, hx⟩ : W)
    exact congrArg Subtype.val h
  have hk := FixedVectors.card_dvd_of_fixed_isotropic_pair (n := 1)
    (hP.to_subgroup χ.ker) ψ hψ v w hv hw (hiso v hvW w hwW) (hfix v hvW) (hfix w hwW)
  rw [card_sp_two] at hk
  have hk3 : Nat.card χ.ker ≤ 3 :=
    three_card_le_of_dvd (hP.to_subgroup χ.ker) hk (by decide : ¬ 3 ^ (1 + 1) ∣ 6)
  have hcW : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := 𝔽), Nat.card_zmod, hdim]
    norm_num
  have hcPerm : Nat.card (Equiv.Perm W) = 24 := by
    classical
    let := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hcW]
    rfl
  have hi : Nat.card χ.range ∣ 24 := hcPerm ▸ χ.range.card_subgroup_dvd_card
  have hi3 : Nat.card χ.range ≤ 3 :=
    three_card_le_of_dvd (hP.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective) hi
      (by decide : ¬ 3 ^ (1 + 1) ∣ 24)
  have he := χ.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  calc
    Nat.card P = Nat.card χ.ker * Nat.card χ.range := he.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hk3 hi3
    _ = 9 := rfl

end ParabolicRanks

/-- Every full stabilizer of a nonzero totally isotropic subspace in the
actual binary symplectic six-space has three-rank at most two. -/
public theorem stabilizer_threeRank_le_two
    (W : Submodule (ZMod 2) (Vector (ZMod 2))) (hW : W ≠ ⊥)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) :
    primeRank 3 (stabilizer W) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le (stabilizer W)).mpr
  intro P hP
  let : IsElementaryAbelian 3 P := hP
  have hp := IsElementaryAbelian.isPGroup 3 P
  have hd := TwoLocalCover.finrank_le_three_of_isotropic W hiso
  have hpos : Module.finrank (ZMod 2) W ≠ 0 := fun h => hW (Submodule.finrank_eq_zero.mp h)
  by_cases htwo : Module.finrank (ZMod 2) W = 2
  · exact ParabolicRanks.card_le_of_plane W htwo hiso P hp
  · exact ParabolicRanks.card_le_of_odd_dim W (by omega) P hp

end Theory.SpecificGroups.SymplecticSix
