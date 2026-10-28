module

public import Stellmacher.PushingUp.SL2TwoNaturalSylow

/-!
# Distinct Sylow fixed lines generate the natural SL₂(2) module

For an elementary abelian group carrying the natural two-dimensional action
through a specified identification of its actor with `SL₂(2)`, the fixed
subgroups of any two distinct Sylow 2-subgroups generate the whole module.
The coordinate equivalence in `IsNaturalSL2TwoActionAlong` is kept throughout,
so the result applies to the given action instance.

Each Sylow subgroup has order two and hence a unique nonidentity involution.
Distinct Sylows give distinct involutions. A kernel-checked calculation in
`SL₂(2)` decomposes every coordinate vector as a sum of vectors fixed by the
two involutions. Equivariance transports these summands to the required fixed
subgroups, where their product is the original group element.

This is the natural-module fixed-line generation used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), (3.3), specialized to `p = 2`, `n = 1`.
-/

namespace Stellmacher.PushingUp

universe u v

private theorem sl2Two_distinct_involutions_fixed_decomposition
    (A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hA : A ≠ 1) (hA2 : A ^ 2 = 1)
    (hB : B ≠ 1) (hB2 : B ^ 2 = 1) (hAB : A ≠ B)
    (z : Fin 2 → ZMod 2) :
    ∃ x y : Fin 2 → ZMod 2,
      Matrix.mulVec A.1 x = x ∧ Matrix.mulVec B.1 y = y ∧ z = x + y := by
  set_option synthInstance.maxSize 5000 in
    decide +revert +kernel

private theorem sylow_generator
    {G : Type u} [Group G] [Finite G] (P : Sylow 2 G)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ g : G, g ∈ P ↔ g = 1 ∨ g = t := by
  have hcard : Nat.card P = 2 := by
    have hGcard : Nat.card G = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨eG⟩
    rw [P.card_eq_multiplicity, hGcard]
    norm_num [Nat.factorization_mul (by decide : 3 ≠ 0) (by decide : 2 ≠ 0),
      show 6 = 3 * 2 from rfl, Nat.prime_two.factorization, Nat.prime_three.factorization]
  obtain ⟨t, ht, hall⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hcard
  have htG : (t : G) ≠ 1 := by
    intro h
    exact ht (Subtype.ext h)
  have ht2 : t * t = 1 := by
    by_contra h
    have heq := hall (t * t) h
    have : t = 1 := mul_right_cancel (heq.trans (one_mul t).symm)
    exact ht this
  refine ⟨t, htG, ?_, ?_⟩
  · simpa [pow_two] using congrArg Subtype.val ht2
  · intro g
    constructor
    · intro hg
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · exact Or.inr (congrArg Subtype.val (hall ⟨g, hg⟩ (by
          intro h
          exact hg1 (congrArg Subtype.val h))))
    · rintro (rfl | rfl)
      · exact P.one_mem
      · exact t.property

/-- The fixed subgroups of distinct Sylow 2-subgroups generate a natural
`SL₂(2)` module, for its specified action and group identification. -/
public theorem fixedPoints_sup_eq_top_of_distinct_sylow_naturalSL2Two
    {G : Type u} {W : Type v}
    [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (P Q : Sylow 2 G) (hPQ : P ≠ Q)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong W eG) :
    FixedPoints.subgroup (P : Subgroup G) W ⊔
      FixedPoints.subgroup (Q : Subgroup G) W = ⊤ := by
  obtain ⟨a, ha, ha2, hP⟩ := sylow_generator P eG
  obtain ⟨b, hb, hb2, hQ⟩ := sylow_generator Q eG
  have hab : a ≠ b := by
    intro heq
    apply hPQ
    apply Sylow.ext
    apply Subgroup.ext
    intro g
    change g ∈ P ↔ g ∈ Q
    rw [hP, hQ, heq]
  have hea : eG a ≠ 1 := by simpa using ha
  have heb : eG b ≠ 1 := by simpa using hb
  have hea2 : eG a ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have heb2 : eG b ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have heab : eG a ≠ eG b := fun h => hab (eG.injective h)
  obtain ⟨eW, heW⟩ := hNat
  apply top_unique
  intro w _
  obtain ⟨x, y, hx, hy, hxy⟩ := sl2Two_distinct_involutions_fixed_decomposition
    (eG a) (eG b) hea hea2 heb heb2 heab (eW (Additive.ofMul w))
  let wx : W := Additive.toMul (eW.symm x)
  let wy : W := Additive.toMul (eW.symm y)
  have hfixed (R : Sylow 2 G) (t : G)
      (hR : ∀ g : G, g ∈ R ↔ g = 1 ∨ g = t)
      (z : Fin 2 → ZMod 2) (hz : Matrix.mulVec (eG t).1 z = z) :
      Additive.toMul (eW.symm z) ∈ FixedPoints.subgroup (R : Subgroup G) W := by
    change ∀ g : (R : Subgroup G), g • Additive.toMul (eW.symm z) = _
    intro g
    rcases (hR g).mp g.property with hg | hg
    · change (g : G) • Additive.toMul (eW.symm z) = _
      rw [hg, one_smul]
    · change (g : G) • Additive.toMul (eW.symm z) = _
      rw [hg]
      apply Additive.ofMul.injective
      apply eW.injective
      rw [heW]
      simpa using hz
  have hw : w = wx * wy := by
    apply Additive.ofMul.injective
    apply eW.injective
    change eW (Additive.ofMul w) = eW (eW.symm x + eW.symm y)
    simpa using hxy
  rw [hw]
  exact Subgroup.mul_mem_sup (hfixed P a hP x hx) (hfixed Q b hQ y hy)

end Stellmacher.PushingUp
