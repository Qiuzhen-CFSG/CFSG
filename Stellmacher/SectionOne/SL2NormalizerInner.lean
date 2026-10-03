module
public import Stellmacher.SectionOne.SL2ProductNormalizerRigidity
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Mathlib.Data.Fintype.Perm

/-!
# Inner automorphisms of SL₂(2)

Every normalizer of an SL₂(2) subgroup differs from an element of that
subgroup by an element of its centralizer. Its automorphism group acts
faithfully on the three nontrivial involutions, since every element is a
product of two involutions. Thus it has at most six elements. Centerlessness
makes inner conjugation injective, and the group itself has six elements,
so every automorphism is inner.

This is the elementary group-side normalizer fact used in the odd-core and
Baumann factorizations of Stellmacher (1.7), journal p.19 of
`refs/latex/stellmacher-n-group.tex`. The only finite computation counts
the three involutions of the concrete SL₂(2) group.
-/

namespace Stellmacher.SectionOne
universe u

private def involutionPerm {H : Type u} [Group H] :
    MulAut H →* Equiv.Perm {x : H // x ≠ 1 ∧ x ^ 2 = 1} where
  toFun φ :=
    { toFun := fun x => ⟨φ x, by
        constructor
        · exact fun hx => x.property.1 (φ.injective (by simpa using hx))
        · simpa only [map_pow, map_one] using congrArg φ x.property.2⟩
      invFun := fun x => ⟨φ.symm x, by
        constructor
        · exact fun hx => x.property.1 (φ.symm.injective (by simpa using hx))
        · simpa only [map_pow, map_one] using congrArg φ.symm x.property.2⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }
  map_one' := by ext x; rfl
  map_mul' := by intro φ ψ; ext x; rfl

private theorem involution_card_three
    {H : Type u} [Group H] [Finite H] (h : IsSL2Two H) :
    Nat.card {x : H // x ≠ 1 ∧ x ^ 2 = 1} = 3 := by
  obtain ⟨e⟩ := h
  let eI : {x : H // x ≠ 1 ∧ x ^ 2 = 1} ≃
      {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) // x ≠ 1 ∧ x ^ 2 = 1} :=
    e.toEquiv.subtypeEquiv (by
      intro x
      change (x ≠ 1 ∧ x ^ 2 = 1) ↔ (e x ≠ 1 ∧ (e x) ^ 2 = 1)
      constructor
      · rintro ⟨hne,hpow⟩
        refine ⟨fun he => hne (e.injective (by simpa using he)), ?_⟩
        simpa only [map_pow,map_one] using congrArg e hpow
      · rintro ⟨hne,hpow⟩
        refine ⟨fun he => hne (by simp [he]), ?_⟩
        apply e.injective
        simpa only [map_pow,map_one] using hpow)
  rw [Nat.card_congr eI, Nat.card_eq_fintype_card]
  decide +kernel

private theorem mulAut_card_le_six
    {H : Type u} [Group H] [Finite H] (h : IsSL2Two H)
    (hgen : ∀ x : H, ∃ a b : H, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ x = a * b) :
    Nat.card (MulAut H) ≤ 6 := by
  classical
  have hinj : Function.Injective (involutionPerm (H := H)) := by
    intro φ ψ heq
    have hfix (x : H) (hx : x ^ 2 = 1) : φ x = ψ x := by
      by_cases hxone : x = 1
      · simp [hxone]
      have he := congrArg (fun f => ((f ⟨x, hxone, hx⟩ :
        {x : H // x ≠ 1 ∧ x ^ 2 = 1}) : H)) heq
      exact he
    ext x
    obtain ⟨a,b,ha,hb,rfl⟩ := hgen x
    rw [map_mul,map_mul,hfix a ha,hfix b hb]
  have hcard := Nat.card_le_card_of_injective (involutionPerm (H := H)) hinj
  let _ : Fintype {x : H // x ≠ 1 ∧ x ^ 2 = 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm {x : H // x ≠ 1 ∧ x ^ 2 = 1}),
    Fintype.card_perm, ← Nat.card_eq_fintype_card,
    involution_card_three h] at hcard
  exact hcard

private theorem sl2_conj_surjective
    {H : Type u} [Group H] [Finite H] (h : IsSL2Two H) :
    Function.Surjective (MulAut.conj : H →* MulAut H) := by
  have hcenter := RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two h
  have hinj : Function.Injective (MulAut.conj : H →* MulAut H) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hφ : MulAut.conj x = 1 := MonoidHom.mem_ker.mp hx
    have hxcenter : x ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro y
      have heq := congrArg (fun φ : MulAut H => φ y) hφ
      change x * y * x⁻¹ = y at heq
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    rwa [hcenter] at hxcenter
  have hcard : Nat.card (MulAut H) ≤ Nat.card H := by
    rw [RankOneThreeGroupAssembly.isSL2Two_card h]
    exact mulAut_card_le_six h (sl2_involution_products h)
  exact (hinj.bijective_of_nat_card_le hcard).2

/-- The correcting inner element for an automorphism induced by a normalizer. -/
public theorem sl2_normalizer_exists_inner
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) (hD : IsSL2Two D) (g : G)
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    ∃ d : D, (d : G)⁻¹ * g ∈ Subgroup.centralizer (D : Set G) := by
  obtain ⟨d, hd⟩ := sl2_conj_surjective hD (D.normalizerMonoidHom ⟨g,hg⟩)
  refine ⟨d, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have heq := congrArg (fun φ : MulAut D => (φ ⟨x,hx⟩ : G)) hd
  change (d : G) * x * (d : G)⁻¹ = g * x * g⁻¹ at heq
  have hm := congrArg (fun z : G => (d : G)⁻¹ * z * g) heq
  simpa [mul_assoc] using hm

/-- A normalizer of an SL₂(2) subgroup differs from an element of that
subgroup by an element of its centralizer. -/
public theorem sl2_normalizer_le_sup_centralizer
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) (hD : IsSL2Two D) :
    Subgroup.normalizer (D : Set G) ≤ D ⊔ Subgroup.centralizer (D : Set G) := by
  intro g hg
  obtain ⟨d,hcentral⟩ := sl2_normalizer_exists_inner D hD g hg
  have hmem : (d : G) * ((d : G)⁻¹ * g) ∈ D ⊔ Subgroup.centralizer (D : Set G) :=
    (D ⊔ Subgroup.centralizer (D : Set G)).mul_mem
      ((show D ≤ D ⊔ Subgroup.centralizer (D : Set G) from le_sup_left) d.property)
      ((show Subgroup.centralizer (D : Set G) ≤
        D ⊔ Subgroup.centralizer (D : Set G) from le_sup_right) hcentral)
  simpa using hmem

end Stellmacher.SectionOne
