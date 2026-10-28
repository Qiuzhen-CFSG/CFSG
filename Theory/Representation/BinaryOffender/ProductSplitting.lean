module
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Offenders split across two independent actors

If neither coordinate representation has a strong offender, the rank of an
elementary subgroup of the product is bounded above by the sum of its projection
ranks, which is bounded above by its fixed codimension. Equality for an offender
forces equality of cardinalities, so it is the product of its projections.
Each nontrivial projection is itself an offender.

This is the direct-sum counting step for the paired natural factors in
Aschbacher–Smith B.6.10 and E.2.3(2), printed pp.117 and216–217.
-/

open Subgroup
namespace Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem card_eq_two_pow_rank_all (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem rank_le_fixedCodim_of_not_strong
    (ρ : Representation (ZMod 2) G V) (hn : ¬ IsStrongFFModule ρ)
    (A : Subgroup G) [IsElementaryAbelian 2 A] : rank A ≤ fixedCodim ρ A := by
  by_cases hA : A = ⊥
  · subst A
    simp [rank]
  · exact Nat.le_of_not_gt (fun h => hn ⟨A, ⟨hA,inferInstance⟩,h⟩)

private theorem rank_le_sum_projections (A : Subgroup (G × H))
    [IsElementaryAbelian 2 A] :
    rank A ≤ rank (A.map (MonoidHom.fst G H)) + rank (A.map (MonoidHom.snd G H)) := by
  let A₁ := A.map (MonoidHom.fst G H)
  let A₂ := A.map (MonoidHom.snd G H)
  let : IsElementaryAbelian 2 A₁ := IsElementaryAbelian.map (MonoidHom.fst G H)
  let : IsElementaryAbelian 2 A₂ := IsElementaryAbelian.map (MonoidHom.snd G H)
  have hle : A ≤ A₁.prod A₂ := le_prod_iff.mpr ⟨le_rfl,le_rfl⟩
  have hc : Nat.card A ≤ Nat.card A₁ * Nat.card A₂ := by
    calc
      Nat.card A ≤ Nat.card (A₁.prod A₂) := card_le_of_le hle
      _ = Nat.card A₁ * Nat.card A₂ := by
        rw [Nat.card_congr (A₁.prodEquiv A₂).toEquiv,Nat.card_prod]
  rw [card_eq_two_pow_rank_all A,card_eq_two_pow_rank_all A₁,
    card_eq_two_pow_rank_all A₂,←pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

variable (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
local notation "Πρ" => Representation.prod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

public theorem product_not_strong
    (hρ : ¬ IsStrongFFModule ρ) (hσ : ¬ IsStrongFFModule σ) :
    ¬ IsStrongFFModule Πρ := by
  rintro ⟨A,hA,hlt⟩
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.map (MonoidHom.fst G H)) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.map (MonoidHom.snd G H)) := IsElementaryAbelian.map _
  have hr := rank_le_sum_projections A
  have h₁ := rank_le_fixedCodim_of_not_strong ρ hρ (A.map (MonoidHom.fst G H))
  have h₂ := rank_le_fixedCodim_of_not_strong σ hσ (A.map (MonoidHom.snd G H))
  rw [fixedCodim_prod] at hlt
  change fixedCodim (ρ.comp (MonoidHom.fst G H)) A +
    fixedCodim (σ.comp (MonoidHom.snd G H)) A < rank A at hlt
  have hc₁ : fixedCodim (ρ.comp (MonoidHom.fst G H)) A = fixedCodim ρ (A.map (MonoidHom.fst G H)) :=
    congrArg (fun X : Submodule (ZMod 2) V => Module.finrank (ZMod 2) (V ⧸ X))
      (fixedSpace_comp_map ρ (MonoidHom.fst G H) A)
  have hc₂ : fixedCodim (σ.comp (MonoidHom.snd G H)) A = fixedCodim σ (A.map (MonoidHom.snd G H)) :=
    congrArg (fun X : Submodule (ZMod 2) W => Module.finrank (ZMod 2) (W ⧸ X))
      (fixedSpace_comp_map σ (MonoidHom.snd G H) A)
  rw [hc₁,hc₂] at hlt
  omega

public theorem offender_product_of_not_strong
    (hρ : ¬ IsStrongFFModule ρ) (hσ : ¬ IsStrongFFModule σ)
    {A : Subgroup (G × H)} (hA : IsOffender Πρ A) :
    A = (A.map (MonoidHom.fst G H)).prod (A.map (MonoidHom.snd G H)) ∧
    (A.map (MonoidHom.fst G H) = ⊥ ∨ IsOffender ρ (A.map (MonoidHom.fst G H))) ∧
    (A.map (MonoidHom.snd G H) = ⊥ ∨ IsOffender σ (A.map (MonoidHom.snd G H))) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let A₁ := A.map (MonoidHom.fst G H)
  let A₂ := A.map (MonoidHom.snd G H)
  let : IsElementaryAbelian 2 A₁ := IsElementaryAbelian.map (MonoidHom.fst G H)
  let : IsElementaryAbelian 2 A₂ := IsElementaryAbelian.map (MonoidHom.snd G H)
  have hr := rank_le_sum_projections A
  change rank A ≤ rank A₁ + rank A₂ at hr
  have h₁ := rank_le_fixedCodim_of_not_strong ρ hρ A₁
  have h₂ := rank_le_fixedCodim_of_not_strong σ hσ A₂
  have hc : fixedCodim ρ A₁ + fixedCodim σ A₂ ≤ rank A := by
    have hc := hA.2
    rw [fixedCodim_prod] at hc
    change Module.finrank (ZMod 2) (V ⧸ fixedSpace (ρ.comp (MonoidHom.fst G H)) A) +
      Module.finrank (ZMod 2) (W ⧸ fixedSpace (σ.comp (MonoidHom.snd G H)) A) ≤ rank A at hc
    rw [fixedSpace_comp_map ρ (MonoidHom.fst G H) A,
      fixedSpace_comp_map σ (MonoidHom.snd G H) A] at hc
    exact hc
  have he₁ : fixedCodim ρ A₁ = rank A₁ := by omega
  have he₂ : fixedCodim σ A₂ = rank A₂ := by omega
  have hrank : rank A = rank A₁ + rank A₂ := by omega
  refine ⟨?_,?_,?_⟩
  · apply eq_of_le_of_card_ge (le_prod_iff.mpr ⟨le_rfl,le_rfl⟩)
    change Nat.card (A₁.prod A₂) ≤ Nat.card A
    rw [Nat.card_congr (A₁.prodEquiv A₂).toEquiv,Nat.card_prod,
      card_eq_two_pow_rank_all A₁,card_eq_two_pow_rank_all A₂,
      card_eq_two_pow_rank_all A,hrank,pow_add]
  · by_cases ha : A₁ = ⊥
    · exact Or.inl ha
    · exact Or.inr ⟨⟨ha,inferInstance⟩,he₁.le⟩
  · by_cases ha : A₂ = ⊥
    · exact Or.inl ha
    · exact Or.inr ⟨⟨ha,inferInstance⟩,he₂.le⟩
end Representation.BinaryOffender
