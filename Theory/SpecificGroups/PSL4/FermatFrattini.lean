module
public import Theory.SpecificGroups.PSL4.OddFrattiniSixteen
public import Theory.SpecificGroups.GL2.FermatFrattini

/-!
# Three Frattini generators for Fermat linear four-space Sylows

The established determinant-one two-block subgroup has odd index in SL₄.
The sharper two-generator calculation for its actual GL₂ base gives three
Frattini generators after adjoining the block swap. The original projective
surjection retains this bound. This excludes a GL₄(2) outer section on the
Fermat PSL₄ family in Aschbacher--Smith 4.4.10--11 and 12.1.9, pp.621 and 793.
-/

public noncomputable section
namespace Theory.SpecificGroups.PSL4.FermatFrattini
open Subgroup Matrix OddFrattiniSixteen
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]
local notation "GL₂" => GL (Fin 2) F
local notation "d" => (GeneralLinearGroup.det : GL₂ →* Fˣ)

private def detSection : Fˣ →* GL₂ :=
  (GeneralLinearGroup.diagonalPair F).comp (MonoidHom.inl Fˣ Fˣ)
omit [Finite F] in
private theorem detSection_spec : (d).comp detSection = MonoidHom.id Fˣ := by
  ext u
  simp [detSection,GeneralLinearGroup.det,GeneralLinearGroup.diagonalPair,Matrix.det_fin_two]

private theorem sylow_frattini_le (hF : ∃ k : ℕ, Nat.card F = 2 ^ (2 ^ k) + 1)
    (P : Sylow 2 (BalancedWreath.W d)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  apply BalancedWreath.sylow_card_frattini_le d detSection detSection_spec 4 ?_ P
  exact GeneralLinearGroup.FermatFrattini.sylow_frattini_le_four hF

theorem linear_frattini_le (hF : ∃ k : ℕ, Nat.card F = 2 ^ (2 ^ k) + 1)
    (P : Sylow 2 SL(4,F)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  have ho : Odd (Nat.card F) := by
    obtain ⟨k,hk⟩ := hF
    rw [hk]
    exact (even_two.pow_of_ne_zero (by positivity : 2 ^ k ≠ 0)).add_one
  let j := inclusion (F := F)
  let Q : Sylow 2 (BalancedWreath.W d) := default
  have hj : Function.Injective j := inclusion_injective
  let U : Subgroup j.range := (Q : Subgroup (BalancedWreath.W d)).map
    (MonoidHom.ofInjective hj).toMonoidHom
  have hUidx : U.index = (Q : Subgroup (BalancedWreath.W d)).index :=
    index_map_of_bijective (MonoidHom.ofInjective hj).bijective _
  let Sg : Subgroup SL(4,F) := U.map j.range.subtype
  have hSidx : ¬ 2 ∣ Sg.index := by
    rw [index_map_subtype,hUidx]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index (odd_index ho).not_two_dvd_nat
  let S : Sylow 2 SL(4,F) := ((Q.isPGroup'.map _).map _).toSylow hSidx
  let e₁ : Q ≃* U := Q.equivMapOfInjective (MonoidHom.ofInjective hj).toMonoidHom
    (MonoidHom.ofInjective hj).injective
  let e₂ : U ≃* S := U.equivMapOfInjective j.range.subtype Subtype.val_injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S),
    ←Theory.GroupTheory.SylowFrattiniBounds.card_congr (e₁.trans e₂)]
  exact sylow_frattini_le hF Q

/-- The actual projective linear quotient preserves the three-generator bound. -/
theorem projective_frattini_le (hF : ∃ k : ℕ, Nat.card F = 2 ^ (2 ^ k) + 1)
    (P : Sylow 2 PSL(4,F)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  exact OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(4,F))) (QuotientGroup.mk'_surjective _)
    (linear_frattini_le hF) P

end Theory.SpecificGroups.PSL4.FermatFrattini
