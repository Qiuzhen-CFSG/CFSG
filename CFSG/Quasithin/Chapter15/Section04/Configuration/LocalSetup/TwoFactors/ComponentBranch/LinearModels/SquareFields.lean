module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields.FieldActor
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields.LinearCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields.CoefficientFixed

/-!
# The square-field fixed-action reduction to PSL₂(9)

A faithful elementary four-group fixing a Sylow two-subgroup has a
nontrivial field actor. Conjugating it to a coefficient involution preserves
its actual fixed subgroup and the self-centralizing two-core condition.
Projective descent identifies that full fixed subgroup with PGL₂ over the
fixed subfield. The two-core obstruction then forces the fixed field, hence
the prime, to be three.

The conditional assembly API is retained, and `prime_eq_three_of_square_field`
discharges its fixed-group identification using `CoefficientFixed`. It covers
both prime residues three and five modulo eight. The source's component and
extension identifications remain the responsibility of the parent application;
this is the intrinsic calculation on the actual PSL₂ matrix group.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163, using the square parameters in F.6.18(6),(8), pp.309–310.
-/

public section
noncomputable section
open GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels

/-- Given the actual coefficient-fixed group identification, the square-field
fixed-action hypotheses force `p = 3`. Projective descent remains an input. -/
theorem prime_eq_three_of_coefficient_fixed_equiv
    {F A : Type*} [Field F] [Finite F] [Group A] [Finite A]
    [IsElementaryAbelian 2 A]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2) (hm : p ^ 2 % 16 = 9)
    (P : Sylow 2 (PSL2 F))
    (ρ : A →* MulAut (PSL2 F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup (PSL2 F)) → ρ a x = x)
    (hc : CharacteristicTwoFixed ρ)
    (hdescent : ∀ (σ : F ≃+* F), orderOf σ = 2 →
      Nonempty ((psl2FieldAut F σ).fixedSubgroup ≃*
        PGL2 (FixedPoints.subfield (Subgroup.zpowers σ) F))) :
    p = 3 := by
  obtain ⟨a, σ, c, ha, hσ, hconj⟩ :=
    SquareFields.exists_coefficient_actor hp hF hm P ρ hρ hA hfix
  let β := (pgl2InnerAutPSL2 F (SquareFields.field_odd hp hF hm)
    (SquareFields.field_large hp hF hm) c)⁻¹
  have hcf : HasCharacteristicTwo (psl2FieldAut F σ).fixedSubgroup := by
    rw [← hconj]
    exact (hc a ha).of_equiv (MulAut.fixedSubgroupCongr β (ρ a))
  obtain ⟨e⟩ := hdescent σ hσ
  have hcard := SquareFields.fixed_subfield_card hF σ hσ
  have hodd : IsOddPrimePower
      (Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F)) :=
    ⟨p, 1, hp, SquareFields.odd_prime hp hm, by decide, by simpa using hcard⟩
  have hthree := SquareFields.pgl2_card_eq_three_of_characteristicTwo
    (FixedPoints.subfield (Subgroup.zpowers σ) F) hodd (hcf.of_equiv e)
  rwa [hcard] at hthree

/-- A faithful elementary four-group fixing a Sylow two-subgroup pointwise,
with characteristic-two fixed subgroups for all its nonidentity actors,
forces a square field of order `p² ≡ 9 (mod 16)` to have `p = 3`.
The coefficient-fixed group identification is proved, with no descent premise. -/
theorem prime_eq_three_of_square_field
    {F A : Type*} [Field F] [Finite F] [Group A] [Finite A]
    [IsElementaryAbelian 2 A]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2) (hm : p ^ 2 % 16 = 9)
    (P : Sylow 2 (PSL2 F))
    (ρ : A →* MulAut (PSL2 F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup (PSL2 F)) → ρ a x = x)
    (hc : CharacteristicTwoFixed ρ) : p = 3 :=
  prime_eq_three_of_coefficient_fixed_equiv hp hF hm P ρ hρ hA hfix hc
    (SquareFields.coefficient_fixed_equiv hp hF hm)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
