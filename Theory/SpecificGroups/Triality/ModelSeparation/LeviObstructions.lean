module

public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import GorensteinWalter.PSL2DihedralSylow
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Triality model obstructions from the cubic arm Levi

The genuine three-arm Levi embeds SL₂ over the cubic coefficient field.
Its upper root subgroup has order q³ ≥ 8 and exponent two, excluding every
odd-field PSL₂ because a dihedral group has no such subgroup of order above
four. Its actual SL₂ order also divides the carrier order; for q = 2^n,
q⁶ = 64^n is one modulo nine, so nine divides that order. Both arguments
include n = 1 and need neither the full triality order nor model simplicity.

The odd-PSL₂ argument is extracted from the already checked Chapter 15
`LieParameter/Triality.lean` proof so that lower-layer consumers can reuse it.
Source: GLS3 §§2.4–2.6 for the arm Levi; Aschbacher–Smith 1.2.1(3), printed
p.504, and the proof of E.6.8, printed p.247 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Triality.Standard.ModelSeparation
open Parabolics

private def armEmbedding (P : Parameters) (hp : P.prime = 2) :
    SL(2,ExtensionField P) →* Carrier P := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact (levi P .arms).subtype.comp
    (((Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).trans
      (leviArmsEquivPSL2 P hp).symm).toMonoidHom)

private theorem armEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (armEmbedding P hp) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  exact (Subgroup.subtype_injective _).comp
    (((Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).trans
      (leviArmsEquivPSL2 P hp).symm).injective)

/-- The actual arm Levi forces nine to divide the carrier order. -/
theorem nine_dvd_card (n : ℕ) (hn : 0 < n) : 9 ∣ Nat.card (Carrier (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  have hd := Subgroup.card_dvd_of_injective (armEmbedding P rfl) (armEmbedding_injective P rfl)
  have hnine : 9 ∣ Nat.card SL(2,ExtensionField P) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, card_extensionField]
    apply dvd_mul_of_dvd_right
    change 9 ∣ ((2 ^ n) ^ 3) ^ 2 - 1
    have he : ((2 ^ n) ^ 3) ^ 2 = 64 ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm n, pow_mul]
      rfl
    rw [he]
    have hm : 64 ^ n % 9 = 1 := by
      simpa only [Nat.ModEq, one_pow, Nat.reduceMod] using
        (show Nat.ModEq 9 64 1 by decide).pow n
    exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  exact hnine.trans hd

private theorem card_le_four_of_dihedral_sylow {A G : Type*} [Group A] [Group G]
    (hG : GorensteinWalter.HasDihedralSylowTwo G) (hA : ∀ a : A, a ^ 2 = 1)
    (f : A →* G) (hf : Function.Injective f) : Nat.card A ≤ 4 := by
  have hpA : IsPGroup 2 A := fun a => ⟨1, by simpa using hA a⟩
  obtain ⟨S, hS⟩ := (hpA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨m, _hm, ⟨eS⟩⟩ := hG S
  let g : A →* S := f.codRestrict (S : Subgroup G) (fun a => hS ⟨a, rfl⟩)
  let k : A →* DihedralGroup (2 ^ m) := eS.toMonoidHom.comp g
  have hk : Function.Injective k := by
    intro a b h
    exact hf (congrArg Subtype.val (eS.injective h))
  calc
    Nat.card A = Nat.card k.range := Nat.card_congr (MonoidHom.ofInjective hk).toEquiv
    _ ≤ 4 := DihedralGroup.card_le_four_of_square_eq_one k.range (by
      intro x
      obtain ⟨a, ha⟩ := x.property
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [← ha, ← map_pow, hA a, map_one])

/-- The cubic elementary root subgroup excludes every odd-field PSL₂. -/
theorem not_equiv_odd_psl2 (n : ℕ) (hn : 0 < n) (F : Type*) [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (e : Carrier (binaryParameters n hn) ≃* PSL(2,F)) : False := by
  let P := binaryParameters n hn
  let := rankOneExtensionCharTwo P rfl
  let u : Multiplicative (ExtensionField P) →* GorensteinWalter.PSL2 F :=
    e.toMonoidHom.comp ((armEmbedding P rfl).comp
      (SpecialLinearGroup.upperUnipotentHom (ExtensionField P)))
  have hu : Function.Injective u := e.injective.comp
    ((armEmbedding_injective P rfl).comp (SpecialLinearGroup.upperUnipotentHom_injective _))
  have hd := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd
  have hc := card_le_four_of_dihedral_sylow hd (fun a : Multiplicative (ExtensionField P) => by
    change 2 • a.toAdd = 0
    simp [nsmul_eq_mul, CharTwo.two_eq_zero]) u hu
  have hl : 8 ≤ Nat.card (Multiplicative (ExtensionField P)) := by
    change 8 ≤ Nat.card (ExtensionField P)
    rw [card_extensionField]
    exact Nat.pow_le_pow_left P.q_ge_two 3
  omega

end Triality.Standard.ModelSeparation
