module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import GorensteinWalter.PSL2DihedralSylow

/-!
# Excluding genuine Ree F₄ from odd-prime PSL₂

For every supplied exceptional endomorphism, the two end simple roots give
a subgroup of its actual twist-fixed group isomorphic to the additive
coefficient field. This type VI root group has order 2^(2m+1) ≥ 8 when
m ≥ 1, and every element squares to one. Transporting it along the two
model isomorphisms contradicts the dihedral Sylow two-subgroups of odd PSL₂:
their subgroups of exponent two have order at most four.

This supplies the Ree comparison in the full characteristic-two list of
Aschbacher–Smith, 1.1.5(3), printed pp.501–503, used in the proof of 15.4.20,
p.1164 (`refs/quasithin.pdf`). The fixed root group construction is GLS3,
2.4.1 and Table 2.4 type VI (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open ReeF4.LocalBlockInput.PairRigidity
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter

/-- Every genuine Ree F₄ witness with m ≥ 1 is incompatible with odd-prime PSL₂.
Both model predicates retain their actual carrier isomorphisms. -/
theorem not_ree {Q : Type*} [Group Q] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (_hp5 : 5 ≤ p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) {m : ℕ} (hm : 1 ≤ m)
    (hree : Chapter1.Section02.LocalModels.IsReeF4At Q m) : False := by
  obtain ⟨F, _, _, hF, ⟨eodd⟩⟩ := hodd
  obtain ⟨d, ⟨eree⟩⟩ := hree
  let eModel := eree.symm.trans eodd
  let A := Multiplicative (ReeF4.CoefficientField m)
  let eA := positiveLinearEquiv d
  let f : A →* GorensteinWalter.PSL2 F :=
    eModel.toMonoidHom.comp ((simpleBlock d .linear true).subtype.comp eA.toMonoidHom)
  have hf : Function.Injective f := eModel.injective.comp
    ((Subgroup.subtype_injective _).comp eA.injective)
  have hA (a : A) : a ^ 2 = 1 := by
    change 2 • a.toAdd = 0
    simp [nsmul_eq_mul, CharTwo.two_eq_zero]
  have hpA : IsPGroup 2 A := fun a => ⟨1, by simpa using hA a⟩
  obtain ⟨S, hS⟩ :=
    (hpA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hd := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    ⟨p, 1, hp, ho, by omega, by simpa using hF⟩
  obtain ⟨n, _hn, ⟨eS⟩⟩ := hd S
  let g : A →* S := f.codRestrict (S : Subgroup _) (fun a => hS ⟨a, rfl⟩)
  let k : A →* DihedralGroup (2 ^ n) := eS.toMonoidHom.comp g
  have hk : Function.Injective k := by
    intro a b h
    exact hf (congrArg Subtype.val (eS.injective h))
  have hc : Nat.card A ≤ 4 := calc
    Nat.card A = Nat.card k.range := Nat.card_congr (MonoidHom.ofInjective hk).toEquiv
    _ ≤ 4 := DihedralGroup.card_le_four_of_square_eq_one k.range (by
      intro x
      obtain ⟨a, ha⟩ := x.property
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [← ha, ← map_pow, hA a, map_one])
  have hl : 8 ≤ Nat.card A := by
    change 8 ≤ Nat.card (ReeF4.CoefficientField m)
    rw [ReeF4.field_card]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ 2 * m + 1)
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
