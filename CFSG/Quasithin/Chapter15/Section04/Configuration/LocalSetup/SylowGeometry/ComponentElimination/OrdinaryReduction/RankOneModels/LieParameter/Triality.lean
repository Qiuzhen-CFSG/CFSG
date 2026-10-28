module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Triality.LeviArmCommutation
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import GorensteinWalter.PSL2DihedralSylow

/-!
# Excluding genuine binary triality from odd-prime PSL₂

The three arms of the genuine D4 graph-field construction give a faithful
SL₂ over the cubic extension. The proved pinned maps and arm commutation
instantiate its descent into the elementary fixed-point subgroup and through
the central quotient. Its upper transvections form an elementary abelian
subgroup of order q³ ≥ 8, including q = 2. Odd-prime PSL₂ has dihedral Sylow
two-subgroups, whose subgroups of exponent two have order at most four.

This supplies the triality comparison in the full characteristic-two list of
Aschbacher–Smith, 1.1.5(3), printed pp.501–503, used in the proof of 15.4.20,
p.1164 (`refs/quasithin.pdf`). The subsystem and Levi construction is GLS3
§2.6, especially 2.6.2 and 2.6.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Matrix
open scoped MatrixGroups
open Triality.Standard Triality.Standard.Parabolics

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

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter

/-- A genuine triality group over a binary field cannot be odd-prime PSL₂.
The two family predicates retain their actual carrier isomorphisms. -/
theorem not_triality {Q : Type*} [Group Q] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (_hp5 : 5 ≤ p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) {f : ℕ} (_hf : 1 ≤ f)
    (htriality : Triality.Standard.IsTrialityGroupAt (2 ^ f) Q) : False := by
  obtain ⟨F, _, _, hF, ⟨eodd⟩⟩ := hodd
  obtain ⟨P, hq, ⟨et⟩⟩ := htriality
  have hp2 : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    apply P.prime_prime.dvd_of_dvd_pow (n := f)
    rw [← hq]
    exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  let := rankOneExtensionCharTwo P hp2
  let eLevi : SL(2, ExtensionField P) ≃* levi P .arms :=
    (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).trans
      (leviArmsEquivPSL2OfPinnedMaps P hp2
        (pinnedRankOneMaps P hp2) (armRootCommutation P hp2)).symm
  let eModel := et.symm.trans eodd
  let u : Multiplicative (ExtensionField P) →* GorensteinWalter.PSL2 F :=
    eModel.toMonoidHom.comp ((levi P .arms).subtype.comp
      (eLevi.toMonoidHom.comp (SpecialLinearGroup.upperUnipotentHom (ExtensionField P))))
  have hu : Function.Injective u := eModel.injective.comp
    ((Subgroup.subtype_injective _).comp (eLevi.injective.comp
      (SpecialLinearGroup.upperUnipotentHom_injective _)))
  have hd := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    ⟨p, 1, hp, ho, by omega, by simpa using hF⟩
  have hc := card_le_four_of_dihedral_sylow hd (fun a : Multiplicative (ExtensionField P) => by
    change 2 • a.toAdd = 0
    simp [nsmul_eq_mul, CharTwo.two_eq_zero]) u hu
  have hl : 8 ≤ Nat.card (Multiplicative (ExtensionField P)) := by
    change 8 ≤ Nat.card (ExtensionField P)
    rw [card_extensionField]
    exact Nat.pow_le_pow_left P.q_ge_two 3
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
