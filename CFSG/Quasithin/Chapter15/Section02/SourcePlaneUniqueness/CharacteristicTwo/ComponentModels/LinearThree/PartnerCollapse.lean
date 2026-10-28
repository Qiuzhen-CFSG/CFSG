module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryResidualAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource
public import Theory.GroupTheory.SolvableRadical

/-!
# Partner collapse from the normal binary cubic factor

The constructed K₁ = O²(K ∩ X) is solvable, with quotient of order three
by its two-core. If Kc lies in MI, its normality in MI makes K₁ normal in
Kc. Consequently the solvable radical of Kc cannot be a two-group.
The earlier alternative Kc = K or two-group radical then forces Kc = K,
and the proved 15.2.21(2) yields the three-prime centralizer C_M(V).

The structural alternative remains explicit: its proper rows must be
obtained from the actual component models in 15.2.12(2), owned by
qt-e-152-plane-geometry. The containment Kc ≤ MI is the earlier
15.2.21(1) conclusion, owned by qt-e-152-char2-small-actions. This module
does not discharge either earlier source premise or prove full 15.2.23.
Final discharge belongs to qt-e-152-plane-uniqueness and component assembly
qt-e-152-char2-component-models.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(2), 15.2.21(1--2), and the proof of 15.2.23,
printed pp.1111, 1114 and 1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private theorem solvable_of_cubic_core_quotient (A : Subgroup G)
    (hA : Nat.card (A ⧸ pCore 2 A) = 3) : Group.IsSolvable A := by
  let : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hA
  let : Group.IsSolvable (A ⧸ pCore 2 A) := inferInstance
  let : Group.IsNilpotent (pCore 2 A) := (pCore_isPGroup (p := 2) (G := A)).isNilpotent
  exact Group.isSolvable_of_ker_le_range (pCore 2 A).subtype (QuotientGroup.mk' (pCore 2 A))
    (by rw [QuotientGroup.ker_mk',range_subtype])

include d in
/-- The normal cubic opposite-parabolic residual rules out a partner orbit
whose solvable radical is a two-group. The nontrivial cubic quotient is
constructed from the actual binary component. -/
theorem Branch.binary_partner_radical_not_two
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I) :
    ¬ IsPGroup 2 (solvableRadical (smallActionKc H Mc)) := by
  let K := smallActionK H
  let Kc := smallActionKc H Mc
  let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
  have hLK : L ≤ K := (map_subtype_le _).trans inf_le_left
  have hLKc : L ≤ Kc := hLK.trans (le_conjugateSpanBy _ _)
  have hnL : Kc ≤ normalizer (L : Set G) := hKcI.trans
    (b.binary_factor_normalized d hI hout hn)
  let A := L.subgroupOf Kc
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnL
  have hc := b.binary_factor_core_quotient_card d hI
  let : Group.IsSolvable L := solvable_of_cubic_core_quotient L hc
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hLKc).toMonoidHom) (subgroupOfEquivOfLe hLKc).injective
  intro hr
  have hp : IsPGroup 2 A := hr.to_le (le_solvableRadical A inferInstance inferInstance)
  have hpL := hp.of_equiv (subgroupOfEquivOfLe hLKc)
  have hq := hpL.to_quotient (pCore 2 L)
  obtain ⟨n,he⟩ := hq.exists_card_eq
  rw [hc] at he
  have hd : 3 ∣ 2 ^ n := he ▸ dvd_refl 3
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

include d in
/-- Apply the earlier 15.2.12 structural alternative after the 15.2.21(1)
centralization. Its proper alternatives have two-group solvable radical;
the literal normal cubic factor therefore forces K = Kc. -/
theorem Branch.binary_partner_eq_of_radical_alternative
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hcases : smallActionKc H Mc = smallActionK H ∨
      IsPGroup 2 (solvableRadical (smallActionKc H Mc))) :
    smallActionK H = smallActionKc H Mc := by
  rcases hcases with he | hr
  · exact he.symm
  · exact (b.binary_partner_radical_not_two d hI hout hn hKcI hr).elim

include d in
/-- The original C_M(V) is three-prime after the structural partner collapse.
The action supplies normality, and the original wreath quotient discharges
the intersection premise of 15.2.21(2). -/
theorem Branch.binary_centralizer_threePrime_of_radical_alternative
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hcases : smallActionKc H Mc = smallActionK H ∨
      IsPGroup 2 (solvableRadical (smallActionKc H Mc))) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) :=
  SmallActionsSource.source_15_2_21_2_from_preceding d
    (b.binary_partner_eq_of_radical_alternative d hI hout
      (b.binary_normal_of_action d hI hout f hker) hKcI hcases)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
