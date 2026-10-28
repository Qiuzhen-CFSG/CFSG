module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import Theory.SpecificGroups.OddThreeRank
public import Theory.ElementaryAbelian.PrimePlane

/-!
# Inner actors in the remaining PSU₃ obstruction

The actual projective unitary model has elementary two-rank at most two:
its elementary subgroups lift through the odd scalar kernel, and a faithful
three-dimensional determinant-one action has at most four simultaneous sign
patterns. Therefore every inner actor in a large-family obstruction is a
four-group, with an actual equivalence to the binary plane.

If a local radical kills a nonidentity element of this four-group, the image
has order at most two. This verifies the literal quotient-rank clause of
E.1.5 for a component E-member, and places that subgroup in the obstruction's
overgroup. The E₀ and component structure conditions remain explicit.

Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.14(7), printed pp.210, 214;
A.3.21(b), printed p.55. This is the rank calculation for the inner branch,
not the construction of an escaping local subgroup.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

/-- Two-rank is bounded in the literal projective model, without replacing it by SU₃. -/
theorem primeRank_two_le_of_model (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p) :
    primeRank 2 L ≤ 2 := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv L e.toEquiv
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp hodd hcard hc

/-- The large inner actors have order exactly four, including at p = 3. -/
theorem inner_member_card_eq_four (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) (hAL : A ≤ L) : Nat.card A = 4 := by
  let := d.elementary.1 A hA
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hc : Nat.card A ≤ 2 ^ 2 := by
    have hh := (primeRank_le_iff_elementary_card_le L).mp
      (primeRank_two_le_of_model L hp hodd hmodel) (A.subgroupOf L) inferInstance
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv] at hh
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hc)
  have hn2 : n = 2 := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hcard1 : Nat.card A ≤ 2 ^ 1 := by
      rw [hn]
      exact pow_le_pow_right' (by decide) hn1
    have hr := IsElementaryAbelian.rank_le_of_card_le A hcard1
    have := d.large A hA hAT hne
    omega
  simpa [hn2] using hn

/-- The remaining inner case contains an actual binary plane in the source family. -/
theorem exists_inner_plane (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L) :
    ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≤ L ∧ Nat.card A = 4 ∧
      Nonempty (A ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨A, hA, hAT, hne, hAL⟩ := hi
  let := d.elementary.1 A hA
  have hc := inner_member_card_eq_four L hp hodd hmodel d hA hAT hne hAL
  exact ⟨A, hA, hAT, hAL, hc,
    IsElementaryAbelian.nonempty_mulEquiv_plane_of_card (p := 2) hc⟩

private theorem rank_image_le_one_of_four {H : Type*} [Group H] [Finite H]
    (A : Subgroup G) [IsElementaryAbelian 2 A] (f : G →* H)
    (hcard : Nat.card A = 4) (z : G) (hz : z ∈ A) (hne : z ≠ 1) (hfz : f z = 1) :
    Group.rank (A.map f) ≤ 1 := by
  let g : A →* A.map f := f.subgroupMap A
  have hker : g.ker ≠ ⊥ := by
    intro hk
    have hzker : (⟨z, hz⟩ : A) ∈ g.ker := by
      apply Subtype.ext
      exact hfz
    have hzone : (⟨z, hz⟩ : A) = 1 := mem_bot.mp (hk ▸ hzker)
    exact hne (congrArg Subtype.val hzone)
  let : Nontrivial g.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hker
  have hkcard : 2 ≤ Nat.card g.ker := Finite.one_lt_card
  have hprod := g.ker.card_mul_index
  rw [index_ker, g.range_eq_top_of_surjective (f.subgroupMap_surjective A), card_top,
    hcard] at hprod
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
  have : Nat.card (A.map f) ≤ 2 := by nlinarith
  simpa using this

/-- An inner four-group loses a rank in a local radical quotient if that radical
contains a nonidentity actor element. -/
theorem isEMemberAt_one_of_four_radical_element {T A K : Subgroup G}
    (hmember : IsEMember T A K) (hcase : ECaseComponent T A K)
    (hcard : Nat.card A = 4) (z : K)
    (hzA : (z : G) ∈ A) (hne : z ≠ 1) (hzR : z ∈ solvableRadical K) :
    IsEMemberAt 1 T A K := by
  let := hmember.1
  let : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf hmember.2.2.1
  refine ⟨hmember, Or.inr ⟨hcase, ?_⟩⟩
  exact rank_image_le_one_of_four (A.subgroupOf K)
    (QuotientGroup.mk' (solvableRadical K))
    ((Nat.card_congr (subgroupOfEquivOfLe hmember.2.2.1).toEquiv).trans hcard)
    z hzA hne ((QuotientGroup.eq_one_iff _).mpr hzR)

/-- Consumer of the rank calculation: a component E-member with a radical
involution from an inner actor lies in the literal obstruction overgroup.
This discharges E.1.5's quotient-rank premise for such a local construction. -/
theorem inner_component_member_le (L : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmodel : ClassicalGroup.IsPSU L 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A K : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) (hAL : A ≤ L)
    (hmember : IsEMember (T : Subgroup G) A K)
    (hcase : ECaseComponent (T : Subgroup G) A K)
    (z : K) (hzA : (z : G) ∈ A) (hz : z ≠ 1) (hzR : z ∈ solvableRadical K) :
    K ≤ d.overgroup :=
  d.members_le A hA hAT K (isEMemberAt_one_of_four_radical_element hmember hcase
    (inner_member_card_eq_four L hp hodd hmodel d hA hAT hne hAL) z hzA hz hzR)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
