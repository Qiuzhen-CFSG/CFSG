module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Basic
public import Theory.GroupTheory.PPerfectHom

/-!
# The exact surviving cubic in the outer alternative

The quotient over the two source factors is cyclic, so the full
commutator condition places X in their product. The projection of its
normal solvable inverse image onto A₆ is trivial. Thus the nontrivial X
is exactly the C₃ factor. This retains the actual product inclusions
and applies to the native group-only outer contract.

Transport back to G*_v gives |X| = 3. The two-perfect L*_v acts trivially
on X, since Aut(X) has order two. Centralizing X as a group does not
mean fixing its moved space in U_v. Consequently these results are
reductions for the remaining outer exclusion, not that exclusion itself.
The natural six-point action and the cubic moved-plane calculation
must still be recovered from B.5.7; no disputed fixed-space splitting
is used here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(4) and B.5.7, printed pp.105–106; 13.6.13, printed p.929.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

private theorem six_solvable_normal (A : Subgroup (alternatingGroup (Fin 6)))
    [A.Normal] [Group.IsSolvable A] : A = ⊥ := by
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := A.subtype)
        (by rw [h]; exact topEquiv.surjective))).elim

variable {D : Type*} [Group D]

private theorem first_solvable_normal (c : ChapterB.OuterSixThreeShape D)
    (B : Subgroup c.first) [B.Normal] [Group.IsSolvable B] : B = ⊥ := by
  let e := c.firstEquiv
  let : (B.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Group.IsSolvable (B.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap B)
      (e.toMonoidHom.subgroupMap_surjective B)
  exact (map_eq_bot_iff_of_injective (f := e.toMonoidHom) B e.injective).mp (six_solvable_normal _)

/-- The full commutator puts the solvable normal subgroup in the literal
cubic factor. Solvability alone would not eliminate this factor. -/
theorem outer_solvable_le_second (c : ChapterB.OuterSixThreeShape D)
    (A C : Subgroup D) [A.Normal] [Group.IsSolvable A]
    (hfull : ⁅A, C⁆ = A) : A ≤ c.second := by
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  let : CommGroup (D ⧸ (c.first ⊔ c.second)) := IsCyclic.commGroup
  have hd : _root_.commutator D ≤ c.first ⊔ c.second :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hAP : A ≤ c.first ⊔ c.second := by
    rw [← hfull]
    exact (commutator_mono le_top le_top).trans hd
  let f : (c.first × c.second) →* D :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp c.product.injective
  let R := A.comap f
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
    (f := f.subgroupComap A) (fun x y h => Subtype.ext (hf (congrArg (fun a : A => (a : D)) h)))
  let p := MonoidHom.fst c.first c.second
  let : (R.map p).Normal := Subgroup.Normal.map inferInstance _ Prod.fst_surjective
  let : Group.IsSolvable (R.map p) := Group.isSolvable_of_surjective
    (f := p.subgroupMap R) (p.subgroupMap_surjective R)
  have hk : R ≤ p.ker := (map_eq_bot_iff R).mp (first_solvable_normal c (R.map p))
  intro x hx
  let y := c.product.symm ⟨x, hAP hx⟩
  have he : (c.product y : D) = x := congrArg Subtype.val (c.product.apply_symm_apply _)
  have hy : y ∈ R := by
    change (c.product y : D) ∈ A
    rwa [he]
  have hy1 : y.1 = 1 := hk hy
  have he' : x = (y.2 : D) := by
    calc
      x = (c.product (y.1, y.2) : D) := he.symm
      _ = (y.1 : D) * (y.2 : D) := c.product_apply _ _
      _ = (y.2 : D) := by simp [hy1]
  rw [he']
  exact y.2.property

/-- A nontrivial normal solvable full commutator is exactly the source
cubic. This is a placement result, not an exclusion of the outer branch. -/
theorem outer_solvable_eq_second [Finite D] (c : ChapterB.OuterSixThreeShape D)
    (A C : Subgroup D) [A.Normal] [Group.IsSolvable A]
    (hne : A ≠ ⊥) (hfull : ⁅A, C⁆ = A) : A = c.second := by
  have hle := outer_solvable_le_second c A C hfull
  have hc : Nat.card c.second = 3 := by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    exact Nat.card_zmod 3
  have hd : Nat.card A ∣ 3 := hc ▸ card_dvd_of_le hle
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · exact (hne ((card_le_one_iff_eq_bot A).mp h.le)).elim
  · exact eq_of_le_of_card_ge hle (by rw [h, hc])

/-- Apply cubic placement to the original X and offender restriction. -/
theorem minimalSolvable_outer_eq_second {G : Type*} [Group G] [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) = c.second := by
  obtain ⟨hn, hne, _, hs, hfull⟩ := minimalSolvable_in_offender L T z v hz S hS hX
  let := hn
  let := hs
  exact outer_solvable_eq_second c _ _ hne hfull

/-- Placement computes the order of the original ambient X, not just
its restriction to the offender actor. -/
theorem minimalSolvable_outer_card {G : Type*} [Group G] [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    Nat.card X = 3 := by
  have hXI := XFamily_le_star_offender L T z v hz S hS hX.1
  rw [← Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv,
    minimalSolvable_outer_eq_second L T z v hz S hS hX c,
    Nat.card_congr c.secondEquiv.toEquiv]
  exact Nat.card_zmod 3

private theorem twoPerfect_centralizes_cubic {E : Type*} [Group E] [Finite E]
    (A B : Subgroup E) [B.Normal] (hA : IsPPerfect 2 A) (hB : Nat.card B = 3) :
    ⁅A, B⁆ = ⊥ := by
  let : IsCyclic B := isCyclic_of_prime_card hB
  have hc : Nat.card (MulAut B) = 2 := by
    rw [IsCyclic.card_mulAut, hB]
    decide
  have hp : IsPGroup 2 (MulAut B) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let f : A →* MulAut B := MulAut.conjNormal.comp A.subtype
  have hf := hA.hom_eq_one_of_isPGroup hp f
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha b hb
  have he := congrArg (fun g : A →* MulAut B => g ⟨a, ha⟩ ⟨b, hb⟩) hf
  have he' : a * b * a⁻¹ = b := congrArg Subtype.val he
  have hh := congrArg (fun x : E => x * a) he'
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm

/-- The actual two-residual L_v centralizes X in the star actor.
This does not say that L_v fixes the moved plane of X in U_v. -/
theorem minimalSolvable_outer_commutator {G : Type*} [Group G] [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    ⁅starImage z v (Lv L v), X⁆ = ⊥ := by
  let : X.Normal := hX.1.2
  exact twoPerfect_centralizes_cubic _ _ (FactorArgument.starLv_twoPerfect L z v)
    (minimalSolvable_outer_card L T z v hz S hS hX c)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
