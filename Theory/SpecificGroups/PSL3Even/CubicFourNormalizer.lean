module

public import Theory.SpecificGroups.PSL3Even.CubicFourNormalizer.NormalSubgroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Frattini.OmegaProducts
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The normal four-group screen for even PSL₃

The concrete upper unitriangular calculation is transported first to a marked
subgroup and then to every Sylow 2-subgroup of PSL₃(F). A normal noncentral
subgroup of order four forces |F|=2. The common-Sylow wrapper expresses
noncentrality through failure to centralize a second subgroup in that Sylow.

Source: Aschbacher–Smith, 2.4.32, printed p.547, paired A₃ screen. The ambient source argument
supplies normalization by the full inner Sylow subgroup; that assumption is
explicit here.
-/

public section
open scoped MatrixGroups
open Subgroup
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.CubicFourNormalizer

variable (F : Type*) [Field F] [Finite F]

/-- Transport the normal-four calculation along a specified UT₃ marking. -/
theorem field_card_two_of_marked_normal_four
    {G : Type*} [Group G] (S A : Subgroup G) (e : U F ≃* S)
    (hcard : Nat.card A = 4) (hAS : A ≤ S) (hSN : S ≤ Subgroup.normalizer A)
    (hne : ¬ A.subgroupOf S ≤ Subgroup.center S) : Nat.card F = 2 := by
  let D := (A.subgroupOf S).comap e.toMonoidHom
  have hmap : D.map e.toMonoidHom = A.subgroupOf S :=
    map_comap_eq_self_of_surjective e.surjective _
  let eD : D ≃* (A.subgroupOf S) :=
    (D.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hcardD : Nat.card D = 4 := by
    calc
      Nat.card D = Nat.card (A.subgroupOf S) := Nat.card_congr eD.toEquiv
      _ = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv
      _ = 4 := hcard
  have hn : (A.subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAS).mpr hSN
  let : D.Normal := hn.comap e.toMonoidHom
  have hnotcentralD : ¬ D ≤ Z F := by
    intro hD
    apply hne
    rw [← hmap, ← center_map_equiv e]
    exact map_mono (by simpa only [Z_eq_center] using hD)
  exact field_card_two_of_normal_four_noncentral F D hcardD hnotcentralD

/-- The projective endpoint for the paired A₃ screen. -/
theorem field_card_two_of_sylow_normal_four
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 PSL(3,F)) (A : Subgroup PSL(3,F))
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup PSL(3,F)))
    (hPN : (P : Subgroup PSL(3,F)) ≤ Subgroup.normalizer A)
    (hne : ¬ A.subgroupOf (P : Subgroup PSL(3,F)) ≤
      Subgroup.center (P : Subgroup PSL(3,F))) : Nat.card F = 2 := by
  let P₀ := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let e : U F ≃* P :=
    (Matrix.PSL3.LinearThree.unipotentEquiv F).trans (Sylow.equiv P₀ P)
  exact field_card_two_of_marked_normal_four F (P : Subgroup PSL(3,F)) A e
    hcard hAP hPN hne

/-- An ambient-center formulation, with the literal Sylow subtype map. -/
theorem field_card_two_of_sylow_normal_four_not_le_center
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 PSL(3,F)) (A : Subgroup PSL(3,F))
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup PSL(3,F)))
    (hPN : (P : Subgroup PSL(3,F)) ≤ Subgroup.normalizer A)
    (hne : ¬ A ≤ (Subgroup.center (P : Subgroup PSL(3,F))).map
      (P : Subgroup PSL(3,F)).subtype) : Nat.card F = 2 := by
  apply field_card_two_of_sylow_normal_four F hn hF P A hcard hAP hPN
  intro hcent
  apply hne
  intro a ha
  exact ⟨⟨a,hAP ha⟩,hcent ha,rfl⟩

/-- The common-Sylow hypothesis makes failure to centralize visible intrinsically. -/
theorem field_card_two_of_sylow_normal_four_not_centralize
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 PSL(3,F)) (A B : Subgroup PSL(3,F))
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup PSL(3,F)))
    (hBP : B ≤ (P : Subgroup PSL(3,F)))
    (hPN : (P : Subgroup PSL(3,F)) ≤ Subgroup.normalizer A)
    (hne : ¬ A ≤ Subgroup.centralizer (B : Set PSL(3,F))) : Nat.card F = 2 := by
  apply field_card_two_of_sylow_normal_four_not_le_center F hn hF P A hcard hAP hPN
  intro hcent
  apply hne
  intro a ha b hb
  obtain ⟨c,hc,rfl⟩ := hcent ha
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨b,hBP hb⟩)

/-- A literal commutator formulation for the paired A₃ source actors. -/
theorem field_card_two_of_sylow_normal_four_commutator_ne_bot
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 PSL(3,F)) (A B : Subgroup PSL(3,F))
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup PSL(3,F)))
    (hBP : B ≤ (P : Subgroup PSL(3,F)))
    (hPN : (P : Subgroup PSL(3,F)) ≤ Subgroup.normalizer A)
    (hne : ⁅A,B⁆ ≠ ⊥) : Nat.card F = 2 := by
  apply field_card_two_of_sylow_normal_four_not_centralize F hn hF P A B hcard hAP hBP hPN
  exact fun h => hne (commutator_eq_bot_iff_le_centralizer.mpr h)

end Matrix.PSL3Even.CubicFourNormalizer
