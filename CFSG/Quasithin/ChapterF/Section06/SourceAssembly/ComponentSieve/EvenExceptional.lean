module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Alternating
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Exceptional and symplectic entries in the small-Sylow sieve

The symplectic four-space, G₂, triality and Ree carriers have a factor sixteen
in their actual orders, using their order formulas or the certified positive
root subgroups. The binary derived G₂ carrier and the Tits carrier have the
same obstruction by their exact orders. The remaining binary symplectic
commutator is the actual A₆ carrier and is excluded by its order-four element.
Thus the original Theorem C rank-two list reduces to its linear constructor.

Source: Aschbacher--Smith, F.6.17, printed p.309, using the actual source
Theorem C model list in A.2.4. All carrier comparisons retain the quotient
and derived-subgroup conventions in that list.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve

open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02
open Theory.GroupTheory Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem sixteen_dvd_binary_power {f d : ℕ} (h : 4 ≤ f * d) :
    16 ∣ (2 ^ f) ^ d := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

/-- The genuine even symplectic model has too large a two-part. -/
theorem not_symplectic_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSp G 2 (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_sp, hF]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (sixteen_dvd_binary_power (by omega)) _) _

/-- The actual split-octonion carrier has too large a two-part. -/
theorem not_g2_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : IsG2At G (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (sixteen_dvd_binary_power (by omega)) _) _

/-- The descended positive root subgroup of the actual triality carrier
already has order divisible by sixteen. -/
theorem not_triality_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    {f : ℕ} (hf : 1 ≤ f)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ f) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f hf).mp hmodel
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  apply dvd_trans _ (Triality.Standard.Parabolics.unipotent
    (Triality.Standard.binaryParameters f hf)).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl]
  change 16 ∣ (2 ^ f) ^ 12
  exact sixteen_dvd_binary_power (by omega)

/-- The literal Ree positive root subgroup excludes every full Ree carrier,
including its binary endpoint. -/
theorem not_ree_f4_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    (m : ℕ) (e : G ≃* ReeF4.Model m) : False := by
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  apply dvd_trans _ (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent]
  exact sixteen_dvd_binary_power (by omega)

/-- The commutator of the actual binary projective symplectic carrier is A₆,
which has no elementary Sylow two-subgroup. -/
theorem not_symplectic_derived_of_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hns : ¬ Group.IsSolvable G)
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  have hn := alternating_degree_of_small_elementary_sylow P hP hns (by decide : 6 ≤ 8)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
  norm_num at hn

/-- The binary G₂ commutator has actual order 6048. -/
theorem not_g2_derived_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv,
    Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  norm_num

/-- The actual Parrott presentation has order 17971200. -/
theorem not_tits_of_small_sylow (P : Sylow 2 G) (hP : Nat.card P ≤ 8)
    (e : G ≃* Tits.ParrottGroup) : False := by
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
  norm_num

/-- Applied to the literal rank-two source constructors, the small elementary
Sylow leaves only the linear three-dimensional family. -/
theorem linear_of_theoremC_rankTwo_small_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] (hP : Nat.card P ≤ 8)
    (hns : ¬ Group.IsSolvable G) {f : ℕ} (hmodel : IsTheoremCRankTwoModel G f) :
    1 ≤ f ∧ ClassicalGroup.IsPSL G 3 (2 ^ f) := by
  cases hmodel with
  | linear hf iso => exact ⟨hf, iso⟩
  | symplectic hf iso => exact (not_symplectic_of_small_sylow P hP hf iso).elim
  | g2 hf iso => exact (not_g2_of_small_sylow P hP hf iso).elim
  | triality hf iso => exact (not_triality_of_small_sylow P hP hf iso).elim
  | ree_f4 m _ _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_ree_f4_of_small_sylow P hP m e).elim
  | symplectic_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_symplectic_derived_of_small_elementary_sylow P hP hns e).elim
  | g2_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_g2_derived_of_small_sylow P hP e).elim
  | tits _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_tits_of_small_sylow P hP e).elim

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
