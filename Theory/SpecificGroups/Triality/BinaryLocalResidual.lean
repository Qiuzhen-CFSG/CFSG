module
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.ArmsParabolicPerfectAtTwo
public import Theory.SpecificGroups.Triality.ParabolicNormalizer
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The whole nonsolvable local subgroup in binary triality

The marked arm quotient is surjective. Its two-group kernel lies in the
positive Sylow, so adjoining that Sylow fills the arms parabolic. The
subgroup is therefore normal in the parabolic with a two-group quotient.
Perfectness of the actual arms parabolic at q = 2 makes this quotient
trivial. Sylow alignment preserves both the whole subgroup and its exact
normalizer, not only the isomorphism type of its two-core quotient.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--636; GLS3 §§2.3--2.6
for the genuine graph-field root parabolics. The local Cartan application
is in RankOneModuleGenericExceptionalCartanLocalBinaryArms.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryLocalSections
open Parabolics

/-- A proper perfect nonsolvable subgroup normalized by the full positive Sylow
is the entire arms parabolic, including its two-core. -/
theorem eq_arms_of_normalized
    (R : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : unipotent (binaryParameters 1 Nat.zero_lt_one) ≤ normalizer (R : Set _)) :
    R = parabolic (binaryParameters 1 Nat.zero_lt_one) .arms := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let L := localFactor P .arms
  let U := unipotent P
  obtain ⟨hRL,honto⟩ := arm_quotient_surjective R hne hns hn
  have he : parabolic P .arms = L := parabolic_arms_eq_localFactor_at_two P rfl rfl
  have hUL : U ≤ L := he ▸ (unipotent_le_borel P).trans (borel_le_parabolic P .arms)
  let q := QuotientGroup.mk' (pCore 2 L)
  have him : (R.subgroupOf L).map q = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨r,hr⟩ := honto y
    exact ⟨inclusion hRL r,r.property,hr⟩
  have hsup : R.subgroupOf L ⊔ pCore 2 L = ⊤ := by
    have hh := congrArg (comap q) him
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  have hcore : (pCore 2 L).map L.subtype ≤ U := by
    have hh := map_mono (f := L.subtype)
      (pCore_isPGroup.le_sylow_of_normal ((unipotentSylow P rfl).subtype hUL))
    change (pCore 2 L).map L.subtype ≤ (U.subgroupOf L).map L.subtype at hh
    rwa [map_subgroupOf_eq_of_le hUL] at hh
  have hjoin : R ⊔ U = L := by
    apply le_antisymm (sup_le hRL hUL)
    have hh := congrArg (map L.subtype) hsup
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRL,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm.le.trans (sup_le_sup_left hcore R)
  let R' := R.subgroupOf L
  let : R'.Normal := (normal_subgroupOf_iff_le_normalizer hRL).mpr (by
    change L ≤ normalizer (R : Set _)
    rw [←hjoin]
    exact sup_le R.le_normalizer hn)
  let : Group.IsPerfect L := he ▸ parabolic_arms_isPerfect_at_two P rfl rfl
  have hgen : R' ⊔ U.subgroupOf L = ⊤ := by
    rw [←subgroupOf_sup hRL hUL,hjoin,subgroupOf_self]
  have hquot : IsPGroup 2 (L ⧸ R') := isPGroup_quotient_of_sup_eq_top R' (U.subgroupOf L)
    ((unipotentSylow P rfl).isPGroup'.comap_subtype) hgen
  let : Group.IsNilpotent (L ⧸ R') := hquot.isNilpotent
  have ht : R' = ⊤ := top_unique (le_of_isPerfect_of_solvable_quotient (⊤ : Subgroup L) R')
  exact (le_antisymm hRL (subgroupOf_eq_top.mp ht)).trans he.symm

/-- Aligning the actual Sylow marks the entire original subgroup as the
binary arms parabolic. No equality of unrelated field degrees is used. -/
theorem marked_arms {G : Type*} [Group G] [Finite G]
    (eG : G ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 G)
    (R : Subgroup G) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : (S : Subgroup G) ≤ normalizer (R : Set G)) :
    ∃ a : G ≃* BinaryCarrier 1 Nat.zero_lt_one,
      (S : Subgroup G).map a.toMonoidHom = unipotent (binaryParameters 1 Nat.zero_lt_one) ∧
      R.map a.toMonoidHom = parabolic (binaryParameters 1 Nat.zero_lt_one) .arms := by
  obtain ⟨a,ha,_,_,_⟩ := marked_arm_quotient eG S R hne hns hn
  let b := a.subgroupMap R
  let : Group.IsPerfect (R.map a.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  refine ⟨a,ha,eq_arms_of_normalized _ ?_ ?_ ?_⟩
  · intro ht
    apply hne
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective _ a.surjective]
    exact ht
  · intro hs
    exact hns (@Group.isSolvable_of_isSolvable_injective R (R.map a.toMonoidHom)
      _ _ b.toMonoidHom b.injective hs)
  · rw [←ha]
    exact (map_mono hn).trans (le_normalizer_map a.toMonoidHom)

/-- Such a subgroup contains the full supplied Sylow and is self-normalizing
inside the binary triality carrier. -/
theorem sylow_le_and_normalizer_eq {G : Type*} [Group G] [Finite G]
    (eG : G ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 G)
    (R : Subgroup G) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : (S : Subgroup G) ≤ normalizer (R : Set G)) :
    (S : Subgroup G) ≤ R ∧ normalizer (R : Set G) = R := by
  obtain ⟨a,hS,hR⟩ := marked_arms eG S R hne hns hn
  constructor
  · apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    rw [hS,hR]
    exact (unipotent_le_borel _).trans (borel_le_parabolic _ .arms)
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_equiv_normalizer_eq,hR,normalizer_parabolic_binary _ rfl]

end Triality.Standard.BinaryLocalSections
