module

public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.PGroup.Omega
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Preparation

/-!
# The cyclic three-core and the first omega subgroup

In a group of three-rank at most two, a subgroup of three-rank two contains
every cubic element in its centralizer: an external cubic element would
adjoin an independent third generator to an elementary nine. Components
centralize the three-core. If the component is normal with center of order
three, its center therefore equals the embedded first omega subgroup of the
three-core. Every elementary subgroup of that core has order at most three,
so the odd-prime cyclicity criterion makes the core cyclic.

`LiftedCover` is the remaining structural construction target. It deliberately
contains neither cyclicity nor the omega equality nor centralizer oddness.
It is not an earlier-source assumption or a proved consequence of B.5.3.
Source: Aschbacher–Smith, A.3.18, pp.51–53, and B.5.7, pp.105–106,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
universe u
variable {H : Type*} [Group H] [Finite H]

/-- A component centralizes the normal three-core. -/
theorem threeCore_centralizes_component {M : Subgroup H} (hM : IsComponent H M) :
    pCore 3 H ≤ centralizer (M : Set H) := by
  rcases hM.normal_dichotomy (pCore 3 H) with h | h
  · let := hM.2
    let : Group.IsNilpotent (pCore 3 H) := (pCore_isPGroup (p := 3) (G := H)).isNilpotent
    let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective h)
    let : IsSimpleGroup (M ⧸ center M) := IsQuasisimple.simple
    let : Nontrivial M := (QuotientGroup.mk'_surjective (center M)).nontrivial
    exact (Group.IsPerfect.not_isSolvable M inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)

/-- The rank bound puts every cubic centralizer element in the component center. -/
theorem centralizer_cube_mem_center (M : Subgroup H)
    (hrM : 1 < primeRank 3 M) (hrH : primeRank 3 H ≤ 2)
    (x : H) (hx : x ∈ centralizer (M : Set H)) (hx3 : x ^ 3 = 1) :
    x ∈ (center M).map M.subtype := by
  have hxm : x ∈ M := by
    by_contra hxm
    have hx1 : x ≠ 1 := fun h => hxm (h ▸ M.one_mem)
    have ho : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    obtain ⟨E, hE, hcard⟩ := exists_elementary_nine_of_three_rank (by omega : 2 ≤ primeRank 3 M)
    let := hE
    let A := E.map M.subtype
    let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
    have hAM : A ≤ M := map_subtype_le E
    have hcardA : Nat.card A = 3 ^ 2 := by
      simpa only [A, card_map_of_injective M.subtype_injective] using hcard
    have hbound := IsElementaryAbelian.primeRank_ge_of_fixed_join A x ho
      (fun ha => hxm (hAM ha)) (by
        intro a ha
        exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp hx a (hAM ha))) hcardA
    omega
  refine ⟨⟨x, hxm⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro m
  exact Subtype.ext (mem_centralizer_iff.mp hx m m.property)

/-- A cubic component center is precisely first omega of the cyclic three-core. -/
theorem cyclic_threeCore_and_omega {M : Subgroup H} [M.Normal]
    (hM : IsComponent H M) (hrM : 1 < primeRank 3 M)
    (hrH : primeRank 3 H ≤ 2) (hz : Nat.card (center M) = 3) :
    IsCyclic (pCore 3 H) ∧
      (omega₁ (pCore 3 H) (p := 3)).map (pCore 3 H).subtype =
        (center M).map M.subtype := by
  let Z := (center M).map M.subtype
  have hZcard : Nat.card Z = 3 := by
    simpa only [Z, card_map_of_injective M.subtype_injective] using hz
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hZle : Z ≤ pCore 3 H := le_sSup ⟨inferInstance, hZp⟩
  have hZpow (z : Z) : z ^ 3 = 1 := by
    rw [← hZcard]
    exact pow_card_eq_one'
  have homega : (omega₁ (pCore 3 H) (p := 3)).map (pCore 3 H).subtype = Z := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply (Subgroup.closure_le _).mpr
      intro x hx
      change (x : H) ∈ Z
      apply centralizer_cube_mem_center M hrM hrH x
        (threeCore_centralizes_component hM x.property)
      have hp : x ^ 3 = 1 := by
        change x ^ (3 ^ 1) = 1 at hx
        simpa only [pow_one] using hx
      exact congrArg (pCore 3 H).subtype hp
    · intro z hzZ
      refine ⟨⟨z, hZle hzZ⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      change (⟨z, hZle hzZ⟩ : pCore 3 H) ^ (3 ^ 1) = 1
      apply Subtype.ext
      change z ^ 3 = 1
      exact congrArg (fun z : Z => (z : H)) (hZpow ⟨z, hzZ⟩)
  refine ⟨?_, homega⟩
  apply (pCore_isPGroup (p := 3) (G := H)).isCyclic_of_odd_of_elementary_card_le
    (by decide)
  intro E hE
  let := hE
  have hle : E.map (pCore 3 H).subtype ≤ Z := by
    rw [← homega]
    exact map_mono (elementaryAbelian_le_omega₁ (p := 3))
  have hcard := card_le_of_le hle
  simpa only [card_map_of_injective (pCore 3 H).subtype_injective, hZcard] using hcard

/-- Construction target for the source reduction preceding the involution
argument. All layer, image and Fitting equalities refer to this same cover.
The source producer must construct these fields from complete earlier inputs. -/
structure LiftedCover (K : GroupClass.{u}) (G : Type u) [Group G]
    (L : Subgroup G) where
  cover : PreparedCover K G
  lift : Subgroup cover.Cover
  component : IsComponent cover.Cover lift
  component_image : lift.map cover.projection = L
  lift_layer : componentLayer cover.Cover = lift
  layer : componentLayer G = L
  component_sqtk : IsSQTK K L
  fitting : generalizedFitting G = (L ⊔ pCore 3 G) ⊔ center G
  center_order : Nat.card (center lift) = 1 ∨ Nat.card (center lift) = 3

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
