module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# A normal quasisimple subgroup modulo its centralizer

For a normal quasisimple subgroup `L` of a finite group `G`, its image in
`G/C_G(L)` is isomorphic to `L/Z(L)` and has trivial centralizer. If `G/L`
is a two-group, that image is the entire generalized Fitting subgroup.

The first isomorphism theorem identifies the component image. Perfectness
lifts its centralizer through the quotient, and the component dichotomy
then kills the two-core. The quasisimple two-quotient theorem finishes.

This is the intrinsic quotient step in Aschbacher--Smith, *The Classification
of Quasithin Groups*, 15.3.41(1), printed p.1138 (1 March 2004 manuscript).
-/

@[expose] public section

namespace Theory.GroupTheory

open Subgroup

variable {G : Type*} [Group G] (L : Subgroup G) [L.Normal]

/-- The actual quotient by the centralizer of the normal subgroup. -/
abbrev CentralizerQuotient := G ⧸ centralizer (L : Set G)

def centralizerQuotientMap : G →* CentralizerQuotient L :=
  QuotientGroup.mk' (centralizer (L : Set G))

/-- The component image, with its inherited subgroup structure. -/
def centralizerQuotientComponent : Subgroup (CentralizerQuotient L) :=
  L.map (centralizerQuotientMap L)

theorem centralizerQuotient_component_ker :
    ((centralizerQuotientMap L).subgroupMap L).ker = center L := by
  ext x
  change ((centralizerQuotientMap L).subgroupMap L) x = 1 ↔ _
  rw [Subtype.ext_iff]
  change QuotientGroup.mk (x : G) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_center_iff, mem_centralizer_iff]
  constructor
  · intro h y
    exact Subtype.ext (h y y.property)
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)

/-- An actual isomorphism, not just a simple-family identification. -/
noncomputable def centralizerQuotientComponentEquiv :
    L ⧸ center L ≃* centralizerQuotientComponent L :=
  (QuotientGroup.quotientMulEquivOfEq (centralizerQuotient_component_ker L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((centralizerQuotientMap L).subgroupMap_surjective L))

theorem centralizerQuotientComponent_simple [IsQuasisimple L] :
    IsSimpleGroup (centralizerQuotientComponent L) :=
  (MulEquiv.isSimpleGroup_congr (centralizerQuotientComponentEquiv L)).mp
    IsQuasisimple.simple

theorem centralizerQuotientComponent_centralizer [Group.IsPerfect L] :
    centralizer (centralizerQuotientComponent L : Set (CentralizerQuotient L)) = ⊥ := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (centralizer (L : Set G)))
  rw [centralizerQuotientComponent, centralizerQuotientMap,
    comap_centralizer_map_eq_of_perfect]
  · exact (QuotientGroup.ker_mk' _).symm
  · rw [QuotientGroup.ker_mk']

private theorem pCore_eq_bot_of_quasisimple_centralizer [Finite G] [IsQuasisimple L]
    (hc : centralizer (L : Set G) = ⊥) : pCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hL.normal_dichotomy (pCore 2 G) with hle | hcomm
  · let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let : Group.IsNilpotent L := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · apply le_bot_iff.mp
    rw [commutator_comm] at hcomm
    exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hc.le

/-- The simple component is all of `F*` when the original quotient is a two-group. -/
theorem centralizerQuotient_generalizedFitting [Finite G] [IsQuasisimple L]
    (hquot : IsPGroup 2 (G ⧸ L)) :
    generalizedFitting (CentralizerQuotient L) = centralizerQuotientComponent L := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : D.Normal := (inferInstance : L.Normal).map q hq
  let : IsSimpleGroup D := centralizerQuotientComponent_simple L
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap L)
    (q.subgroupMap_surjective L)
  have hp : IsPGroup 2 (CentralizerQuotient L ⧸ D) :=
    hquot.of_surjective (QuotientGroup.map L D q (le_comap_map q L))
      (QuotientGroup.map_surjective_of_surjective L D q
        ((QuotientGroup.mk'_surjective D).comp hq) (le_comap_map q L))
  exact generalizedFitting_eq_of_quasisimple_two_quotient D hp
    (pCore_eq_bot_of_quasisimple_centralizer D
      (centralizerQuotientComponent_centralizer L))

end Theory.GroupTheory
