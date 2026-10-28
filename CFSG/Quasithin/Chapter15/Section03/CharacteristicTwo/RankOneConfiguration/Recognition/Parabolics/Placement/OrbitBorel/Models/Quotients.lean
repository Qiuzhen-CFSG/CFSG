module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization.Models

/-!
# Comparing the intrinsic and Thompson component quotients

The intrinsic two-core of the selected C-component lies in the two-core of I
by subnormality. The star quotient is two-reduced, so its quotient map kills
that core. Thus the component star map factors through L/O₂(L), without
assuming that L is normal in I. The full nonnormal-component list makes
L/O₂(L) centerless; together with the supplied quasisimplicity this gives
simplicity. Its nontrivial star image is therefore isomorphic to it.

These comparisons preserve the actual maps and all four nonnormal model
alternatives. They do not assert the remaining intersection with B.5.6.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed pp.503–504, and the first paragraph of 15.3.27, printed p.1130.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual star projection kills O₂(I), since its image is two-reduced. -/
theorem ambient_twoCore_le_starMap_ker (d : LocalData G) {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    pCore 2 I ≤ (d.starMap I).ker := by
  have hm : (pCore 2 I).map (d.starMap I) ≤ pCore 2 (d.Star I) :=
    le_sSup ⟨(inferInstance : (pCore 2 I).Normal).map _ (QuotientGroup.mk'_surjective _),
      pCore_isPGroup.map _⟩
  exact (Subgroup.map_eq_bot_iff _).mp
    (le_bot_iff.mp (hm.trans_eq (d.star_twoCore_eq_bot hS hZS)))

/-- Subnormality, rather than relative normality, suffices for the component
map to kill its intrinsic two-core. -/
theorem component_twoCore_le_starMap_ker (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    pCore 2 c.L ≤ (d.componentStarMap (component_le c)).ker := by
  let B := c.L.subgroupOf I
  let e : c.L ≃* B := (subgroupOfEquivOfLe (component_le c)).symm
  have hBI := pCoreIn_le_of_subnormal 2
    (LocalData.thompson_component_in c.le_thompson c.component).subnormal
  intro x hx
  have hxB : e x ∈ pCore 2 B := by
    rw [← pCore_map_iso 2 e]
    exact mem_map_of_mem _ hx
  have hxI : (e x : I) ∈ pCore 2 I := hBI (mem_map_of_mem B.subtype hxB)
  apply Subtype.ext
  exact ambient_twoCore_le_starMap_ker d hS hZS hxI

/-- The genuine surjection from the intrinsic two-core quotient to L*. -/
noncomputable def componentQuotientStarMap (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    (c.L ⧸ pCore 2 c.L) →* d.starImage I c.L :=
  QuotientGroup.lift (pCore 2 c.L) (d.componentStarMap (component_le c))
    (component_twoCore_le_starMap_ker d c hS hZS)

/-- Surjectivity retains the selected component, not merely its central quotient. -/
theorem componentQuotientStarMap_surjective (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    Function.Surjective (componentQuotientStarMap d c hS hZS) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (d.componentStarMap_surjective (component_le c)) _

omit [Finite G] in
/-- Every nonnormal model is simple here; the quasisimple input rules out
solvable small parameters in the odd-prime PSL₂ branch. -/
theorem nonnormal_component_quotient_isSimple (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hm : NonnormalCComponentModel (c.L ⧸ pCore 2 c.L)) :
    IsSimpleGroup (c.L ⧸ pCore 2 c.L) := by
  let Q := c.L ⧸ pCore 2 c.L
  let : IsQuasisimple Q := c.core_quotient_quasisimple
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have hz : center Q = ⊥ :=
    Chapter15.Section03.ComponentIntersection.CoreNormalization.nonnormalModel_center_eq_bot
      hm (Group.IsPerfect.not_isSolvable Q)
  let e : (Q ⧸ center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

/-- Under the nonnormal model list, the factored star map is an actual
isomorphism. Neither normality nor Y₊ containment is assumed. -/
noncomputable def nonnormalComponentQuotientEquivStar (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hm : NonnormalCComponentModel (c.L ⧸ pCore 2 c.L)) :
    (c.L ⧸ pCore 2 c.L) ≃* d.starImage I c.L := by
  let := nonnormal_component_quotient_isSimple d c hm
  let : IsQuasisimple (d.starImage I c.L) := c.star_quasisimple
  let : IsSimpleGroup ((d.starImage I c.L) ⧸ center (d.starImage I c.L)) :=
    IsQuasisimple.simple
  let : Nontrivial (d.starImage I c.L) :=
    (QuotientGroup.mk'_surjective (center (d.starImage I c.L))).nontrivial
  let f := componentQuotientStarMap d c hS hZS
  have hf : Function.Surjective f := componentQuotientStarMap_surjective d c hS hZS
  have hinj : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases f.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have he : f = 1 := MonoidHom.ker_eq_top_iff.mp ht
      obtain ⟨x, hx⟩ := exists_ne (1 : d.starImage I c.L)
      obtain ⟨y, rfl⟩ := hf x
      exact (hx (by rw [he]; rfl)).elim
  exact MulEquiv.ofBijective f ⟨hinj, hf⟩

/-- The comparison agrees with the actual star map on each component element. -/
theorem nonnormalComponentQuotientEquivStar_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hm : NonnormalCComponentModel (c.L ⧸ pCore 2 c.L)) (l : c.L) :
    nonnormalComponentQuotientEquivStar d c hS hZS hm
      (QuotientGroup.mk' (pCore 2 c.L) l) = d.componentStarMap (component_le c) l := rfl

/-- The full nonnormal list transfers to the literal star component. -/
theorem component_star_nonnormal_model {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    NonnormalCComponentModel (d.starImage I c.L) := by
  have hm := (component_orbit_index_and_model earlier hG d hI c hn).2
  exact hm.of_mulEquiv (nonnormalComponentQuotientEquivStar d c hS hZS hm).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
