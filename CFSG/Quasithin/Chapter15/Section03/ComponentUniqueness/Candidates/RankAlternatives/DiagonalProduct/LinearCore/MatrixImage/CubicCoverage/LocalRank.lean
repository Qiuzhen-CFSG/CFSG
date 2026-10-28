module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OuterActor
public import Theory.Quasithin.Rank


/-!
# Three-rank of the actual component action

The normalizer used here is relative to the source overgroup I. Its action on
L/O₂(L), in any supplied coordinates, has kernel C_{I ∩ N(L)}(L): perfectness
and the central two-core identify the section centralizer with the ordinary
centralizer. The existing full-rank centralizer theorem makes this kernel
prime to three. Thus the action image has three-rank at most two and contains
all inner automorphisms of the quotient model.

Consequently an outer cubic actor in this image cannot centralize an elementary
abelian subgroup of order nine in the inner automorphisms. The fixed subgroup
and actor would generate an elementary abelian subgroup of order 27. This
argument includes central two-covers and keeps the original quotient map.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18,
printed pp.51--52, used in the last paragraph of 15.3.37, printed p.1135.
The concrete field-automorphism fixed subgroup is a separate obligation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage.CubicCoverage
variable {G H : Type*} [Group G] [Group H]

/-- The quotient action of the normalizer inside the actual overgroup I. -/
def localAction (I L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* H) :
    (I ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut H :=
  quotientAction inf_le_right e

/-- Every inner automorphism is induced by an element of the actual component. -/
theorem inner_le_localAction_range {I L : Subgroup G} (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* H) : MulAut.innerSubgroup H ≤ (localAction I L e).range := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨l, rfl⟩ := quotientMap_surjective e z
  exact ⟨⟨l, hLI l.property, L.le_normalizer l.property⟩,
    quotientAction_on_component inf_le_right e _ l.property⟩

/-- Restricting the relative normalizer action gives the original Y₊ action. -/
theorem localAction_on_yplus {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* H) (x : d.Yplus) :
    localAction I L e ⟨x, (h.theta_eq ▸ (theta_le (d.M ⊓ I)).trans inf_le_right) x.property,
      hn x.property⟩ = quotientAction hn e x := by
  rfl

variable [Finite G]

/-- The action kernel is prime to three, also for the central two-cover branch. -/
theorem localAction_kernel_coprime {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (e : (L ⧸ pCore 2 L) ≃* H) :
    Nat.Coprime 3 (Nat.card (localAction I L e).ker) := by
  let eL := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
  have hcore : pCore 2 L ≤ center L := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (pCore_map_iso 2 eL).symm ▸ hx
    apply mem_center_iff.mpr
    intro l
    have he := congrArg eL
      (mem_center_iff.mp ((component_center_eq_twoCore h.component h.odd_core).ge hz)
        (eL.symm l))
    change l * eL z = eL z * l
    simpa only [map_mul, eL.apply_symm_apply] using he
  let N := I ⊓ normalizer (L : Set G)
  have hk : (localAction I L e).ker.map N.subtype ≤ I ⊓ centralizer (L : Set G) := by
    rw [localAction, quotientAction_ker inf_le_right e hcore]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.property.1, ha⟩
  have hc := local_centralizer_three_coprime h.component_le h.component h.odd_core
    h.rank_component.ge h.rank_overgroup
  have hc' := hc.of_dvd_right (card_dvd_of_le hk)
  simpa only [Subgroup.card_map_of_injective N.subtype_injective] using hc'

/-- Factoring out the actual action kernel preserves the source three-rank bound. -/
theorem localAction_range_rank {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (e : (L ⧸ pCore 2 L) ≃* H) :
    primeRank 3 (localAction I L e).range ≤ 2 := by
  let f := localAction I L e
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hk : Nat.Coprime 3 (Nat.card f.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact localAction_kernel_coprime h e
  have hr := primeRank_le_of_surjective_of_coprime 3 f.rangeRestrict
    f.rangeRestrict_surjective hk
  have hi := Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (inf_le_left : I ⊓ normalizer (L : Set G) ≤ I)) (inclusion_injective _)
  exact hr.trans (hi.trans h.rank_overgroup)

/-- An outer cubic actor cannot fix an inner elementary abelian nine-group. -/
theorem quotientAction_no_fixed_nine {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* H) (x : d.Yplus) (hx : orderOf x = 3)
    (ho : quotientAction hn e x ∉ MulAut.innerSubgroup H)
    (E : Subgroup (MulAut H)) [IsElementaryAbelian 3 E]
    (hE : E ≤ MulAut.innerSubgroup H) (hc : Nat.card E = 9)
    (hf : E ≤ centralizer ({quotientAction hn e x} : Set (MulAut H))) : False := by
  let A := (localAction I L e).range
  let : Finite A := Finite.of_surjective (localAction I L e).rangeRestrict
    (localAction I L e).rangeRestrict_surjective
  have hEA : E ≤ A := hE.trans (inner_le_localAction_range h.component_le e)
  have hxA : quotientAction hn e x ∈ A :=
    ⟨_, localAction_on_yplus h hn e x⟩
  let a : A := ⟨quotientAction hn e x, hxA⟩
  let D := E.subgroupOf A
  let eD : D ≃* E := subgroupOfEquivOfLe hEA
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.subgroupOf hEA
  have hcD : Nat.card D = 3 ^ 2 := (Nat.card_congr eD.toEquiv).trans hc
  have ha : orderOf a = 3 := by
    rw [← Subgroup.orderOf_coe]
    apply orderOf_eq_prime
    · change quotientAction hn e x ^ 3 = 1
      rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    · change quotientAction hn e x ≠ 1
      exact fun he => ho (he.symm ▸ (MulAut.innerSubgroup H).one_mem)
  have haD : a ∉ D := fun hm => ho (hE hm)
  have hfD : D ≤ centralizer ({a} : Set A) := by
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hf hz))
  have hr := IsElementaryAbelian.primeRank_ge_of_fixed_join D a ha haD hfD hcD
  have hu : primeRank 3 A ≤ 2 := localAction_range_rank h e
  omega

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage.CubicCoverage
