module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.GroupTheory.QuasithinBasic

/-!
# Normal elementary subgroups of the marked outer Mathieu vertices

A normal elementary abelian two-subgroup of the involution-centralizer vertex
lies in its two-core. Every involution of that core belongs to the inner M₁₂,
so the existing two-rank bound for M₁₂ bounds this subgroup by three.

The natural-four normalizer vertex has trivial center: a central element lies
in the common Sylow subgroup and hence is either the identity or the marked
involution. The latter would place the entire second vertex in the
common Sylow subgroup, contradicting their respective orders 384 and 128.

These statements isolate the vertex orientation needed in Aschbacher--Smith,
14.6.10(4), printed p.1028; compare 14.5.5, printed p.1014, refs/quasithin.pdf.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open Subgroup Theory.GroupTheory

/-- A normal elementary subgroup of the involution-centralizer parabolic
has its literal ambient image in the inner M₁₂. -/
theorem normal_elementary_image_le_inner (E : Subgroup firstParabolic)
    [E.Normal] [IsElementaryAbelian 2 E] : E.map firstParabolic.subtype ≤ inner := by
  have hcore : E ≤ pCore 2 firstParabolic :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 E⟩
  rintro x ⟨y, hy, rfl⟩
  have hycore : y.val ∈ outerCore := by
    have hh := (intrinsicCoreEquiv innerModel ⟨y, hcore hy⟩).property
    rwa [intrinsicCoreEquiv_coe] at hh
  have hsq : y.val ^ 2 = 1 := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) (⟨y,hy⟩ : E)
    exact congrArg (fun e : E => e.val.val) hh
  exact quaternionCore_le_inner innerModel
    (outerCore_square_one_mem_quaternionCore innerModel y.val hycore hsq)

/-- A normal elementary subgroup of C(z) has two-rank at most three. -/
theorem normal_elementary_primeRank_le_three (E : Subgroup firstParabolic)
    [E.Normal] [IsElementaryAbelian 2 E] : primeRank 2 E ≤ 3 := by
  let A := E.map firstParabolic.subtype
  have hA : A ≤ inner := normal_elementary_image_le_inner E
  let e : E ≃* A.subgroupOf inner :=
    (E.equivMapOfInjective firstParabolic.subtype firstParabolic.subtype_injective).trans
      (subgroupOfEquivOfLe hA).symm
  have hr : primeRank 2 inner ≤ 3 := by
    rw [← primeRank_equiv 2 innerModel.equiv]
    exact m12_twoRank_le_three
  rw [primeRank_equiv 2 e]
  exact (primeRank_le_of_injective 2 (A.subgroupOf inner).subtype
    (A.subgroupOf inner).subtype_injective).trans hr

/-- The generator-rank form of the same elementary bound. -/
theorem normal_elementary_rank_le_three (E : Subgroup firstParabolic)
    [E.Normal] [IsElementaryAbelian 2 E] : Group.rank E ≤ 3 := by
  have ht := (⊤ : Subgroup E).rank_le_primeRank 2
    ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤)
  rw [Group.rank_congr Subgroup.topEquiv] at ht
  exact ht.trans (normal_elementary_primeRank_le_three E)

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

namespace Sporadic.Mathieu.M12ExceptionalExtension
open Subgroup

private theorem center_eq_bot_of_center_inf {A : Type*} [Group A]
    (K L : Subgroup A) (w : A) (hw : w ∈ K)
    (hL : ∀ a : A, a ∈ L ↔ a * w = w * a)
    (hc : ∀ g : (L ⊓ K : Subgroup A), g ∈ center (L ⊓ K : Subgroup A) →
      (g : A) = 1 ∨ (g : A) = w)
    (hn : ¬ K ≤ L) : center K = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  have hgw : w * g.val = g.val * w := congrArg (fun x : K => x.val)
    ((mem_center_iff.mp hg) ⟨w, hw⟩)
  have hfirst : g.val ∈ L := (hL g.val).mpr hgw.symm
  let gt : (L ⊓ K : Subgroup A) := ⟨g.val, hfirst, g.property⟩
  have hgt : gt ∈ center (L ⊓ K : Subgroup A) := mem_center_iff.mpr (fun x => Subtype.ext
    (congrArg (fun y : K => y.val) ((mem_center_iff.mp hg) ⟨x.val, x.property.2⟩)))
  rcases hc gt hgt with hone | hz
  · exact mem_bot.mpr (Subtype.ext hone)
  · apply False.elim
    apply hn
    intro a ha
    apply (hL a).mpr
    have h := congrArg (fun x : K => x.val) ((mem_center_iff.mp hg) ⟨a, ha⟩)
    change a * g.val = g.val * a at h
    change g.val = w at hz
    rwa [hz] at h

/-- The natural-four normalizer has trivial center. This distinguishes it
from the involution-centralizer vertex of the marked amalgam. -/
theorem secondParabolic_center_eq_bot : center secondParabolic = ⊥ := by
  apply center_eq_bot_of_center_inf secondParabolic firstParabolic z
    SecondCoordinates.z_mem_overlap.2 (fun _ => mem_centralizer_singleton_iff)
    (SecondCoordinates.center_mem innerModel)
  intro h
  have hl : secondParabolic ≤ overlap := le_inf h le_rfl
  have hc := card_le_of_le hl
  rw [SecondCoordinates.card_secondParabolic innerModel,
    SecondCoordinates.card_overlap innerModel] at hc
  omega

end Sporadic.Mathieu.M12ExceptionalExtension

namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open Subgroup

/-- The bound survives a local-group identification with the marked
involution-centralizer parabolic. -/
theorem normal_elementary_rank_le_three_of_equiv {P : Type*} [Group P] [Finite P]
    (e : P ≃* firstParabolic) (E : Subgroup P)
    [E.Normal] [IsElementaryAbelian 2 E] : Group.rank E ≤ 3 := by
  let A := E.map e.toMonoidHom
  let : A.Normal := (inferInstance : E.Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  rw [Group.rank_congr (e.subgroupMap E)]
  exact normal_elementary_rank_le_three A

/-- The two-rank form transported through a local-group identification. -/
theorem normal_elementary_primeRank_le_three_of_equiv {P : Type*} [Group P] [Finite P]
    (e : P ≃* firstParabolic) (E : Subgroup P)
    [E.Normal] [IsElementaryAbelian 2 E] : primeRank 2 E ≤ 3 := by
  let A := E.map e.toMonoidHom
  let : A.Normal := (inferInstance : E.Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  rw [Theory.GroupTheory.primeRank_equiv 2 (e.subgroupMap E)]
  exact normal_elementary_primeRank_le_three A

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

