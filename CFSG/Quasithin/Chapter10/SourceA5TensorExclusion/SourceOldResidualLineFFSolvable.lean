module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognition
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.TwoThreeSolvable
/-!
# Solvability of the original Cartan--Sylow subgroup

The source Borel is contained in the normalizer of the orbit Sylow
subgroup. Modulo the orbit two-core this normalizer lies over the Sylow
normalizer in A₅ × A₅, of order 144, and hence is solvable. The original
Sylow normalizes that entire subgroup, so adjoining the Cartan to the
Sylow remains solvable. Restriction and passage through any action map
preserve the same conclusion.

This supplies the solvable Sylow overgroup used in the three Lie-type
rows of Aschbacher--Smith 9.3.1, printed p.733. It makes no assumption
that the Cartan normalizes the original Sylow subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
variable {G : Type*} [Group G] [Finite G]
private theorem pair_lift_normalizer_solvable
    (q : G →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (S : Sylow 2 G) :
    Group.IsSolvable (normalizer (S : Set G)) := by
  let N := normalizer (S : Set G)
  let Q := S.mapSurjective hq
  let NQ := normalizer (Q : Set (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
  let f : N →* NQ := (q.comp N.subtype).codRestrict NQ (fun x =>
    (le_normalizer_map q) (mem_map_of_mem q x.property))
  have hfker : IsPGroup 2 f.ker :=
    (hk.comap_subtype (K := N)).to_le (fun x hx => congrArg Subtype.val hx)
  let : Group.IsNilpotent f.ker := hfker.isNilpotent
  let : Group.IsSolvable NQ := isSolvable_of_prime_dvd_card_eq_two_or_three NQ (by
    intro p hp hd
    have h6 : p ∣ 2 * 3 := hp.dvd_of_dvd_pow (hd.trans (show Nat.card NQ ∣ 6 ^ 4 by
      rw [Theory.AlternatingFive.pair_sylow_normalizer_card Q]
      decide))
    exact (hp.dvd_mul.mp h6).imp
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp)
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp))
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)
end CFSG.Quasithin.Chapter10.SourceOldResidualLineFF
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include D in
private theorem orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩

include m in
/-- The literal source Borel has a solvable Sylow extension. -/
theorem cartan_sylow_join_isSolvable (A : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) :
    Group.IsSolvable (A ⊔ (T : Subgroup G) : Subgroup G) := by
  let R := localOrbit T L
  let N := sourceOrbitSylowNormalizer T L
  have hNR : N ≤ R := inf_le_left
  obtain ⟨S,hS⟩ := orbit_sylow_intersection (D := D)
  let NR := normalizer (S : Set R)
  have hNsub : N.subgroupOf R = NR := by
    change (R ⊓ normalizer ((T : Subgroup G) ⊓ R : Set G)).subgroupOf R = _
    rw [inf_subgroupOf_left]
    change (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).subgroupOf R = NR
    rw [subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right)]
    have hh : ((T : Subgroup G) ⊓ R).subgroupOf R = (T : Subgroup G).subgroupOf R := by
      ext x
      exact ⟨fun h => h.1,fun h => ⟨h,x.property⟩⟩
    rw [hh,←hS]
    rfl
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp m.sylow_not_normalizes_component
  obtain ⟨q,hq,hk,_⟩ := source_a5_original_product_quotient D e
    m.sylow_not_normalizes_component ht htn
  let : Group.IsSolvable NR := SourceOldResidualLineFF.pair_lift_normalizer_solvable
    q hq (hk ▸ pCore_isPGroup) S
  let : Group.IsSolvable (N.subgroupOf R) := hNsub ▸ inferInstance
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hNR).toMonoidHom) (subgroupOfEquivOfLe hNR).surjective
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := le_normalizer_componentOrbit L T
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) := by
    have hTQ : (T : Subgroup G) ≤ normalizer ((T : Subgroup G) ⊓ R : Set G) :=
      (le_inf (T : Subgroup G).le_normalizer hTR).trans inf_normalizer_le_normalizer_inf
    exact (le_inf hTR (hTQ.trans (normalizer ((T : Subgroup G) ⊓ R : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (N ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes N (T : Subgroup G) hTN
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (sup_le_sup (hAB.trans (map_subtype_le _)) le_rfl))

include m in
/-- Restriction and any subsequent homomorphism retain the same solvable
Cartan--Sylow subgroup. This applies to the original Omega action quotient. -/
theorem cartan_sylow_image_join_isSolvable (A X : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hAX : A ≤ X) (hTX : (T : Subgroup G) ≤ X)
    {Y : Type*} [Group Y] (f : X →* Y) :
    Group.IsSolvable ((A.subgroupOf X).map f ⊔
      (((T.subtype hTX : Sylow 2 X) : Subgroup X).map f) : Subgroup Y) := by
  let : Group.IsSolvable (A ⊔ (T : Subgroup G) : Subgroup G) :=
    m.cartan_sylow_join_isSolvable A hAB
  have hAXT : A ⊔ (T : Subgroup G) ≤ X := sup_le hAX hTX
  let : Group.IsSolvable ((A ⊔ (T : Subgroup G)).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAXT).toMonoidHom) (subgroupOfEquivOfLe hAXT).injective
  have he : A.subgroupOf X ⊔ ((T.subtype hTX : Sylow 2 X) : Subgroup X) =
      (A ⊔ (T : Subgroup G)).subgroupOf X := (subgroupOf_sup hAX hTX).symm
  rw [←Subgroup.map_sup,he]
  exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
