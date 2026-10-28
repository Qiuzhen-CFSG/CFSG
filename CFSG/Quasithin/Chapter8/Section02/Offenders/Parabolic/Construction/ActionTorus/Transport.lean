module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient
public import Theory.GroupTheory.OddSubgroupLift

/-!
# The two different images of the selected local normalizer

Source: Aschbacher–Smith, Proposition 8.2.2(8), printed pp.714–715,
and Lemma E.2.14(9), printed pp.226–227.

The maps from M ∩ I to its automizer and to I* are kept literal. A
model centralizer bound makes the action kernel a two-group. Schur–Zassenhaus
then lifts every odd subgroup of the action image. Its image in I* has the
same order because the kernel of the second map is also a two-group.
Neither map is factored through the other: O₂(I) can act nontrivially on V.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE
variable {G : Type*} [Group G]

def selectedStarMap (M I : Subgroup G) : ↥(M ⊓ I) →* Star M I :=
  (QuotientGroup.mk' (localCore M I)).comp (inclusion inf_le_right)

def selectedActionMap (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G)) :
    ↥(M ⊓ I) →* inducedAutomizer V (M ⊓ I) :=
  (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hn)).codRestrict _
    (fun x => ⟨⟨x, hn x.property⟩, x.property, rfl⟩)

theorem selectedActionMap_surjective (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G)) :
    Function.Surjective (selectedActionMap M I V hn) := by
  rintro ⟨a, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem selectedActionMap_ker (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G)) :
    (selectedActionMap M I V hn).ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) := by
  rw [selectedActionMap, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker,
    MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker]
  rfl

theorem selectedStarMap_ker_two (M I : Subgroup G)
    (hc : localCore M I = pCore 2 I) : IsPGroup 2 (selectedStarMap M I).ker := by
  have he : (selectedStarMap M I).ker =
      (pCore 2 I).comap (inclusion (show M ⊓ I ≤ I from inf_le_right)) := by
    rw [selectedStarMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hc]
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

/-- The model fact concerns only the centralizer of V* in the marked Borel.
Its preimage has two-group kernel, which controls the different action kernel. -/
theorem selectedActionMap_ker_two (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G))
    (hc : localCore M I = pCore 2 I)
    (hC : IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I)))) :
    IsPGroup 2 (selectedActionMap M I V hn).ker := by
  apply (hC.comap_of_ker_isPGroup (selectedStarMap M I)
    (selectedStarMap_ker_two M I hc)).to_le
  rw [selectedActionMap_ker]
  intro x hx
  refine ⟨?_, ?_⟩
  · exact mem_map_of_mem _ x.property.1
  · rintro _ ⟨v, hv, rfl⟩
    change QuotientGroup.mk' (localCore M I) v *
        QuotientGroup.mk' (localCore M I) ⟨x.val, x.property.2⟩ =
        QuotientGroup.mk' (localCore M I) ⟨x.val, x.property.2⟩ * QuotientGroup.mk' (localCore M I) v
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx v.val hv)

private theorem injective_on_odd_subgroup {D Q : Type*} [Group D] [Finite D] [Group Q]
    (f : D →* Q) (hker : IsPGroup 2 f.ker) (U : Subgroup D)
    (hodd : Odd (Nat.card U)) : Function.Injective (f.comp U.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxker : (x : D) ∈ f.ker := hx
  obtain ⟨n, hn⟩ := hker ⟨x, hxker⟩
  have hpow : x ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun y : f.ker => (y : D)) hn)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_left.pow_left n) (orderOf_dvd_of_pow_eq_one hpow)
    (orderOf_dvd_natCard x))

/-- A lift has exactly the original action image and the same order in I*.
No containment between the two kernels is used. -/
theorem selected_odd_lift [Finite G] (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G))
    (hc : localCore M I = pCore 2 I)
    (hC : IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I))))
    (X : Subgroup (inducedAutomizer V (M ⊓ I))) (ho : Odd (Nat.card X)) :
    ∃ D : Subgroup ↥(M ⊓ I),
      D.map (selectedActionMap M I V hn) = X ∧
      Function.Injective ((selectedStarMap M I).comp D.subtype) ∧
      Nat.card (D.map (selectedStarMap M I)) = Nat.card X ∧
      Nat.card D = Nat.card X := by
  obtain ⟨D, hD, _, hcard, _⟩ := (selectedActionMap M I V hn).exists_odd_subgroup_lift
    (selectedActionMap_surjective M I V hn) (selectedActionMap_ker_two M I V hn hc hC) X ho
  have hi := injective_on_odd_subgroup (selectedStarMap M I)
    (selectedStarMap_ker_two M I hc) D (hcard.symm ▸ ho)
  refine ⟨D, hD, hi, ?_, hcard⟩
  have hr : ((selectedStarMap M I).comp D.subtype).range = D.map (selectedStarMap M I) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, hcard]

/-- The two descriptions use the same elements of M ∩ I. -/
theorem selected_lift_action_image (M I V : Subgroup G)
    (hn : M ⊓ I ≤ normalizer (V : Set G)) (D : Subgroup ↥(M ⊓ I)) :
    (D.map (selectedActionMap M I V hn)).map (inducedAutomizer V (M ⊓ I)).subtype =
      inducedAutomizer V (D.map (M ⊓ I).subtype) := by
  ext a
  constructor
  · rintro ⟨b, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨⟨d, hn d.property⟩, ⟨d, hd, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨d, hd, he⟩, hb⟩
    refine ⟨selectedActionMap M I V hn d, mem_map_of_mem _ hd, ?_⟩
    rw [← hb]
    change V.normalizerMonoidHom.rangeRestrict ⟨d.val, hn d.property⟩ =
      V.normalizerMonoidHom.rangeRestrict b
    exact congrArg V.normalizerMonoidHom.rangeRestrict (Subtype.ext he)

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
