module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Equality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.FittingImage
public import Theory.GroupTheory.PCoreImage

/-!
# The Cartan commutator deduction in 11.4.1(3)

Put A = L₁ and R = O₂(AT). For a T-invariant overgroup K of A,
O₂(KT) lies in R. The subgroup KR is normal in KT: K normalizes KR,
and T normalizes both factors. Hence O₂(KR) = O₂(KT). An actor
normalizing K and R therefore preserves this same two-core, even if it
does not normalize KT.

The Fitting index bounds R/(R intersect O₂(KT)) by two. The preceding
normalization lets the small-quotient lemma conclude [R,X] ≤ O₂(KT).
In particular this applies to the original odd Cartan; oddness itself
is unnecessary once the quotient has at most two elements.

The two model-dependent premises, radical containment and the Fitting
index, remain explicit here and are not claimed as source theorems.
Source: Aschbacher--Smith, 11.4.1(3), printed pp.775--776.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G]

private theorem core_normalized (B : Subgroup G) :
    B ≤ normalizer (B.pCoreIn 2 : Set G) :=
  B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))

/-- The ambient two-core lies in the two-core of every subgroup containing T. -/
theorem join_core_le_local_core (T : Sylow 2 G) (A K : Subgroup G) (hAK : A ≤ K) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hT : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hT.trans le_sup_right)
    ((sup_le_sup_right hAK _).trans (core_normalized _))

/-- Replacing T by the first radical preserves the literal ambient two-core. -/
theorem core_join_radical_eq (T : Sylow 2 G) (A K : Subgroup G)
    (hAK : A ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    (K ⊔ (A ⊔ (T : Subgroup G)).pCoreIn 2).pCoreIn 2 =
      (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let R := (A ⊔ (T : Subgroup G)).pCoreIn 2
  have hRT : R ≤ T := by
    simpa only [R, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (A ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (core_normalized _)
  have hJB : K ⊔ (T : Subgroup G) ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans (K ⊔ R).le_normalizer)
      ((le_inf hTK hTR).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (sup_le_sup_left hRT K) hJB
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((join_core_le_local_core T A K hAK).trans le_sup_right)
      ((sup_le_sup_left hRT K).trans (core_normalized _))

/-- The original Cartan needs to normalize K and R₁, not the whole Sylow join. -/
theorem actor_normalizes_join_core (T : Sylow 2 G) (A K X : Subgroup G)
    (hAK : A ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G))
    (hXR : X ≤ normalizer ((A ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    X ≤ normalizer ((K ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  rw [← core_join_radical_eq T A K hAK hTK]
  exact ((le_inf hXK hXR).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

variable [Finite G]

/-- Derive the actual ambient commutator bound from the two distinct
model-dependent inputs in the printed proof. -/
theorem local_commutator_of_radical_fitting_index (T : Sylow 2 G) (A K X : Subgroup G)
    (hAK : A ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G))
    (hXR : X ≤ normalizer ((A ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
    (hR : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype)
    (hi : (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2) :
    ⁅(A ⊔ (T : Subgroup G)).pCoreIn 2, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := K ⊔ (T : Subgroup G)
  let R := (A ⊔ (T : Subgroup G)).pCoreIn 2
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans (sup_le_sup_right hAK _)
  have hRi : R.subgroupOf J ≤ solvableRadical J := by
    intro r hr
    obtain ⟨s, hs, he⟩ := hR hr
    exact (Subtype.ext he : s = r) ▸ hs
  have hidx := two_subgroup_core_index_le_two (R.subgroupOf J)
    ((isPGroup_pCoreIn 2 _).comap_subtype) hRi hi
  have hidx' : (J.pCoreIn 2).relIndex R ≤ 2 := by
    rw [← map_subgroupOf_eq_of_le hRJ]
    exact (relIndex_map_map_of_injective (pCore 2 J) (R.subgroupOf J)
      J.subtype_injective).trans_le hidx
  have hnormal : ((J.pCoreIn 2).subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer (join_core_le_local_core T A K hAK)).mpr
      (hRJ.trans (core_normalized J))
  exact commutator_le_of_normalized_quotient_card_le_two X R (J.pCoreIn 2) hXR
    (actor_normalizes_join_core T A K X hAK hTK hXK hXR) hnormal hidx'

variable {T : Sylow 2 G} {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The literal original chosen-flag application. The two earlier radical
calculations remain explicit until the strict model branches supply them. -/
theorem ofFlag_commutator_of_radical_fitting_index (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXK : X ≤ normalizer (K : Set G)) (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hR : (ofFlag S f X z H).R₁ ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype)
    (hi : (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2) :
    ⁅(ofFlag S f X z H).R₁, X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  local_commutator_of_radical_fitting_index T (f.Li 0) K X hAK hTK hXK hXR hR hi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
