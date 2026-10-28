module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The first radical as a Sylow subgroup of the component radical

The natural marking identifies the original first residual quotient with
PSL₂ over the original binary field. Hence O∞(L₁T) = O₂(L₁T). Restricting
O∞(KT) to L₁T and using the proved radical containment identifies its
intersection with T as R₁. Normal-subgroup Sylow restriction then proves
that the literal R₁ is Sylow in O∞(KT), for every surviving alternative.

These results use neither the odd-extension Fitting index nor its proposed
numerical bound. They prepare that bound for the same triangle assembly
owner, qt-d-1222-shadow-component-triangle.
Source: Aschbacher–Smith, 11.4.1(3), printed pp.775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

private theorem radical_comap_le {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (i : A →* B) (hi : Function.Injective i) :
    (solvableRadical B).comap i ≤ solvableRadical A := by
  let C := (solvableRadical B).comap i
  let j : C →* solvableRadical B := (i.comp C.subtype).codRestrict _ (fun x => x.property)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun a b hab => Subtype.ext (hi (congrArg Subtype.val hab)))
  exact le_solvableRadical C inferInstance inferInstance

/-- Restriction to the seed join identifies the radical intersection with T. -/
theorem sylow_inf_radical_eq_local_core (T : Sylow 2 G) (A K : Subgroup G)
    (hAK : A ≤ K)
    (hA : solvableRadical (A ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
    (hR : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype) :
    (T : Subgroup G) ⊓
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype = (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hRT : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (A ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  refine le_antisymm ?_ (le_inf hRT hR)
  rintro r ⟨hrT,rJ,hrJ,he⟩
  let Y := A ⊔ (T : Subgroup G)
  let J := K ⊔ (T : Subgroup G)
  have hYJ : Y ≤ J := sup_le_sup_right hAK _
  have hrY : r ∈ Y := mem_sup_right hrT
  have hi : inclusion hYJ (⟨r,hrY⟩ : Y) ∈ solvableRadical J := by
    exact (show rJ = inclusion hYJ (⟨r,hrY⟩ : Y) from Subtype.ext he) ▸ hrJ
  have hh := radical_comap_le (inclusion hYJ) (inclusion_injective hYJ) hi
  rw [hA] at hh
  exact mem_map_of_mem Y.subtype hh

/-- The local two-core is Sylow in the larger radical once containment holds. -/
theorem local_core_sylow_radical (T : Sylow 2 G) (A K : Subgroup G)
    (hAK : A ≤ K)
    (hA : solvableRadical (A ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
    (hR : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype) :
    Chapter1.IsSylowIn 2 ((A ⊔ (T : Subgroup G)).pCoreIn 2)
      ((solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype) := by
  let J := K ⊔ (T : Subgroup G)
  let B := (solvableRadical J).map J.subtype
  have hn : (B.subgroupOf J).Normal := by
    change ((solvableRadical J).map J.subtype |>.comap J.subtype).Normal
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    infer_instance
  have ht : Chapter1.IsSylowIn 2 (T : Subgroup G) J :=
    ⟨T.subtype le_sup_right, by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]⟩
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal ht
    (show B ≤ J from map_subtype_le _) hn.isSubnormal
  rw [sylow_inf_radical_eq_local_core T A K hAK hA hR] at hs
  exact hs

variable {T : Sylow 2 G} {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The original natural marking identifies the seed-join radical with its two-core. -/
theorem ofFlag_seed_radical_eq_core (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c) :
    solvableRadical (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) := by
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  exact join_radical_eq_core_of_psl2 T (f.Li 0) (f.sylow_normalizes_Li 0)
    (by
      exact (show 3 < 2 ^ 2 from by decide).trans_le
        (Nat.pow_le_pow_right (by decide) S.nonbinary))
    (by
      obtain ⟨f₀,hu,_,hq,_⟩ := LocalGeometry.exists_unique_marked_flag D S c
      have he : f.Li 0 = f₀.Li 0 := by
        change LocalGeometry.localResidual L (c.preimage (f.space 0)) = _
        rw [hu 0 (f.space 0) (f.dimension 0) (f.invariant 0)]
        rfl
      exact ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
        he.symm ▸ hq 0⟩)
/-- In every surviving case, the original first radical is Sylow in O∞(KT). -/
theorem ofFlag_surviving_sylow_radical (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree) :
    Chapter1.IsSylowIn 2 (ofFlag S f X z H).R₁
      ((solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype) := by
  have hA : f.Li 0 ≠ ⊥ := by
    intro he
    apply (Triangle.Reselection.flag_residual_mem_local D S f 0).1.ne_bot
    rw [he]
    exact bot_subgroupOf _
  exact local_core_sylow_radical T (f.Li 0) K hAK (ofFlag_seed_radical_eq_core S f)
    (ofFlag_surviving_radical_containment S f X z H K hK hA hAK hTK hcase)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
