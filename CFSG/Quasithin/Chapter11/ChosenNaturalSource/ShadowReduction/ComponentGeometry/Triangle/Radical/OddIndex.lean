module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Sylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Extension

/-!
# The odd-extension index on the original chosen flag

For each literal odd-extension row of 11.1.1, identify O₂,F(K) using its
normal nilpotent kernel, then pass to KT. The original R₁ is Sylow in the
radical, so the Fitting index is exactly [R₁ : O₂(KT)]. Both the nilpotent
odd-kernel and elementary p²-kernel rows retain their actual quotient maps;
no splitting or restriction on nilpotent exponents is assumed.

This reduction isolates the remaining geometric bound [R₁ : O₂(KT)] ≤ 2.
It is not a proof of that bound or of 11.4.1(3). Its discharge and the final
application to Surviving.ofFlag_surviving_bounds_of_sl2_index stay with
qt-d-1222-shadow-component-triangle; the earlier source inputs stay with
qt-d-1222-shadow-components.
Source: Aschbacher–Smith, 11.1.1 and 11.4.1(3), printed pp.761,775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

/-- The equality keeps the original ambient R₁ and O₂(KT), not isomorphic substitutes. -/
theorem local_fitting_index_eq_core_index (T : Sylow 2 G) (A K : Subgroup G)
    (hAK : A ≤ K)
    (hA : solvableRadical (A ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G))
    (hR : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype)
    (hQ : IsPGroup 2 (solvableRadical
      ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)))) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) =
      ((K ⊔ (T : Subgroup G)).pCoreIn 2).relIndex
        ((A ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let J := K ⊔ (T : Subgroup G)
  let R := (A ⊔ (T : Subgroup G)).pCoreIn 2
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans (sup_le_sup_right hAK _)
  have hs : Chapter1.IsSylowIn 2 (R.subgroupOf J) (solvableRadical J) := by
    apply (Chapter1.IsSylowIn.map_iff J.subtype J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRJ]
    exact local_core_sylow_radical T A K hAK hA hR
  rw [fitting_index_eq_sylow_core_index _ hs hQ]
  change (pCore 2 J).relIndex (R.subgroupOf J) =
    ((pCore 2 J).map J.subtype).relIndex R
  have he := relIndex_map_map_of_injective (f := J.subtype)
    (pCore 2 J) (R.subgroupOf J) J.subtype_injective
  rw [map_subgroupOf_eq_of_le hRJ] at he
  exact he.symm
variable {T : Sylow 2 G} {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- For the actual flag, the remaining Fitting index is exactly the size of
R₁/O₂(KT). The nilpotent odd-kernel model is the literal 11.1.1 row. -/
theorem ofFlag_fitting_index_eq_core_index_of_nilpotent_extension
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree)
    {p : ℕ} (hp : 3 < p) (ho : Odd p)
    (hm : Chapter1.Section02.LocalModels.HasExtension (K ⧸ pCore 2 K)
      (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
      (fun Q _ => Source.IsSL Q 2 p)) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) =
      ((K ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (ofFlag S f X z H).R₁ := by
  have hr := (Chapter1.isSylowIn_iff.mp
    (ofFlag_surviving_sylow_radical S f X z H K hK hAK hTK hcase)).2.1
  exact local_fitting_index_eq_core_index T (f.Li 0) K hAK (ofFlag_seed_radical_eq_core S f) hr
    (join_radical_fitting_quotient_isTwoGroup_of_sl2 T K hTK hp ho
      (Comparison.Frattini.twoFitting_sl2_of_nilpotent_extension hp ho hm))

/-- The elementary p² row has the same literal reduction; no split extension
or unrestricted prime-field model is substituted for the source quotient. -/
theorem ofFlag_fitting_index_eq_core_index_of_elementary_extension
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hK : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Chapter1.Section02.LocalModels.HasExtension (K ⧸ pCore 2 K)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) =
      ((K ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (ofFlag S f X z H).R₁ := by
  have hr := (Chapter1.isSylowIn_iff.mp
    (ofFlag_surviving_sylow_radical S f X z H K hK hAK hTK hcase)).2.1
  exact local_fitting_index_eq_core_index T (f.Li 0) K hAK (ofFlag_seed_radical_eq_core S f) hr
    (join_radical_fitting_quotient_isTwoGroup_of_sl2 T K hTK hp
      ((Fact.out : p.Prime).odd_of_ne_two (by omega))
      (Comparison.Frattini.twoFitting_sl2_of_elementary_extension hp hm))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
