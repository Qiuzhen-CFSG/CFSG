module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.RelativeModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.FittingImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Fitting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Fitting indices in normal two-extensions of the odd SL₂ rows

An actual SL₂ quotient above O₂,F(K) gives index exactly two in O∞(K).
For a normal two-extension J of K, functoriality of the Fitting preimage
shows that O∞(J/O₂,F(J)) is a two-group. This does not bound its order:
additional two-actors can enlarge it. Its order is exactly the index of
O₂(J) in any Sylow two-subgroup of O∞(J), since two-subgroups meet the
Fitting preimage only in O₂(J).

The final theorem applies the extension argument to the literal join KT.
The companion original-flag application supplies the actual odd-kernel
models. The numerical bound remains with qt-d-1222-shadow-component-triangle.
Source: Aschbacher–Smith, 11.1.1 and 11.4.1(3), printed pp.761,775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

/-- The actual SL₂ Fitting quotient gives radical index two in the component. -/
theorem fitting_index_two_of_sl2 {p : ℕ} (hp : 3 < p) (ho : Odd p)
    (hm : Source.IsSL (G ⧸ twoFittingCore G) 2 p) :
    (twoFittingCore G).relIndex (solvableRadical G) = 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let Q := G ⧸ twoFittingCore G
  let q := QuotientGroup.mk' (twoFittingCore G)
  let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : IsQuasisimple Q := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (by omega) e
  have hr : solvableRadical Q = center Q :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))))
  have hc : Nat.card (center Q) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (GorensteinWalter.sl2ProjectiveProjection_ker F) ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card F (hF ▸ ho)
  rw [← QuotientGroup.ker_mk' (twoFittingCore G), relIndex_ker,
    ← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), hr, hc]

/-- Passing to the ambient Fitting preimage can enlarge the radical index,
but the quotient is still a two-group. -/
theorem radical_fitting_quotient_isTwoGroup (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup 2 (G ⧸ K))
    (hi : (twoFittingCore K).relIndex (solvableRadical K) = 2) :
    IsPGroup 2 (solvableRadical (G ⧸ twoFittingCore G)) := by
  let q := QuotientGroup.mk' (twoFittingCore G)
  let Q := G ⧸ twoFittingCore G
  let B := K.map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let f : K →* B := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hk : twoFittingCore K ≤ f.ker := by
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr
      (twoFittingCore_map_subtype_le_of_normal K (mem_map_of_mem K.subtype hk))
  let fk := QuotientGroup.lift (twoFittingCore K) f hk
  let qk := QuotientGroup.mk' (twoFittingCore K)
  have himg : IsPGroup 2 ((solvableRadical K).map qk) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one, ← relIndex_ker, qk, QuotientGroup.ker_mk'] using hi
  have hB : IsPGroup 2 (solvableRadical B) := by
    have hsol : Group.IsSolvable f.ker := by
      let j : f.ker →* twoFittingCore G :=
        (K.subtype.comp f.ker.subtype).codRestrict _ (fun x => by
          apply (QuotientGroup.eq_one_iff _).mp
          exact congrArg Subtype.val (show f x.val = 1 from x.property))
      let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
      exact Group.isSolvable_of_isSolvable_injective (f := j)
        (fun x y he => Subtype.ext (Subtype.ext
          (congrArg (fun z : twoFittingCore G => (z : G)) he)))
    let := hsol
    have he : (solvableRadical K).map f = solvableRadical B := by
      rw [← comap_solvableRadical_eq_of_solvable_ker f hf,map_comap_eq_self_of_surjective hf]
    rw [← he, show f = fk.comp qk from rfl, ← map_map]
    exact himg.map fk
  have hQB : IsPGroup 2 (Q ⧸ B) := by
    let g := QuotientGroup.map K B q (by intro k hk; exact mem_map_of_mem q hk)
    exact hquot.of_surjective g (QuotientGroup.map_surjective_of_surjective K B q
      ((QuotientGroup.mk'_surjective B).comp (QuotientGroup.mk'_surjective _)) _)
  exact radical_isTwoGroup_of_normal_two_quotient B hB hQB


/-- The radical quotient above O₂,F is detected exactly by a Sylow two-subgroup. -/
theorem fitting_index_eq_sylow_core_index (P : Subgroup G)
    (hP : Chapter1.IsSylowIn 2 P (solvableRadical G))
    (hQ : IsPGroup 2 (solvableRadical (G ⧸ twoFittingCore G))) :
    (twoFittingCore G).relIndex (solvableRadical G) = (pCore 2 G).relIndex P := by
  let q := QuotientGroup.mk' (twoFittingCore G)
  let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hr : (solvableRadical G).map q = solvableRadical (G ⧸ twoFittingCore G) := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_map hP q
  have he : (solvableRadical G).map q = P.map q :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 _ (hr.symm ▸ hQ)
      (map_mono (Chapter1.isSylowIn_iff.mp hP).2.1) le_rfl
  have hi : P ⊓ twoFittingCore G = P ⊓ pCore 2 G :=
    le_antisymm (le_inf inf_le_left
      (two_intersection_fitting_le_core P (Chapter1.isSylowIn_iff.mp hP).1))
      (inf_le_inf_left _ twoCore_le_twoFittingCore)
  calc
    (twoFittingCore G).relIndex (solvableRadical G) =
        Nat.card ((solvableRadical G).map q) := by
      simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker (solvableRadical G) q)
    _ = Nat.card (P.map q) := by rw [he]
    _ = (twoFittingCore G).relIndex P := by
      simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker P q).symm
    _ = (pCore 2 G).relIndex P := by
      rw [← inf_relIndex_left P (twoFittingCore G), hi, inf_relIndex_left]
/-- The SL₂ Fitting model controls the prime support of the enlarged radical quotient. -/
theorem join_radical_fitting_quotient_isTwoGroup_of_sl2 (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    {p : ℕ} (hp : 3 < p) (ho : Odd p)
    (hm : Source.IsSL (K ⧸ twoFittingCore K) 2 p) :
    IsPGroup 2 (solvableRadical
      ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G))) := by
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let e : B ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hF : (twoFittingCore B).map e.toMonoidHom = twoFittingCore K := by
    refine le_antisymm (twoFittingCore_map_equiv_le e) ?_
    intro k hk
    exact ⟨e.symm k, twoFittingCore_map_equiv_le e.symm
      (mem_map_of_mem e.symm.toMonoidHom hk), e.apply_symm_apply k⟩
  have hi : (twoFittingCore B).relIndex (solvableRadical B) = 2 := by
    have he := relIndex_map_map_of_injective (f := e.toMonoidHom)
      (twoFittingCore B) (solvableRadical B) e.injective
    rw [hF,map_solvableRadical_equiv e] at he
    exact he.symm.trans (fitting_index_two_of_sl2 hp ho hm)
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right), subgroupOf_self])
  exact radical_fitting_quotient_isTwoGroup B hq hi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
