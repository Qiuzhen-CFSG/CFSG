module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals

/-!
# Normalization and solvable exclusion for the marked rank-one Borel

The intersection of a solvable subgroup with the normal PSL₂ component
contains the marked Sylow two-subgroup, so lies in its Borel. That Sylow
subgroup is the two-core of the intersection. Characteristicity therefore
makes the solvable subgroup normalize the marked Sylow and its Borel.
Lifting inside K retains the two-core kernel. The exact universal earlier
solvable-overgroup conclusion of 13.8.13 then places the lift in M.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed p.954/PDF p.971, using 13.8.13.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
open Components.Swapped.LinearTwo
variable {G : Type*} [Group G] [Finite G]

theorem solvable_normalizes_borel (K A : Subgroup G) [K.Normal]
    [Group.IsSolvable A] (S : Sylow 2 K) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL K 2 (2 ^ n))
    (hSA : (S : Subgroup K).map K.subtype ≤ A) :
    A ≤ normalizer (SylowBorel.relativeBorel K S : Set G) := by
  let C := A ⊓ K
  let U := (S : Subgroup K).map K.subtype
  have hUC : U ≤ C := le_inf hSA (map_subtype_le _)
  let N := A.subgroupOf K
  let i : N →* A :=
    { toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : A => x.val) h))
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hi
  have hSN : (S : Subgroup K) ≤ N := by
    intro x hx
    exact hSA ⟨x,hx,rfl⟩
  have hNS := Chapter1.XiEmbedding.SwappedSylow.binary_model_solvable_overgroup_le_normalizer
    (by omega) hmodel S N hSN
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc u hu
    obtain ⟨x,hx,rfl⟩ := hu
    exact ⟨(⟨c,hc.2⟩ : K) * x * (⟨c,hc.2⟩ : K)⁻¹,
      le_normalizer_iff.mp hNS ⟨c,hc.2⟩ hc.1 x hx,rfl⟩
  have hUQ : U ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes
    (S.isPGroup'.map K.subtype) hUC hCU
  have hQK : C.pCoreIn 2 ≤ K := (pCoreIn_le 2 C).trans inf_le_right
  have hcore : C.pCoreIn 2 = U := by
    have hp : IsPGroup 2 ((C.pCoreIn 2).subgroupOf K) :=
      (isPGroup_pCoreIn 2 C).comap_subtype
    have hle : (S : Subgroup K) ≤ (C.pCoreIn 2).subgroupOf K := by
      intro x hx
      exact hUQ ⟨x,hx,rfl⟩
    have he := S.is_maximal' hp hle
    have hm := congrArg (fun P => P.map K.subtype) he
    rwa [map_subgroupOf_eq_of_le hQK] at hm
  have hAC : A ≤ normalizer (C : Set G) :=
    (le_inf A.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hAU : A ≤ normalizer (U : Set G) := by
    rw [← hcore]
    exact hAC.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  rw [SylowBorel.relativeBorel_eq]
  apply le_trans (le_inf ?_ le_normalizer_of_normal) inf_normalizer_le_normalizer_inf
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj a).bijective,
    mem_normalizer_iff_map_conj_eq.mp (hAU ha)]

theorem source_borel_normalized_and_le_M (H K D T G₁ M : Subgroup G)
    (hKH : K ≤ H) (hDH : D ≤ H) (hTH : T ≤ H) [(K.subgroupOf H).Normal]
    [Group.IsSolvable (D ⊔ T : Subgroup G)]
    (S : Sylow 2 (Source.starImage H K)) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hS : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H T ⊓ Source.starImage H K)
    (hKG : K ≤ G₁) (hbase : D ⊔ T ≤ G₁)
    (hex : ∀ J : Subgroup G, D ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M) :
    let B₀ := HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S)
    D ⊔ T ≤ normalizer (B₀ : Set G) ∧ B₀ ≤ M := by
  let Ks := Source.starImage H K
  let A := Source.starImage H (D ⊔ T)
  let Bstar := SylowBorel.relativeBorel Ks S
  have hAH : D ⊔ T ≤ H := sup_le hDH hTH
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable ((D ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAH).toMonoidHom) (subgroupOfEquivOfLe hAH).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((D ⊔ T).subgroupOf H))
  have hSA : (S : Subgroup Ks).map Ks.subtype ≤ A := by
    rw [hS]
    exact inf_le_left.trans (map_mono (subgroupOf_mono H le_sup_right))
  have hnB := solvable_normalizes_borel Ks A S hn hmodel hSA
  have hnK : D ⊔ T ≤ normalizer (K : Set G) :=
    hAH.trans (le_normalizer_of_normal_subgroupOf hKH)
  have hnorm := borelLift_normalized H K (D ⊔ T) hKH hAH Bstar hnK hnB
  let e := (normalizer (S : Set Ks)).equivMapOfInjective Ks.subtype Ks.subtype_injective
  let : Group.IsSolvable (normalizer (S : Set Ks)) :=
    (BinaryBorel.factor_facts (by omega) hmodel S).1
  let : Group.IsSolvable Bstar := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact ⟨hnorm, borelLift_le_M H K D T G₁ M hKH Bstar hnorm hKG hbase hex⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

end
