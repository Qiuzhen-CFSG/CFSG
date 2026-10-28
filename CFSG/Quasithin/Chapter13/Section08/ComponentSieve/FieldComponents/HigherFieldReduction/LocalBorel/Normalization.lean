module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.LiftTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SylowBorel

/-!
# Source normalization of the higher-field Borel

Intersect the solvable local group A with the normal component K*. The
intrinsic model theorem makes its supplied Sylow two-subgroup normal in
the intersection; Sylow maximality identifies it with the two-core.
Characteristicity then makes A normalize that Sylow and its normalizer
inside K*. Lift this literal Borel through H → H/O₂(H), inside K, and
take its characteristic two-residual. The quotient kernel is retained.

This generalizes the earlier rank-one transfer at
ExternalModules.Structure.MarkedBorel.Normalization to all seven source
models without changing that interface.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954, with the actual
Sylow marking and relative component normality from the preceding setup.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization
open Components.Swapped.LinearTwo TorusModels.Assembly
variable {G : Type*} [Group G] [Finite G]

/-- The intersection with the normal component has the marked Sylow as its
two-core. Its characteristicity makes a solvable overgroup normalize the
marked Borel for each of the seven higher-field models. -/
theorem solvable_normalizes_borel (K A : Subgroup G) [K.Normal]
    [Group.IsSolvable A] (S : Sylow 2 K) {n : ℕ} {unitary four : Bool}
    (model : Model K n unitary four) (hn : 1 < n)
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
  have hNS := model_solvable_overgroup_le_normalizer model hn S N inferInstance hSN
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

/-- Lift the seven-model Borel normalization through the actual star map
inside K, then take its characteristic two-residual. -/
theorem source_borel_normalized (H K D T : Subgroup G)
    (hKH : K ≤ H) (hDH : D ≤ H) (hTH : T ≤ H)
    [(K.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    [Group.IsSolvable (D ⊔ T : Subgroup G)]
    (hT : Chapter1.IsSylowIn 2 T H) {n : ℕ} {unitary four : Bool}
    (model : Model (Source.starImage H K) n unitary four) (hn : 1 < n) :
    D ⊔ T ≤ normalizer (borel H K T hKH hT : Set G) := by
  let Ks := Source.starImage H K
  let A := Source.starImage H (D ⊔ T)
  let S := sourceSylow H K T hT
  let Bstar := SylowBorel.relativeBorel Ks S
  have hAH : D ⊔ T ≤ H := sup_le hDH hTH
  let : Group.IsSolvable ((D ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hAH).toMonoidHom) (subgroupOfEquivOfLe hAH).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((D ⊔ T).subgroupOf H))
  have hSA : (S : Subgroup Ks).map Ks.subtype ≤ A := by
    rw [sourceSylow_image H K T hT]
    exact inf_le_left.trans (map_mono (subgroupOf_mono H le_sup_right))
  have hnB := solvable_normalizes_borel Ks A S model hn hSA
  have hnK : D ⊔ T ≤ normalizer (K : Set G) :=
    hAH.trans (le_normalizer_of_normal_subgroupOf hKH)
  have hn0 : D ⊔ T ≤ normalizer (borel₀ H K T hKH hT : Set G) :=
    borelLift_normalized H K (D ⊔ T) hKH hAH Bstar hnK hnB
  exact hn0.trans (normalizer_le_normalizer_characteristic_image
    (borel₀ H K T hKH hT) (pResidual 2 (borel₀ H K T hKH hT)))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization
