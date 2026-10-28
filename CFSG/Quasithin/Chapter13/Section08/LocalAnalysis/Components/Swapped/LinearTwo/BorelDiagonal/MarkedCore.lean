module
public import Theory.GroupTheory.NormalSubdirectCore
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProjectedImages
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The two-core of a normal exchanged field-four Borel marking

A nontrivial normal two-perfect marking projects onto the first factor
Borel. Exchange gives the second projection. The normal subdirect core
theorem then puts the entire product Sylow in the marking, and relative
normality identifies this with its intrinsic two-core.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058. The original
point residual application is in LocalReduction.BinaryPointCore.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BorelProjections
variable {Q : Type*} [Group Q] [Finite Q]

/-- The whole Sylow two-subgroup is the core of a normal exchanged marking. -/
theorem normal_swapped_core (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) (τ : MulAut (BinaryBorel.borel S))
    (hτ : (BinaryBorel.secondAxis S).map τ.toMonoidHom = BinaryBorel.firstAxis S)
    (D : Subgroup (BinaryBorel.borel S)) [D.Normal]
    (hD : D.map τ.toMonoidHom = D) (hne : D ≠ ⊥) (hp : IsPPerfect 2 D) :
    (D.pCoreIn 2).map (BinaryBorel.borel S).subtype = (S : Subgroup (Q × Q)) := by
  let e := BinaryBorel.coordinates S
  let A := BinaryBorel.borel (BinaryBorel.firstSylow S)
  let B := BinaryBorel.borel (BinaryBorel.secondSylow S)
  have hf := first_image_eq_top hmodel S τ hτ D hD hne hp
  have hsup : D ⊔ BinaryBorel.secondAxis S = ⊤ := by
    rw [←firstProjection_ker,←comap_map_eq,hf,comap_top]
  have hsup' : D ⊔ BinaryBorel.firstAxis S = ⊤ := by
    have hh := congrArg (map τ.toMonoidHom) hsup
    simpa only [Subgroup.map_sup,hD,hτ,map_top_of_surjective τ.toMonoidHom τ.surjective] using hh
  let g := (MonoidHom.snd A B).comp e.toMonoidHom
  have hg : Function.Surjective g := Prod.snd_surjective.comp e.surjective
  have hk : (BinaryBorel.firstAxis S).map g = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    exact Subtype.ext hx
  have hs : D.map g = ⊤ := by
    have hh := congrArg (map g) hsup'
    simpa only [Subgroup.map_sup,hk,sup_bot_eq,map_top_of_surjective _ hg] using hh
  let : (D.map e.toMonoidHom).Normal := (inferInstance : D.Normal).map _ e.surjective
  have hcore : pCore 2 (A × B) ≤ D.map e.toMonoidHom :=
    pCore_le_normal_subdirect
      (BinaryBorel.factor_twoPerfect (n := 2) (by decide) hmodel _)
      (BinaryBorel.factor_twoPerfect (n := 2) (by decide) hmodel _)
      (D.map e.toMonoidHom) (by rw [map_map]; exact hf) (by rw [map_map]; exact hs)
  have hc : pCore 2 (BinaryBorel.borel S) ≤ D := by
    intro x hx
    have hh := hcore (show e x ∈ pCore 2 (A × B) by
      rw [←pCore_map_iso 2 e]; exact mem_map_of_mem _ hx)
    obtain ⟨y,hy,he⟩ := hh
    exact e.injective he ▸ hy
  have he : D.pCoreIn 2 = pCore 2 (BinaryBorel.borel S) := by
    rw [pCoreIn,pCore_subnormal_eq_comap 2 (inferInstance : D.Normal).isSubnormal,
      map_comap_eq,range_subtype,inf_eq_right.mpr hc]
  rw [he]
  exact BinaryBorel.ambient_twoCore S
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BorelProjections
