module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.ActionData
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.PcComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Data

/-!
# Transfer of finite Steinberg word certificates to Rudvalis

Permutation checks are transferred through the faithful original model inclusion.
No alternate model or external computation is assumed. Source and conventions:
Max4Geometry.Words and the preserved ATLAS max4 program.
-/

open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate Max4Normalizers Max4Normalizers.GeneratorMaps
namespace Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
set_option maxRecDepth 30000

@[expose] public def permWord (j : Fin 11) : Equiv.Perm (Fin 4060) :=
  normalFormPermutation (Max4Words.masks j)

@[expose] public def modelInclusion : Model →* Equiv.Perm (Fin 4060) :=
  modelSubgroup.subtype

public theorem permWord_eq (j : Fin 11) :
    permWord j = modelInclusion (Max4Words.generator j) :=
  normalFormPermutation_eq _

public theorem actor_eq (i : Fin 2) :
    gen i.castSucc.castSucc = modelInclusion (actorGenerator i : Model) := by
  fin_cases i
  · exact gen_eq 0 |>.trans LocalCardinality.Max4.generator0_eq
  · exact gen_eq 1 |>.trans LocalCardinality.Max4.generator1_eq

public theorem product_eq (w : List (Fin 11)) :
    (w.map permWord).prod = modelInclusion ((w.map Max4Words.generator).prod) := by
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, ← permWord_eq]

public theorem transfer (i : Fin 2) (j : Fin 11)
    (h : gen i.castSucc.castSucc * permWord j * (gen i.castSucc.castSucc)⁻¹ =
      ((conjugateWord i j).map permWord).prod) :
    (actorGenerator i : Model) * Max4Words.generator j * (actorGenerator i : Model)⁻¹ =
      ((conjugateWord i j).map Max4Words.generator).prod := by
  apply modelSubgroup.subtype_injective
  change modelInclusion ((actorGenerator i : Model) * Max4Words.generator j *
    (actorGenerator i : Model)⁻¹) = modelInclusion
      (((conjugateWord i j).map Max4Words.generator).prod)
  simpa only [map_mul, map_inv, actor_eq, permWord_eq, product_eq] using h

end Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
