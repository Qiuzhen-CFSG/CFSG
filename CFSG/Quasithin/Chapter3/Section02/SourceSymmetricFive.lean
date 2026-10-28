module
public import CFSG.Quasithin.Chapter3.Section02.SourceResidualSylow
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SymmetricFive

/-!
# The natural S₅ exclusion on the original FSU module

For both original actor alternatives, the actual reduced seed supplies
Hypothesis 3.1.5. The source S₅ quotient marking now implies the residual
Sylow condition, and the genuine 3.1.1 common-normal theorem contradicts
uniqueness. The independent C.5.8 producer retains that one earlier-source
implication; no S₅ Sylow or span-placement hypothesis remains.
Source: Aschbacher–Smith 3.1.7 and 3.2.2(6), printed pp.575–579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

open Representation BinaryPermutation BinaryPermutation.FiveCentralExtension

theorem source_reduced_seed_natural_symmetric_five_excluded
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G))
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZ : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (center Y).map Y.subtype) :
    let qrc := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
    let U := (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
    let hU : IsPReduced 2 U := qrc.sylowOmega_reduced (hG.evenCharacteristic T)
    letI : U.Normal := hU.normal
    letI : IsElementaryAbelian 2 U := hU.elementary
    ∀ (q : Y →* Sym) (hq : Function.Surjective q)
      (hker : q.ker = centralizer (U : Set Y))
      (p : Additive U →ₗ[ZMod 2] core (Fin 5)) (_hp : Function.Surjective p)
      (_heK : ∀ k ∈ pResidual 2 Y, ∀ v,
        p (NormalElementaryQuotient.representation U q hq hker (q k) v) =
          coreRepresentation (Fin 5) (q k) (p v))
      (_hk : p.ker = fixedSpace
        (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 Y).map q)), False := by
  let qrc := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  let U := (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y
  have hU : IsPReduced 2 U := qrc.sylowOmega_reduced (hG.evenCharacteristic T)
  let : U.Normal := hU.normal
  let : IsElementaryAbelian 2 U := hU.elementary
  dsimp only
  intro q hq hker p hp heK hk
  have hs := qrc.residual_sylow_of_natural_symmetric_five hG hM hu hJ hZ q hq hker p hp heK hk
  exact source_reduced_seed_not_residual_sylow T X M hXM hTM hG hM hX hc I hI h311 hu hY hs
end CFSG.Quasithin.Chapter3.Section02
