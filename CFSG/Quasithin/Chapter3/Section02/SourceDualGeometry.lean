module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceDualGeometry

/-!
# The original FSU application of the D.1.4 quadratic core closure

Under the source inside-core and unique-chief-factor alternatives, the
original orbit module has [U,Q]=[v,Q] for a noncentral seed vector, and
Q acts quadratically. This applies the proved D.1.4 group geometry to
the literal qrc configuration from both original FSU actor alternatives.
Source: Aschbacher–Smith, D.1.4 and 3.1.6/3.2.2, pp.175–176,573–579.
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

theorem source_reduced_seed_coreClosure_commutator_geometry
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T) :
    let Q := ChapterD.UniqueFactor.intersectionClosure (X ⊔ (T : Subgroup G)) Y
    ∃ v ∈ V_T,
      v ∉ V_T ⊓ centralizer ((pResidual 2 Y).map Y.subtype : Set G) ∧
      ⁅ChapterD.conjugateSpan Y V_T,Q⁆ = ⁅zpowers v,Q⁆ ∧
      ⁅ChapterD.conjugateSpan Y V_T,Q⁆ ≤
        V_T ⊓ centralizer ((pResidual 2 Y).map Y.subtype : Set G) ∧
      ⁅⁅ChapterD.conjugateSpan Y V_T,Q⁆,Q⁆ = ⊥ :=
  ChapterD.UniqueFactor.source_coreClosure_commutator_geometry
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs

end CFSG.Quasithin.Chapter3.Section02
