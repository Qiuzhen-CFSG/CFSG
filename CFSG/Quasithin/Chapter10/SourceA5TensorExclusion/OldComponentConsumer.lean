module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupComponent

/-!
# The original old residual in the tensor pair consumer

The old H-star residual is kept literally while the A₅ quotient and source
9.3.2 Sylow/core premises place it in the stabilizer local family. Its
Sylow supplement gives escape from M, so adjoining it to the original L
also escapes M. The checked pair theorem then identifies the residual of
the new overgroup as the common C-component containing both original factors.

Source: Aschbacher–Smith 9.3.4–6, printed pp.733–734. Quotient recognition,
nontrivial overgroup core and the tensor action premises remain explicit.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_tensor_old_residual_component_product
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (hcore : H.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (M₀ U : Subgroup G) (hMcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit U L : Set G))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤
      centralizer (componentOrbit U L : Set G)) :
    (pResidual 2 M₀).IsCComponent ∧
      L.subgroupOf M₀ ≤ pResidual 2 M₀ ∧
      ((pResidual 2 H).map H.subtype).subgroupOf M₀ ≤ pResidual 2 M₀ ∧
      ∀ g : M₀, ∃ k ∈ pResidual 2 M₀,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀), k * r = g := by
  have hK := source_a5_hstar_residual_at_stabilizer
    (le_normalizer_componentOrbit L T) hH eK hSyl hcore
  have hout : ¬ M₀ ≤ D.maximalLocal := by
    intro hm
    exact hK.2.2 ((hgen ▸ (show (pResidual 2 H).map H.subtype ≤
      (L ⊔ (pResidual 2 H).map H.subtype) ⊔
        ((T : Subgroup G) ⊓ normalizer (L : Set G)) from
      le_sup_of_le_left le_sup_right)).trans hm)
  exact source_a5_tensor_pair_component_product D e hn M₀
    ((pResidual 2 H).map H.subtype) U hMcore hgen hout hK.2.1 hQ hKU hmove

end CFSG.Quasithin.Chapter10
