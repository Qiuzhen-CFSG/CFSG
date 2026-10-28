module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Normalization of both literal marked SL₃ preimages

The aligned model supplied by LocalStructure marks the source intersection
only by containment in the upper unipotent subgroup. The local-family Sylow
condition and relative subnormality make that containment an equality.
The complete adequate B.5 classification then excludes graph interchange,
and equivariance of componentPlusMap transfers preservation of each flag
to normalization of its actual preimage.

No local-family membership or Tᵥ-normalization of either preimage is an
input. This therefore supplies the independent normalization input needed
by LocalStructure, using precisely its original containment marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the setup before 13.6.14 and the parabolic step in 13.6.19, printed pp.929–931.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection Matrix.PSL3.LinearThree
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source local-family condition makes Tᵥ ∩ K Sylow in K. Thus its
surjective model image fills the marked unipotent group. -/
theorem marked_intersection_eq_unipotent {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hm : 0 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤ unipotentSL F) :
    ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) = unipotentSL F := by
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.1.2.2.1 le_sup_left hK.1.2.1.subnormal
  obtain ⟨S, hS⟩ := hs
  have heS : (S : Subgroup K) = (Tv T v).subgroupOf K := by
    have hh := congrArg (comap K.subtype) hS
    simpa only [comap_map_eq_self_of_injective K.subtype_injective,
      comap_inf, comap_subtype, subgroupOf_self, inf_top_eq] using hh
  let f := e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)
  let S' := S.mapSurjective (f := f)
    (e.surjective.comp (componentPlusMap_surjective K L T z v hL hz))
  have heS' : (S' : Subgroup SL(3, F)) = ((Tv T v).subgroupOf K).map f := by
    change (S : Subgroup K).map f = _
    rw [heS]
  have hu := (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hm hF).isPGroup'
  exact (S'.is_maximal' hu (heS' ▸ hmark)).trans heS' |>.symm

variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- Both literal flag preimages are Tᵥ-invariant under the complete adequate
B.5 classifier. The containment marking is exactly the output of
LocalStructure.exists_aligned_model; no local membership is used. -/
theorem flagPreimages_normalized [IsElementaryAbelian 2 (Uv z v)]
    {𝒦 : GroupClass.{u}}
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F) :
    Tv T v ≤ normalizer (pointPreimage F K L T z v hL hz e : Set G) ∧
      Tv T v ≤ normalizer (linePreimage F K L T z v hL hz e : Set G) := by
  have he := marked_intersection_eq_unipotent (lt_trans Nat.zero_lt_one hm) hF
    K L T z v hL hz hK e hmark
  have hflags := modelAction_flags K L T z v hL hz source hSQ hK hn hU hSyl
    hcore hF hm e he
  exact flagPreimages_normalized_of_modelAction K L T z v hL hz hn e
    (fun t => (hflags t).1) (fun t => (hflags t).2)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
