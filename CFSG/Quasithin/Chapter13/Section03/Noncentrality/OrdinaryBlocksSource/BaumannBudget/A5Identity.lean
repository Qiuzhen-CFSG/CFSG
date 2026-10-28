module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.A5Radical
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryOffenderSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.Inputs

/-!
The literal selected component in the ordinary diagonal argument satisfies
both the radical factorization and the Baumann identity. The actual A5 module
and reduction (g) are the inputs of the existing identity contract.
Source: Aschbacher--Smith, 13.3.14, printed p.893.
-/

public section
open scoped commutatorElement IsMulCommutative

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The literal selected component supplies the intended R1 equality in13.3.14.
The actual module mark and reduction(g) are the permitted earlier local inputs. -/
theorem ordinary_selected_point_radical_identity
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hout : ¬ sourceOne L T P ≤ K.map H.subtype)
    (hm : Chapter6.Source.IsConjugationModel (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
      Chapter6.Source.a5Module) :
    (sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ K.map H.subtype) ⊔
        (K.map H.subtype ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hgenG := congrArg (map H.subtype) hgen
  rw [map_commutator,map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hgenG
  obtain ⟨eK,_,_⟩ := hm
  exact Diagonal.point_radical_eq_component_sylow_sup_core _ _ T
    (T_normalizes_one L T P d.line_stable) hnG (h1332 _ hf).1
    ordinary_point_residual_twoPerfect (ordinary_point_residual_quotient_card d eL)
    hout hgenG eK
end CFSG.Quasithin.Chapter13.Section03.Noncentrality

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- The ordinary diagonal Baumann identity on every literal selected component.
Its allowed A5 module and reduction(g) premises are retained in the target;
no block, chief budget, full-span or plane-noncentrality premise is used. -/
theorem ordinaryBaumannIdentitySource_of_original_source
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T) : OrdinaryBaumannIdentitySource d := by
  intro K hK hKs hmove hn hgen hq hU hf hout hm
  let B := K.map H.subtype
  let A := sourceOne L T P
  let J := Diagonal.localGroup B A T
  let I := Diagonal.movedModule B A T
  have hnG : A ≤ normalizer (B : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hJN : J ≤ normalizer (B : Set G) :=
    sup_le (sup_le B.le_normalizer hnG) (h1332 B hf).1
  have hJI : J ≤ normalizer (I : Set G) :=
    reduced_image_commutator_normalized J B (le_sup_left.trans le_sup_left) hJN
  have hIW : I ≤ (reducedTwoSubgroup J).map J.subtype :=
    reduced_image_commutator_le J B (le_sup_left.trans le_sup_left)
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let : IsElementaryAbelian 2 ((reducedTwoSubgroup J).map J.subtype) :=
    IsElementaryAbelian.map J.subtype
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_le hIW
  have hIQ : I ≤ J.pCoreIn 2 := hIW.trans (map_mono (reducedPSubgroup_le_pCore 2 J))
  have hIT : I ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ J from le_sup_right)] using hh
    exact hIQ.trans hQT
  have hIB : I ≤ B := le_normalizer_iff_commutator_le_right.mp
    (((map_subtype_le _ : (reducedTwoSubgroup J).map J.subtype ≤ J)).trans hJN)
  have hfactor := ordinary_selected_point_radical_identity d eL h1332 K hf hn hgen hout hm
  have hIR : I ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [hfactor]
    exact (le_inf hIT hIB).trans le_sup_left
  exact Diagonal.baumann_eq_of_a5_radical_factor B I _ T (h1332 B hf).1 hIB hIR
    ((sup_le (le_sup_left.trans le_sup_left) le_sup_right).trans hJI) hm hfactor
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
