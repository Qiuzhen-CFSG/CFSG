module

public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.PrimeDivisors
public import CFSG.Quasithin.ChapterF.Section09.Setup
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Literal F.9 source application of ordinary component recovery

The original F.9 hypothesis puts O₂(L) in its ambient Sylow subgroup and
hence in H. Its characteristic-two and generated-core fields discharge the
two local inputs of the prime-divisor calculation. The original natural
coordinates and genuine theta identity then place the point-centralizing
two-perfect subgroup Y in L.

This is the ordinary component-placement step in the13.7.4(1) application
of Aschbacher–Smith13.3.9. It does not assert the final faithfulness theorem.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G:Type*} [Group G] [Finite G]

theorem le_component_of_f9_theta (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (M Y:Subgroup G) [IsElementaryAbelian 2 D.V]
    (hLP:D.L≤M⊓normalizer (D.V:Set G))
    (hPL:M⊓normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (α:D.L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(D.L⧸pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (e:Additive D.V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:D.L) (v:Additive D.V), e (conjugationRepresentation
      (M⊓normalizer (D.V:Set G)) D.V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (htheta:closure {x:G|x∈M ∧ orderOf x=3}=D.L) (hp:IsPPerfect 2 Y)
    (hY:Y≤M⊓normalizer (D.V:Set G)) (hYH:Y≤D.H)
    (hnY:D.H≤normalizer (Y:Set G))
    (w:Additive D.V) (hw:w≠0) (hc:Y≤centralizer ({(w.toMul:G)}:Set G)) : Y≤D.L := by
  have hQH:D.L.pCoreIn 2≤D.H :=
    ((isPGroup_pCoreIn 2 D.L).le_sylow_of_normalized D.T
      (h.normalizes_L.trans (normalizer_le_normalizer_characteristic_image D.L
        (pCore 2 D.L)))).trans h.T_le_H
  have hcore:pCore 2 (D.L⊔D.H:Subgroup G)=⊥ := by
    have he:D.LT⊔D.H=D.L⊔D.H := by
      change (D.L⊔(D.T:Subgroup G))⊔D.H=D.L⊔D.H
      rw [sup_assoc,sup_eq_right.mpr h.T_le_H]
    exact he ▸ h.generated_core
  have hchar:centralizer (pCore 2 D.H:Set D.H)≤pCore 2 D.H := by
    simpa only [h.characteristic_H] using centralizer_generalizedFitting_le D.H
  exact le_component_of_theta_and_core_free_join M D.L D.V D.H Y hLP hPL α hα
    eL e he htheta hp hY hYH hnY hQH hcore hchar w hw hc
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
