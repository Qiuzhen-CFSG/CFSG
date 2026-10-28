module
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.CharacteristicNormalizerClosure
/-!
# The actual central module under characteristic-two pushing up

The radical contains O₂(G). If the latter is self-centralizing, every
central involution of the radical lies in Ω₁Z(O₂(G)). Consequently a subgroup
outside the characteristic-normalizer control group must act nontrivially
on this literal normal elementary subgroup. These are the module hypotheses
in Aschbacher, Math. Z. 177 (1981), 10.3, p.78.

This module explicitly assumes characteristic two for G. The general C.2.4
statement only assumes it for its component, so that reduction is not
asserted here.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

noncomputable abbrev radicalCentralModule : Subgroup G := omegaOneCenterAmbient (pCore 2 G)

omit [Finite G] in
theorem radicalCentralModule_normal : (radicalCentralModule (G := G)).Normal := by
  let : (omega₁ (center (pCore 2 G)) (p := 2)).Characteristic := omega₁_characteristic _
  change (((omega₁ (center (pCore 2 G)) (p := 2)).map
    (center (pCore 2 G)).subtype).map (pCore 2 G).subtype).Normal
  infer_instance

omit [Finite G] in
theorem radicalCentralModule_elementary : IsElementaryAbelian 2 (radicalCentralModule (G := G)) :=
  omegaOneCenterAmbient_elementaryAbelian _

theorem radicalCentralModule_le {R : Subgroup G} (hr : IsPRadical 2 R) :
    radicalCentralModule (G := G) ≤ R := by
  intro x hx
  exact pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le
    ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1

omit [Finite G] in
theorem core_centralizes_radicalCentralModule :
    pCore 2 G ≤ centralizer (radicalCentralModule (G := G) : Set G) := by
  intro q hq v hv
  exact ((mem_omegaOneCenterAmbient_iff _ v).mp hv).2.2 q hq |>.symm

theorem radicalOmega_le_radicalCentralModule {R : Subgroup G} (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    omegaOneCenterAmbient R ≤ radicalCentralModule (G := G) := by
  intro x hx
  obtain ⟨_, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
  have hxC : x ∈ centralizer (pCore 2 G : Set G) := fun q hq =>
    hxc q (pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le hq)
  exact (mem_omegaOneCenterAmbient_iff _ x).mpr ⟨hc hxC,hx2,hxC⟩

theorem outside_moves_radicalCentralModule {R M L : Subgroup G}
    (hr : IsPRadical 2 R) (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ L ≤ M) :
    ¬ L ≤ centralizer (radicalCentralModule (G := G) : Set G) := by
  intro hfix
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hr.1
  have hCne : C ≠ ⊥ := omega_center_ne_bot hr.isPGroup
  have hLC : L ≤ centralizer (C.map R.subtype : Set G) :=
    hfix.trans (centralizer_le (radicalOmega_le_radicalCentralModule hr hc))
  exact hout ((hLC.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((normalizer_le_characteristicNormalizerClosure R C hCne).trans hcontrol))
end CFSG.Quasithin.ChapterC.Section02Source
