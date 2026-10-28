module
public import CFSG.Quasithin.ChapterC.Section02.ThompsonNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# The canonical Sylow-center module under characteristic control

If the omega center of the two-core is self-centralizing modulo that core,
the conjugate span of the Sylow-center involutions lies in the omega center.
When a simple normal component in the faithful quotient escapes the marked
control subgroup, its centralizer forces the smaller canonical span to have
the same kernel. Thus passage to the canonical module introduces no extra
faithfulness hypothesis.

Source: Aschbacher–Smith C.2.7(3)(a), printed pp.146–147, and its 15.4.20
application. This is the canonical-module step before rank-one recognition.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] in
theorem canonical_span_le_omega_of_kernel (T : Sylow 2 G)
    (hk : centralizer (omegaOneCenterAmbient (pCore 2 G) : Set G) = pCore 2 G) :
    normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ omegaOneCenterAmbient (pCore 2 G) := by
  have hQT : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hVQ : omegaOneCenterAmbient (pCore 2 G) ≤ pCore 2 G := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  let : (omegaOneCenterAmbient (pCore 2 G)).Normal := by
    apply normal_iff_map_conj_eq.mpr
    intro g
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
      Subgroup.Normal.map_conj_eq]
  apply normalClosure_le_normal
  intro z hz
  have hZ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzQ : z ∈ pCore 2 G := hk ▸
    (show z ∈ centralizer (omegaOneCenterAmbient (pCore 2 G) : Set G) from
      fun v hv => hZ.2.2 v (hQT (hVQ hv)))
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hzQ,hZ.2.1,fun v hv => hZ.2.2 v (hQT hv)⟩

omit [Finite H] in
theorem canonical_span_kernel_of_simple_component (T : Sylow 2 G)
    (hne : (T : Subgroup G) ≠ ⊥)
    (hk : centralizer (omegaOneCenterAmbient (pCore 2 G) : Set G) = pCore 2 G)
    (M L : Subgroup G) (hcontrol : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ L ≤ M)
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = pCore 2 G)
    (C : Subgroup H) [C.Normal] [IsSimpleGroup C] [Group.IsPerfect C]
    (hLC : L.map q = C) (hC : centralizer (C : Set H) = ⊥) :
    centralizer (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G) =
      pCore 2 G := by
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hUV := canonical_span_le_omega_of_kernel T hk
  have hQN : pCore 2 G ≤ centralizer (U : Set G) :=
    hk.ge.trans (centralizer_le hUV)
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hne
  let Z := (omega₁ (center T) (p := 2)).map (center T).subtype
  let : (omega₁ (center T) (p := 2)).Characteristic := omega₁_characteristic _
  let : Z.Characteristic := inferInstance
  have hZ : Z ≠ ⊥ := omega_center_ne_bot T.isPGroup'
  have hNZ : normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure (T : Subgroup G) Z hZ).trans hcontrol
  have hNM : centralizer (U : Set G) ≤ M :=
    (centralizer_le (show omegaOneCenterAmbient (T : Subgroup G) ≤ U from le_normalClosure)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZ)
  let N := centralizer (U : Set G)
  have hn : N.map q = ⊥ := by
    by_contra hz
    let : (N.map q).Normal := (inferInstance : N.Normal).map q hq
    have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot C
      (Group.IsPerfect.not_isMulCommutative C) hC (N.map q) hz
    have hLN : L ≤ N := by
      have hm : L.map q ≤ N.map q := hLC ▸ hle
      have hh := map_le_iff_le_comap.mp hm
      rwa [comap_map_eq_self (hker ▸ hQN)] at hh
    exact hout (hLN.trans hNM)
  exact le_antisymm (hker ▸ (map_eq_bot_iff N).mp hn) hQN

end CFSG.Quasithin.ChapterC
