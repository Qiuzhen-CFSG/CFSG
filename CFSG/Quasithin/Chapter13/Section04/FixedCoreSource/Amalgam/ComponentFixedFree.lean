module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLineOrbits
public import Theory.GroupTheory.PGroup.OmegaCentralizerDetection

/-!
# No component-fixed vectors in the original omega module

For the actual original pair, the two fixed lines are disjoint. Since X=KT
and T centralizes its omega-center, this makes C_{Ω₁Z(T)}(K) trivial. The
omega module is elementary abelian and lies in T. If its K-fixed subgroup
were nontrivial, Sylow normalization would give a nonidentity fixed point
in Ω₁Z(T), a contradiction. Thus C_{V₀}(K)=1, for every selected component;
no linear-model assumption is needed.

LinearFixedFree uses this to remove the constant part of each permutation
quotient. Structural1222 and Source1332OneTwo remain genuine preceding
inputs with final discharge in the fixed-core assembly.
Source: Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem original_pair_component_fixed_free
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
 :
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    U ⊓ centralizer (C : Set G) = ⊥ := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  have he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  have hUT : U ≤ (T : Subgroup G) := by
    intro u hu
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTX) (hred.le_pCore (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu))
  have hTC := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  have hgen := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  have hdis := (original_pair_fixed_lines h structural D m hout
    hindexL hindexA hindexB hd).2.2.2.1
  have hZ : Z ⊓ centralizer (C : Set G) = ⊥ := by
    apply bot_unique
    intro z hz
    have hCX : X ≤ centralizer ({z} : Set G) := by
      change A ⊔ B ≤ _
      rw [hgen]
      exact sup_le (fun c hc => mem_centralizer_singleton_iff.mpr (hz.2 c hc))
        (fun t ht => mem_centralizer_singleton_iff.mpr
          (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht))
    apply hdis.le
    exact ⟨⟨hz.1,fun a ha => mem_centralizer_singleton_iff.mp (hCX ((show A ≤ X from le_sup_left) ha))⟩,
      hz.1,fun b hb => mem_centralizer_singleton_iff.mp (hCX ((show B ≤ X from le_sup_right) hb))⟩
  exact inf_centralizer_eq_bot_of_omega_disjoint T C U he hUT
    (hTX.trans (le_normalizer_conjugateSpanBy Z X)) hTC hZ
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
