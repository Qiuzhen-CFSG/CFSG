module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRestriction

/-!
# Exceptional rank-one geometry on the original Chapter 12 setup

An outside subgroup centralizing Ω₁(Z(T)) forces C_{Ω₁(Z(T))}(L)=1:
a nonidentity central involution would put both LT and H in the unique
maximal local N_G(L). This proves the centralizer-disjointness step of
5.1.14(3) from its earlier centralization assertion, without assuming an
A₅ module or T-invariance of the chosen Irr⁺ subgroup.

The L₃(4) application constructs the relative C-component using the earlier
residual centralization and uniqueness facts. The other application
transports each actual A₇/J₂/M₂₃ quotient model of an ambient component
into the literal omega centralizer. The full-layer module input remains
explicit in both applications. Once an exceptional exit is supplied,
restriction identifies the original chosen module and forces n=2.

These are conditional source applications. The L₃(4) analysis of 5.1.14
and the Cartan-escape analysis of 5.1.13--5.2.2 are still to be proved;
this module does not assert 5.2.3 or the universal exceptional exit.
Source: Aschbacher--Smith, pp.635--649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

namespace ChosenModule
variable (D : ChosenModule T L V)
include D

/-- Original 5.1.14(3) follows from centralization by the actual outside H. -/
theorem centralOmega_disjoint_of_outside_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  apply eq_bot_iff.mpr
  intro z hz
  by_contra hzone
  have hz1 : z ≠ 1 := fun heq => hzone (mem_bot.mpr heq)
  have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1
  have hCC : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      centralizer ({z} : Set G) := centralizer_le (Set.singleton_subset_iff.mpr hz.1)
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hzT.2.1 hz1))
  have hLC : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hz.2 l hl)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
  have hNM : N = normalizer (L : Set G) := by
    have hh := hu.normalizer_unique N hN
    rw [he] at hh
    exact hh ((sup_le hLC hTC).trans hCN)
  exact hH.1.2 (hNM ▸ hHC.trans (hCC.trans hCN))
/-- Apply the proved relative-residual transport to the original L₃(4)
branch. The earlier whole-layer, centralization and uniqueness inputs remain. -/
theorem rankOne_exceptional_linear_of_source
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L))
    (hRC : residual H ≤ omegaCentralizer T)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
      N = normalizer (residual H : Set G)) :
    RankOneModule.ExceptionalExit T L H := by
  have hT : (T : Subgroup G) ≠ ⊥ := fun hb =>
    D.ne_bot (bot_unique (hb ▸ D.le_sylow))
  obtain ⟨KZ, hKZ, he⟩ := linear_residual_component_of_unique hT hH.1.1.2 hRC hu hlinear
  exact ⟨hmodel, KZ, hKZ, he.le, Or.inr ⟨he, hlinear⟩⟩

omit [Finite G] in
/-- The whole-layer exit supplies the original chosen model and binary exponent. -/
theorem rankOne_exceptional_module_and_exponent
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hex : RankOneModule.ExceptionalExit T L H) :
    n = 2 ∧ Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  have hm := D.a5_model_of_one_or_two_on_overgroup D.le_rankOne_commutatorLayer hex.1
  refine ⟨?_, hm⟩
  obtain ⟨e, _⟩ := hm
  exact Chapter6.Source.exponent_eq_two_of_psl_and_a5 hn hpsl e

end ChosenModule

namespace RankOneModule

omit [Finite G] in
/-- Transfer each source quotient isomorphism along the literal relative
component inclusion, preserving its residual containment. -/
theorem exceptional_of_ambient_component
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4)
    {X : Subgroup G} (hXC : X ≤ omegaCentralizer T)
    (hX : (X.subgroupOf (omegaCentralizer T)).IsCComponent)
    (hRX : residual H ≤ X)
    (hm : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    ExceptionalExit T L H := by
  let e := subgroupOfEquivOfLe hXC
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨hmodel, X.subgroupOf (omegaCentralizer T), hX, ?_, Or.inl ⟨hlinear, ?_⟩⟩
  · simpa only [map_subgroupOf_eq_of_le hXC] using hRX
  · exact hm.imp (fun hf => hf.map (fun f => q.trans f))
      (fun hf => hf.imp (fun hf => hf.map (fun f => q.trans f))
        (fun hf => hf.map (fun f => q.trans f)))

end RankOneModule
end CFSG.Quasithin.Chapter12.Section02
