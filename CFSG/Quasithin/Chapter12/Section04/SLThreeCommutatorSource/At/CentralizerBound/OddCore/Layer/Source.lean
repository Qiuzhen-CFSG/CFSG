module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore.Layer.Marked
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore.Closure.Source
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.Exclusion
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.SourceKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceSevenEscape
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The odd-core layer and final exclusion in 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

A failed plane-core inclusion invokes the pointwise E.6.19 detector, whose
proved model inspection leaves A₇ and its perfect triple cover. On either
cover, V centralizes the fixed subgroup of the original involution z because
C_G(z) = N_G(V) and the plane's local centralizer equals C_G(V). Fixed-point
lifting and the seven-point double centralizer therefore restrict V's
component action to {1,z}.

The genuine E.6.8 escaping hyperplane then centralizes the whole component:
a nontrivial action would make its component centralizer lie in C_G(z).
Restriction preserves the ordinary component, contradicting the already
proved hyperplane component exclusion. Thus every plane-core inclusion
holds. The abelian plane core centralizes the ordinary layer, and the
constructed odd conjugate closure finishes the source odd-core contradiction.
All component normality and subgroup maps are relative to their literal
centralizers. No E.6.18 exclusion or global balance theorem is assumed.

Source: Aschbacher–Smith 12.4.8, printed pp.815–816, with the pointwise
component detector from E.6.19, printed p.252.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
open ChapterE ChapterE.Section06 ChapterE.Section06.Hyperplanes
open ComponentBalance ComponentBalance.OddObstruction
open Components.RemainingSieve.AlternatingActions
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

private theorem seven_quotient {X : Type*} [Group X]
    (h : Chapter1.Section02.LocalModels.IsAlternating X 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover X 7) :
    Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have hz : center X = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by simp), card_bot]
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e⟩
  · exact h.2.2

/-- The exceptional plane component is impossible in the original marked
four-dimensional module. -/
theorem no_seven_plane (c : Configuration T L V U)
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 1)
    (J : Subgroup G) (hJ : CentralizerComponent W J) (hs : IsSeven J) : False := by
  let _ := c.chosen.elementary
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 W hWU hcor
  have hn : V ≤ normalizer (J : Set G) := Components.RemainingSieve.component_normalized hE hg.2.2.2 hJ
  obtain ⟨z,hz,hfix,hM⟩ := fixed_involution c
  obtain ⟨S,_,hmark⟩ := marked_centralizer c z hz hfix hM W
    (hWU.trans c.le_module) hg.2.2.2.2.1 (c.sylow_centralizers.2 W hWU hcor)
  let H := centralizer (W : Set G)
  let D := J.subgroupOf H
  let eD : D ≃* J := subgroupOfEquivOfLe hJ.1
  let _ : IsQuasisimple D := hJ.2.2
  obtain ⟨_,α,P,ha,d,_⟩ := hmark.component_inputs D hJ.2
  obtain ⟨eQ⟩ := seven_quotient (hs.of_equiv eD.symm)
  let ψ : V →* MulAut D := (MulAut.congr eD.symm).toMonoidHom.comp (actionHom hn)
  have hψ (v : V) (x : D) : ((ψ v x : H) : G) = (v : G) * (x : G) * (v : G)⁻¹ := rfl
  have hsmall (v : V) : ψ v = 1 ∨ ψ v = α := by
    apply SLThreeCommutatorSource.CentralizerBound.OddCore.marked_seven_fixed_fixer d eQ
    intro x hx
    have hxz : (x : G) ∈ centralizer ({z} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun y : D => ((y : H) : G)) ((MulAut.mem_fixedSubgroup _ _).mp hx)
      rw [ha] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hxV : (x : G) ∈ centralizer (V : Set G) :=
      hg.2.2.1.le ⟨hM.symm ▸ hxz, x.val.property⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [hψ, hxV v v.property, mul_inv_cancel_right]
  obtain ⟨A,⟨hAV,hAcor⟩,hWA,houtA⟩ :=
    Components.RemainingSieve.source_sevenEscape hE W hg.2.2.2 J hJ hs
  have hJA : J ≤ centralizer (A : Set G) := by
    by_contra hnot
    have hex : ∃ a : A, ψ ⟨a,hAV a.property⟩ ≠ 1 := by
      by_contra! he
      apply hnot
      intro j hj a haA
      have hh := congrArg (fun b : MulAut D => ((b (eD.symm ⟨j,hj⟩) : H) : G))
        (he ⟨a,haA⟩)
      change a * j * a⁻¹ = j at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh)
    obtain ⟨a,hane⟩ := hex
    have hea : ψ ⟨a,hAV a.property⟩ = α := (hsmall _).resolve_left hane
    apply houtA
    intro j hj
    rw [hM]
    apply mem_centralizer_singleton_iff.mpr
    have hh : ψ ⟨a,hAV a.property⟩ (eD.symm ⟨j,hj.1⟩) = eD.symm ⟨j,hj.1⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hψ]
      change (a : G) * j * (a : G)⁻¹ = j
      rw [hj.2 a a.property, mul_inv_cancel_right]
    rw [hea] at hh
    have hv := congrArg (fun y : D => ((y : H) : G)) hh
    rw [ha] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hescape : ¬ centralizer (A : Set G) ≤ normalizer (V : Set G) :=
    fun h => houtA (inf_le_right.trans h)
  let cA : Configuration T L V A :=
    ⟨c.hypothesis,c.chosen,c.extension,c.fixed_nontrivial,c.structural,
      c.normalizer_action,hAV,hAcor,hescape⟩
  exact cA.component_false ((show IsComponentIn J H from hJ).restrict hJA (centralizer_le hWA))

/-- Failure of the literal plane-core inclusion is detected by E.6.19;
the exceptional component contradicts the original module action. -/
theorem core_le_plane_core (c : Configuration T L V U)
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 1) :
    core U ≤ core W := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.le_module
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 W hWU hcor
  have hindex : W.relIndex U = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
      hcor, pow_one]
  have hi : W.relIndex V = 4 := by
    have he := relIndex_mul_relIndex W U V hWU c.le_module
    have hu : U.relIndex V = 2 := by
      rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
        c.corank, pow_one]
    rw [hindex,hu] at he
    exact he.symm
  have hc : subgroupCorank V W = 2 := by
    change Nat.log 2 (W.relIndex V) = 2
    rw [hi]
    decide
  by_contra hfail
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  obtain ⟨J,d⟩ := source_detectedComponent hE hg.2.2.2 hWU c.le_module hfail
  have hs := detected_isSeven_of_adequate hE hg.2.2.2 hc c.le_module hindex d
    (adequate_models_knownSimple hE W hg.2.2.2 J d.component)
  exact no_seven_plane c W hWU hcor J d.component hs

/-- The original embedded odd core centralizes the ordinary layer of each
plane centralizer. Its abelian odd core is a solvable normal subgroup. -/
theorem core_centralizes_plane_layer (c : Configuration T L V U)
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 1) :
    core U ≤ centralizer ((componentLayer (centralizer (W : Set G))).map
      (centralizer (W : Set G)).subtype : Set G) := by
  let H := centralizer (W : Set G)
  obtain ⟨_,_,_,_,_,_,hcomm⟩ := simultaneous_inversion c
  let : IsMulCommutative (core W) := (hcomm W hWU hcor).2
  let e : pPrimeCore 2 H ≃* core W :=
    (pPrimeCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let : IsMulCommutative (pPrimeCore 2 H) :=
    isMulCommutative_iff.mpr (fun x y => e.injective (by simp only [map_mul,mul_comm]))
  have hh := componentLayer_le_centralizer_solvable_normal (pPrimeCore 2 H)
  intro x hx
  obtain ⟨a,ha,rfl⟩ := core_le_plane_core c W hWU hcor hx
  rintro y ⟨b,hb,rfl⟩
  exact congrArg Subtype.val ((hh hb a ha).symm)

/-- The final ordinary-layer input, with all local and model premises discharged. -/
theorem layerCentralization : LayerCentralization.{u} := by
  intro G _ _ T L V U c _ W hWU hcor
  exact core_centralizes_plane_layer c W hWU hcor

/-- Original 12.4.8's odd-core case, including the layer and abelian-closure
arguments, with no remaining local input. -/
theorem oddCoreExclusion : OddCoreExclusion.{u} :=
  oddCoreExclusion_of_layer layerCentralization

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
