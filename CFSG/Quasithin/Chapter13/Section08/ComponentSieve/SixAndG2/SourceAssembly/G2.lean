module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.SourceApplication
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.SourceKnown
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal.RankSourceActions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Seed

/-!
# The original derived-G₂ exclusion and surviving group quotients

The original F.9 hypothesis supplies the faithful action on U_H/V₁.
The derived-G₂ component has no rank-one displacement, so the source geometry
selects a strict critical pair with its actual conjugator and rank comparison.
Recognition constructs the natural component section on that same pair.

Two remaining action premises of the parabolic argument are proved here.
The parabolic-fixed cyclic seed makes the action on V_H/U_H faithful.
Component generation and [U_H,Q_H]=V₁ identify the kernel of the plus section.
The parabolic estimates then contradict the natural/Weyl upper bound.
All section maps and both commutator-preimage kernels are literal.

The final application uses the constrained overgroup theorem and the original
counterexample's K-group hypothesis to prove G₁=H=KT and eliminate G₂(2)′
from the surviving quotient list. Earlier component, orbit and field reductions
remain explicit. This proves the group part of 13.8.27; the marked A₆/L₄ modules
and terminal setups remain with `qt-d-138-six-g2-source`, and the original
preceding setup remains with `qt-d-1381-source`.

Source: Aschbacher–Smith, 13.8.27, printed p.963 (PDF p.980),
combined manuscript of 1 March 2004. The G₂ carrier is the derived subgroup,
not the full octonion automorphism group. Atlas attribution is retained in
LICENSES/ATLAS.txt.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.Section02 CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open CriticalGeometry SourceCompletion
open SolvableExclusion.Three.Supercritical.Offenders
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.HigherFieldReduction.ExternalModules
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u

private theorem rank_one_transvection
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E) (g : D)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 1) :
    IsTransvection ρ g := by
  let t := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hr.le)
  have hact (w : E) : ρ g w = w + f w • v := LinearMap.congr_fun he w
  have hne : ρ g ≠ LinearMap.id := by
    intro h
    rw [h, sub_self, LinearMap.range_zero, finrank_bot] at hr
    contradiction
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        change ρ g v = 0
        rw [hact, h, one_smul, ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨f, v, hf, hv, hfv, hact⟩

/-- B.4.2 excludes rank-one displacement on any faithful module for the
actual almost simple derived G₂ actor, including the upper source section. -/
theorem g2_no_rank_one
    {D E : Type*} [Group D] [Finite D] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E) (hf : Function.Injective ρ)
    (C : Subgroup D) (hfit : generalizedFitting D = C)
    (e : C ≃* commutator (Atlas.G2.Model (ZMod 2))) (g : D) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
  let : C.Normal := hfit ▸ inferInstance
  obtain ⟨hq, hc⟩ := G2Parabolic.component_properties_of_fitting C hfit e
  let := hq
  intro hr
  have ht := rank_one_transvection ρ g hr
  apply G2Recognition.no_transvection ρ C hf hc e g ht.ne_one (transvection_square hf ht)
  rwa [fixedCodim_zpowers_eq_displacement_rank]

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem faithful_of_cyclic_g2
    {D E : Type*} [Group D] [Finite D] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) D E) (C P : Subgroup D)
    (hfit : generalizedFitting D = C)
    (e : C ≃* commutator (Atlas.G2.Model (ZMod 2))) (hjoin : C ⊔ P = ⊤)
    (hcyclic : SixRecognition.OppositeUpper.IsParabolicCyclic σ P)
    (hmoved : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  let : C.Normal := hfit ▸ inferInstance
  obtain ⟨hq, hc⟩ := G2Parabolic.component_properties_of_fitting C hfit e
  let := hq
  have hcomp : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases hcomp.normal_dichotomy σ.ker with hC | hC
  · obtain ⟨v, hv, hs⟩ := hcyclic
    let S : Subgroup D := {
      carrier := {g | σ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change σ (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro g hg
        change σ g⁻¹ v = v
        have hh := congrArg (σ g⁻¹) hg
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply] using hh.symm }
    have hS : C ⊔ P ≤ S := sup_le
      (fun g hg => LinearMap.congr_fun (hC hg) v) hv
    have hall (g : D) : σ g v = v := hS (hjoin ▸ mem_top g)
    have hfixed : (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace σ ⊤ := by
      rw [← hs]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change σ g v ∈ fixedSpace σ ⊤
      rw [hall]
      intro a
      exact hall a
    obtain ⟨g, v, hm⟩ := hmoved
    exact (hm (hfixed (by trivial) ⟨g, mem_top g⟩)).elim
  · exact bot_unique ((commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm σ.ker C).trans hC)).trans hc.le)

/-- A displayed star action has the canonical quotient as a binary
conjugation section. Both kernels and representative formulas are retained. -/
private def star_section {U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : SolvableExclusion.Five.StarAction H U Z) (hUH : U ≤ H) (hZU : Z ≤ U) :
    BinaryConjugationSection H U Z
      ((linearAction a).comp (QuotientGroup.mk' (pCore 2 H))) where
  section_le := hUH
  kernel_le := hZU
  normalized := a.normalizes
  coordinates := (MulEquiv.multiplicativeAdditive (U ⧸ Z.subgroupOf U)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Z.subgroupOf U))
  onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel_eq := by ext x; exact QuotientGroup.eq_one_iff x
  equivariant := fun h v => (congrArg Additive.ofMul (a.conjugation h v)).symm

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The upper source module is faithful: a nontrivial kernel would contain
K*, while the parabolic-fixed cyclic seed would then make the whole action
trivial. This proves the faithful-action premise in the G₂ final paragraph. -/
theorem g2_upper_action
    [IsElementaryAbelian 2 (Source.VH H V)]
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ a : SolvableExclusion.Five.StarAction H (Source.VH H V) (Source.UH H V₃),
      Function.Injective (linearAction a) ∧
      Nonempty (BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃)
        ((linearAction a).comp (QuotientGroup.mk' (pCore 2 H)))) := by
  obtain ⟨a, _⟩ := Terminal.exists_rank_section_action d hF9 hHz.2.1 hcomm
  let t := star_section a (conjugateSpanBy_le_self hF9.V_le_H)
    (conjugateSpanBy_mono d.seed_le le_rfl)
  let s : AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.UpperSection
      H (Source.VH H V) (Source.UH H V₃) (linearAction a) := {
    le := t.section_le
    normalizes := t.normalized
    kernel_le := t.kernel_le
    quotient := t.coordinates
    surjective := t.onto
    kernel := t.kernel_eq
    conjugates := fun h v => (t.equivariant h v).symm }
  have hP : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ H := hHz.1.2
  have hnorm : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) := by
    rw [← Comparison.local_edge d hF9]
    exact inf_le_left.trans d.normalizes_V
  obtain ⟨hcyclic, hmoved⟩ := SixRecognition.OppositeUpper.source_cyclic s
    (sourceOne L T V₁ ⊔ (T : Subgroup G)) d.seed_le (Comparison.local_seed_index d) hnorm hnc
  have hgen : Source.starImage H K ⊔ Source.starImage H
      (sourceOne L T V₁ ⊔ (T : Subgroup G)) = ⊤ := by
    rw [Source.starImage, Source.starImage, ← Subgroup.map_sup,
      ← subgroupOf_sup hKH hP, ← hjoin, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  exact ⟨a, faithful_of_cyclic_g2 (linearAction a) _ _ hfit
    ((Components.componentStarEquiv H K hKH hK).symm.trans eK) hgen hcyclic hmoved, ⟨t⟩⟩

/-- In the G₂ branch, the original plus section is faithful. If its kernel
contained K*, component generation would put all U_H in C_UH(Q_H), contrary
to the source commutator [U_H,Q_H]=V₁. -/
theorem g2_plus_kernel
    (hV₃ : V₃ ≤ H) (hline : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2) (hz : H ≤ centralizer (V₁ : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcomm : ⁅Source.UH H V₃, Source.QH H⁆ = V₁)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H := by
  let U := Source.UH H V₃
  let Q := Source.QH H
  let U₀ := U ⊓ centralizer (Q : Set G)
  have hNU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V₃ H
  have hNQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN₀ : H ≤ normalizer (U₀ : Set G) :=
    (le_inf hNU (hNQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hZU : V₁ ≤ U₀ := le_inf hline
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hz))
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction H U U₀ hNU hN₀ (hcomm.le.trans hZU)
  let σ := linearAction a
  let t := star_section a (conjugateSpanBy_le_self hV₃) (show U₀ ≤ U from inf_le_left)
  let C := Source.starImage H K
  let : C.Normal := by
    change (Source.starImage H K).Normal
    rw [← hfit]
    infer_instance
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨hq, hc⟩ := G2Parabolic.component_properties_of_fitting C hfit e
  let := hq
  have hcomp : IsComponent (Source.Hstar H) C :=
    ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases hcomp.normal_dichotomy σ.ker with hC | hC
    · have hKU : ⁅K, U⁆ ≤ U₀ := by
        apply commutator_le.mpr
        intro k hk u hu
        have he : QuotientGroup.mk' (pCore 2 H) ⟨k, hKH hk⟩ ∈ σ.ker :=
          hC (mem_map_of_mem _ hk)
        exact (t.action_mem_ker_iff ⟨k, hKH hk⟩).mp he u hu
      have hUU : U ≤ U₀ :=
        hUK.le.trans ((commutator_comm _ _).le.trans hKU)
      have hzero : ⁅U, Q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (hUU.trans inf_le_right)
      have he : V₁ = ⊥ := hcomm.symm.trans hzero
      have hh := hcard
      rw [he, card_bot] at hh
      contradiction
    · exact bot_unique ((commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_comm σ.ker C).trans hC)).trans hc.le)
  have he := t.action_kernel_map hN₀
  have hk : (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker = pCore 2 H := by
    ext h
    change σ (QuotientGroup.mk' (pCore 2 H) h) = 1 ↔ h ∈ pCore 2 H
    rw [← map_one σ, hf.eq_iff]
    exact QuotientGroup.eq_one_iff h
  rw [hk] at he
  exact he.symm

/-- Recognition and the parabolic contradiction on a source-selected pair.
Only preceding component/orbit facts remain explicit. Both source kernel
identities are proved from generation and the original cyclic seed.
The pair, full section, parabolic marking, strict star inclusion and all three lower rank estimates are constructed. -/
theorem g2_exclusion
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal)
    (hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (orbit : letI : (Source.starImage H K).Normal := hfit ▸ inferInstance
      OrbitInputs ρ (Source.starImage H K) P hP)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  let : ((Source.UH H V₃).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (conjugateSpanBy_le_self hF9.plus_le_H)).mpr
      (le_normalizer_conjugateSpanBy V₃ H)
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨hq, _⟩ := G2Parabolic.component_properties_of_fitting (Source.starImage H K) hfit e
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (f9_commutatorPreimage_eq _ hF9 H le_rfl).le.trans inf_le_right
  have hf := faithful_of_centralizer_le_core ρ hρ hk
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hHz hF9 hjoin hK hN hq
    hcentral hcomm ρ hρ (g2_no_rank_one ρ hf _ hfit e)
  let c := w.pair
  have geo := local_earlierGeometry d hF9 c
  have inputs := CriticalSource.earlier_inputs d hHz hF9 hcentral hcomm ρ hρ
  have hUg : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans geo.Vgamma_H
  have hrev : Source.VH H V ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [← c.vertexGroup_gamma]
    exact geo.VH_endpoint
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) :=
    ⟨by intro he; have := w.positive; rw [he, Representation.BinaryOffender.rank_bot] at this; omega,
      starImage_isElementaryAbelian H _ hUg⟩
  have hidx := c.index_comparison_of_selected_rank V₃ V₁ hUg geo.Dgamma_kernel w.comparison
  have hcrit := Nat.log_mono_right (b := 2) hidx
  let recognized : G2Recognition.SourceHypotheses (K := K) ρ c := {
    seed_le := hF9.plus_le_H
    line_le := d.line_le_uh H
    line_card := d.line_card
    line_central := hF9.H_centralizes
    component_le := hKH
    component := hK
    model := ⟨eK⟩
    fitting := hfit
    conjugates := hρ
    centralizer := hk
    generated := hUK
    sylow := P
    sylow_generation := hP
    orbit := orbit
    forward := hUg
    reverse := (conjugateSpanBy_mono d.seed_le le_rfl).trans hrev
    elementary := hA
    quadratic := w.quadratic_member.2.1
    bound := inputs.estimate c w.positive w.comparison
    critical := hcrit }
  obtain ⟨eK', hs⟩ := G2Recognition.section_model ρ c recognized
  obtain ⟨a, ha, ⟨t⟩⟩ := g2_upper_action d hHz hF9 hcomm inputs.noncentral
    hKH hK hjoin hfit eK
  have hplus := g2_plus_kernel (H := H) (V₃ := V₃) (V₁ := V₁) hF9.plus_le_H (d.line_le_uh H) d.line_card
    hF9.H_centralizes hKH hK hfit hUK
    (Section07.source_commutator_conclusions (localNaturalSetup d) hF9 hHz.2.1 hcomm).2.2.1 eK
  have hno (h : H) : SectionActions.vAction H V V₃ h ≠ 1 →
      binaryLinear (SectionActions.vAction H V V₃ h) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Vsection H V V₃)) := by
    intro hn ht
    have he : a.action (QuotientGroup.mk' (pCore 2 H) h) = SectionActions.vAction H V V₃ h := by
      ext v
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ v
      exact (a.conjugation h v).trans (SectionActions.quotientAction_apply H
        (Source.VH H V) (Source.UH H V₃) _ _ h v).symm
    have hr := LinearEquiv.mem_dilatransvections_iff_finrank.mp
      (LinearEquiv.transvections_subset_dilatransvections ht)
    have hn1 := g2_no_rank_one (linearAction a) ha _ hfit e (QuotientGroup.mk' (pCore 2 H) h)
    have hr' : Module.finrank (ZMod 2)
        (LinearMap.range ((linearAction a) (QuotientGroup.mk' (pCore 2 H) h) - LinearMap.id)) ≤ 1 :=
      (congrArg (fun α : MulAut (Source.Vsection H V V₃) => Module.finrank (ZMod 2)
        (LinearMap.range ((binaryLinear α).toLinearMap - LinearMap.id))) he).le.trans hr
    have hz : Module.finrank (ZMod 2)
        (LinearMap.range ((linearAction a) (QuotientGroup.mk' (pCore 2 H) h) - LinearMap.id)) = 0 := by
      omega
    have hz' := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    have hid := sub_eq_zero.mp hz'
    apply hn
    ext v
    have hh := LinearMap.congr_fun hid (Additive.ofMul v)
    change a.action (QuotientGroup.mk' (pCore 2 H) h) v = v at hh
    rwa [he] at hh
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hgen := w.generation (Source.UH H V₃) le_rfl (not_le_of_gt w.strict_base)
  have hedge := c.edge_commutator_le_of_flag V₃ d.seed_le inputs.flag_index
    inputs.noncentral inputs.edge_normalizes
  have hproper := (SectionActions.CriticalPair.strict_star_of_no_v_transvection c V₃ V₁
    d.seed_le hF9.V_le_H geo.Vgamma_H
    ((conjugateSpanBy_mono d.seed_le le_rfl).trans geo.VH_endpoint) (d.line_le_uh H)
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point d.line_card hgen hedge inputs.noncentral hA.1 hno).1
  have hHC : H = centralizer (V₁ : Set G) := by
    rw [hH, d.first_normalizer]
    exact le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _)
  have hVQ : Source.VH H V ≤ Source.QH H :=
    Section07.VH_le_core (localNaturalSetup d) hF9
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have hsmall : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := hF9.commutator_UH_QH_le_point
  exact G2Parabolic.source_exclusion_of_earlier_geometry c hF9.V_le_H d.seed_le
    (d.line_le_uh H) d.line_card hF9.H_centralizes hKH hK ρ hρ
    hk hUK eK' hs hUg hrev hVQ hA
    (starImage_isElementaryAbelian H c.Vgamma geo.Vgamma_H) hproper hHC w.comparison
    (by simpa only [commutator_comm] using hsmall)
    hplus (linearAction a) t ha hfit

private theorem source_ambient_sqtk
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    IsSQTK KnownSimple.IsKnownSimple (G₁ ⧸ pCore 2 G₁) := by
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hn : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    contradiction
  have hloc : IsTwoLocal G₁ := ⟨V₁, hn, hp, d.first_normalizer⟩
  have hG := d.counterexample.qtke.twoLocal_sqtk hloc
  refine ⟨?_, hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G₁) pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

open scoped Pointwise in
/-- The original surviving quotient sieve with its G₂ branch removed and
its overgroup equality proved. The L₄ branch retains the covered local
quotient and the whole-star quotient. This is the group part of 13.8.27;
the marked modules and case-one symmetry are assembled separately. -/
theorem surviving_source_quotients
    (embeddings : EarlierEmbeddings.{u} KnownSimple.IsKnownSimple)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (orbit : letI : (Source.starImage H K).Normal := hfit ▸ inferInstance
      OrbitInputs ρ (Source.starImage H K) P hP) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      (IsAlternating (K ⧸ pCore 2 K) 6 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 ∧
        IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
        ClassicalGroup.IsPSL (H ⧸ pCore 2 H) 4 2) := by
  have hQ := source_ambient_sqtk d
  obtain ⟨hc, hn, hGH, hKT⟩ :=
    Overgroup.Rigidity.source_equalities embeddings d facts hHz hKH hK hQ
  refine ⟨hc, hn, hGH, hKT,
    (Overgroup.Rigidity.source_set_product embeddings d facts hHz hKH hK hQ).2, ?_⟩
  rcases Overgroup.surviving_quotient facts hHz hKH hK with h6 | hrest
  · exact Or.inl h6
  rcases hrest with h4 | hg2
  · have hh := facts.binaryReduction hHz hKH hK (by decide : 3 ≤ 4)
      (by decide : 4 ≤ 5) h4
    exact Or.inr ⟨h4, hh.2⟩
  · obtain ⟨eK⟩ := hg2
    have hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
      rw [← sup_assoc, sup_eq_left.mpr (facts.base_le hHz hKH hK)]
      exact hKT
    exact (g2_exclusion d hHz hF9 hGH.symm hKH hK (facts.normal hHz hKH hK)
      hjoin hfit hUK hcentral hcomm ρ hρ P hP orbit eK).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
