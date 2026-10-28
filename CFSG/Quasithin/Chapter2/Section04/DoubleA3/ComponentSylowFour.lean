module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowR
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.CubicModel
/-!
# The original normal four-group in the component Sylow

The centerless component's actual Sylow intersection lies in R, which
normalizes the first cubic module. Normality carries its x-conjugate into the
same Sylow. The source noncommutation therefore makes this four-group
noncentral in the intrinsic Sylow of the component.

Source: Aschbacher–Smith, 2.4.32, printed p.547. This retains the original
component, involution centralizer, Sylow intersection, and right conjugator.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.component_sylow_normal_four
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hzK : center K = ⊥)
    (hU : c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype) :
    let U := (c.U₁.subgroupOf (involutionCentralizer g.z₂)).subgroupOf K
    ∃ P : Sylow 2 K,
      (P : Subgroup K) = (g.P₂ : Subgroup (involutionCentralizer g.z₂)).subgroupOf K ∧
      IsElementaryAbelian 2 U ∧ Nat.card U = 4 ∧
      U ≤ (P : Subgroup K) ∧
      (P : Subgroup K) ≤ normalizer (U : Set K) ∧
      ¬ U.subgroupOf (P : Subgroup K) ≤ center (P : Subgroup K) := by
  let H := involutionCentralizer g.z₂
  let UH := c.U₁.subgroupOf H
  let U := UH.subgroupOf K
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hRH : sourceR d ≤ H := fun r hr => mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  have hUH : c.U₁ ≤ H := hUR.trans hRH
  have hUK : UH ≤ K := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hU hu
    exact H.subtype_injective he ▸ hv
  have hUP : UH ≤ (g.P₂ : Subgroup H) := by
    intro u hu
    have hh : (u:G) ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_left (hUR hu)
    obtain ⟨v,hv,he⟩ := hh
    exact H.subtype_injective he ▸ hv
  obtain ⟨P,hP⟩ := g.P₂.exists_subgroupOf_eq_of_normal K
  have hUPK : U ≤ (P : Subgroup K) := by
    rw [hP]
    exact fun u hu => hUP hu
  have hPR : ∀ p : P, ((p:K):G) ∈ sourceR d := by
    intro p
    apply g.component_sylow_le_sourceR K hzK
    refine ⟨mem_map_of_mem H.subtype (p:K).property,?_⟩
    have hp : (p:K) ∈ (P : Subgroup K) := p.property
    rw [hP] at hp
    exact mem_map_of_mem H.subtype hp
  have hPN : (P : Subgroup K) ≤ normalizer (U : Set K) := by
    intro p hp
    apply mem_normalizer_iff.mpr
    intro u
    have hrB : (p:G) ∈ ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) := by
      rw [c.baumann]
      exact hPR ⟨p,hp⟩
    exact mem_normalizer_iff.mp (c.first.coordinates.normalizes hrB) (u:G)
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 UH := IsElementaryAbelian.subgroupOf hUH
  have hUE : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUK
  have hcard : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).trans
        (RankOneSetup.cubic_module_card c.cubic_first))
  refine ⟨P,hP,hUE,hcard,hUPK,hPN,?_⟩
  intro hcent
  apply c.noncommuting
  rintro _ ⟨a,ha,rfl⟩ b hb
  let x : H := ⟨c.x,g.x_second⟩
  have hxP : x ∈ (g.P₂ : Subgroup H) := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    exact (show v = x from Subtype.ext he) ▸ hv
  let aH : H := ⟨a,hUH ha⟩
  let bH : H := ⟨b,hUH hb⟩
  have haK : aH ∈ K := hUK ha
  have hbK : bH ∈ K := hUK hb
  let v : K := ⟨x⁻¹*aH*x,by simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem aH haK x⁻¹⟩
  have hvP : v ∈ (P : Subgroup K) := by
    rw [hP]
    change x⁻¹*aH*x ∈ (g.P₂ : Subgroup H)
    exact (g.P₂ : Subgroup H).mul_mem ((g.P₂ : Subgroup H).mul_mem
      ((g.P₂ : Subgroup H).inv_mem hxP) (hUP ha)) hxP
  let w : K := ⟨bH,hbK⟩
  have hwU : w ∈ U := hb
  have hc := mem_center_iff.mp (hcent (show (⟨w,hUPK hwU⟩ : P) ∈ U.subgroupOf (P : Subgroup K) from hwU)) ⟨v,hvP⟩
  have hcG := congrArg (fun t : P => (((t:K):H):G)) hc.symm
  change b*(c.x⁻¹*a*c.x) = (c.x⁻¹*a*c.x)*b at hcG
  simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,inv_inv] using hcG
end CFSG.Quasithin.Chapter2.DoubleA3
