module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Centralizers
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActions
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentStructure
public import Theory.SpecificGroups.AlternatingSix.FourGroupMovement
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree

/-!
# Correlated component geometry after the paired-cubic selection

The original first block and the opposite four-group act on the selected
ordinary component. The two-model conclusion of 2.4.32 and the noncentrality
of 2.4.34 select A₆ and mark an actual opposite-module element as a
transposition. The original outside conjugator moves the first four-group,
so its action is outside natural S₆, while all of J(S) acts naturally.
The original centralizers, Sylow subgroup, involutions, component and right
conjugator are retained in the terminal source record.

The actual selection in 2.4.32 and the fusion argument in 2.4.34 remain
explicit inputs. Normality, the complete action step 2.4.35, and all carrier
transports are proved here. Source: Aschbacher–Smith, printed pp.547–548.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual component and noncentrality conclusions of 32 and 34 supply
all of the terminal component geometry, with the original right conjugator. -/
theorem SourceCentralizerGeometry.component_geometry_of_two_models
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* A6) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hVK : ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂))) :
    ∃ b : SourceComponentGeometry d, b.z = g.z₂ ∧ b.s = c.s⁻¹ ∧
      (b.z₁ : G) = g.z₁ ∧ (b.u : G) ∈ c.U₂ ∧ (b.x : G) = c.x ∧
      b.K.map (involutionCentralizer b.z).subtype = K.map (involutionCentralizer g.z₂).subtype ∧
      (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
        (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype := by
  let H := involutionCentralizer g.z₂
  let L := (d.block.map d.H.subtype).subgroupOf H
  let U := c.U₁.subgroupOf H
  let V := c.U₂.subgroupOf H
  let R := (sourceR d).subgroupOf H
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hVR : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hRH : sourceR d ≤ H := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  have hLH : d.block.map d.H.subtype ≤ H := hLK.trans (map_subtype_le _)
  have hUH : c.U₁ ≤ H := hUR.trans hRH
  have hVH : c.U₂ ≤ H := hVR.trans hRH
  have hUK : U ≤ K := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hLK ((map_subtype_le _) hu)
    exact H.subtype_injective he ▸ hv
  have hLKi : L ≤ K := by
    intro l hl
    obtain ⟨v,hv,he⟩ := hLK hl
    exact H.subtype_injective he ▸ hv
  obtain ⟨eL⟩ := ChapterC.IsAlternatingBlock.equiv_alternatingFour c.cubic_first
  let eLi : L ≃* alternatingGroup (Fin 4) := (subgroupOfEquivOfLe hLH).trans eL
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  have hUcard : Nat.card U = 4 := (Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).trans
    (RankOneSetup.cubic_module_card c.cubic_first)
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hUcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hVL : V ≤ centralizer (L : Set H) := by
    intro v hv l hl
    apply Subtype.ext
    exact c.commute ((map_subtype_le _) hv) l hl
  have hRN : R ≤ normalizer (U : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro u
    have hrB : (r : G) ∈ ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) := by
      rw [c.baumann]
      exact hr
    exact mem_normalizer_iff.mp (c.first.coordinates.normalizes hrB) u
  obtain ⟨eK,u,hu,σ,hσ,ha,hn⟩ := marked_actions_of_two_component_models K L V U R
    hLKi hUK eLi hmodel (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) hVL hVK hRN
  let x : H := ⟨c.x,g.x_second⟩
  have hUP : U ≤ (g.P₂ : Subgroup H) := by
    intro u hu
    have hh : (u : G) ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_left (hUR hu)
    obtain ⟨v,hv,he⟩ := hh
    exact H.subtype_injective he ▸ hv
  have hxP : x ∈ (g.P₂ : Subgroup H) := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    exact (show v = x from Subtype.ext he) ▸ hv
  have hm : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set H) := by
    intro hh
    apply c.noncommuting
    rintro _ ⟨v,hv,rfl⟩ w hw
    let vH : H := ⟨v,hUH hv⟩
    let wH : H := ⟨w,hUH hw⟩
    exact congrArg Subtype.val (hh (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom
      (show vH ∈ U from hv)) wH hw)
  have hx := conjugationAction_not_natural_of_four_movement K eK
    (g.P₂ : Subgroup H) U g.P₂.isPGroup' hUK hUP x hxP hm
  let z₁ : H := ⟨g.z₁,hUH g.first_mem⟩
  have hRP : R ≤ (g.P₂ : Subgroup H) := by
    intro r hr
    have hh : (r : G) ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_left hr
    obtain ⟨v,hv,he⟩ := hh
    exact H.subtype_injective he ▸ hv
  let b : SourceComponentGeometry d := {
    z := g.z₂
    involution := g.order_second ▸ pow_orderOf_eq_one g.z₂
    nonidentity := fun he => by
      have hh := g.order_second
      simp [he] at hh
    K := K
    normal := inferInstance
    componentEquiv := eK
    thompson_le := hRH
    S₁ := g.P₂
    thompson_sylow := hRP
    u := u
    x := x
    σ := σ
    swap := hσ
    transposition := ha
    outside_natural := hx
    natural_thompson := hn
    s := c.s⁻¹
    z₁ := z₁
    first_in_thompson := hUR g.first_mem
    first_in_component := hUK g.first_mem
    exchange := by simpa using g.exchange }
  exact ⟨b,rfl,rfl,rfl,hu,rfl,rfl,rfl⟩

/-- The ordinary component supplied before 32, its absorption/two-model
conclusion, and the noncentrality of 34 construct the same actual geometry.
Normality is discharged by the original marked 1.1.5 actor. -/
theorem SourceCentralizerGeometry.component_geometry_of_component_models
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* A6) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hVK : ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂))) :
    ∃ b : SourceComponentGeometry d, b.z = g.z₂ ∧ b.s = c.s⁻¹ ∧
      (b.z₁ : G) = g.z₁ ∧ (b.u : G) ∈ c.U₂ ∧ (b.x : G) = c.x ∧
      b.K.map (involutionCentralizer b.z).subtype = K.map (involutionCentralizer g.z₂).subtype ∧
      (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
        (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype := by
  have hz : g.z₁ ∈ K.map (involutionCentralizer g.z₂).subtype :=
    hLK ((map_subtype_le _) g.first_mem)
  obtain ⟨a,ha,he⟩ := hz
  have hprod : g.z₁*g.z₂ = (a:G)*g.z₂ := congrArg (· * g.z₂) he.symm
  let : K.Normal := (source_component_structure g.z₂ g.P₂ M (g.z₁*g.z₂)
    h K hK a ha hprod ho).1
  exact g.component_geometry_of_two_models K hLK hmodel hVK

end CFSG.Quasithin.Chapter2.DoubleA3
