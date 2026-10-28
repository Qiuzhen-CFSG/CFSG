module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.NormalImage
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.GroupTheory.ProjectedModuleAbsorption

/-!
# The actual projected four-group lies in the component

The first cubic module acts by inner automorphisms because its marked fixed
involution does. Pull it back to the centerless component through the actual
component-normalizer action. The original Sylow intersection gives a normalizer
index at most two; the commutator-module argument then identifies this pullback
with the original four-group. Its fixed involution and the source 1.1.5 actor
force the component to be normal and identify the whole layer.

Source: Aschbacher–Smith 2.4.32–33, printed pp.547–548.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.first_module_le_component
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hzK : center K = ⊥) :
    c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype := by
  let H := involutionCentralizer g.z₂
  let N := normalizer (K : Set H)
  let KN := K.subgroupOf N
  let A := d.block.map d.H.subtype
  let L := A.subgroupOf H
  let LN := L.subgroupOf N
  let U := c.U₁.subgroupOf H
  let UN := U.subgroupOf N
  let R := (sourceR d).subgroupOf H
  have hLH : A ≤ H := g.first_block_le_second_centralizer
  have hLN : L ≤ N := g.first_block_normalizes_component hG K hK
  have hUH : c.U₁ ≤ H := (map_subtype_le _).trans hLH
  have hUL : U ≤ L := by
    intro u hu
    change (u:G) ∈ A
    exact (show c.U₁ ≤ A from map_subtype_le _) hu
  have hUN : U ≤ N := hUL.trans hLN
  let eL : LN ≃* A := (subgroupOfEquivOfLe hLN).trans (subgroupOfEquivOfLe hLH)
  let j : A →* N := LN.subtype.comp eL.symm.toMonoidHom
  let φ := K.normalizerMonoidHom
  let f := φ.comp j
  have hact (l : A) (k : K) : ((f l k : H) : G) = (l:G)*(k:G)*(l:G)⁻¹ := rfl
  obtain ⟨f₀,hf₀,hact₀⟩ := g.faithful_first_block_action hG h K hK
  have heq : f = f₀ := by
    ext l k
    exact (hact l k).trans (hact₀ l k).symm
  have hf : Function.Injective f := heq ▸ hf₀
  have hφL : Function.Injective (φ.comp LN.subtype) := by
    intro l m he
    apply eL.injective
    apply hf
    exact he
  have hφK : Function.Injective (φ.comp KN.subtype) := by
    have bridge (a : KN) : φ (a : N) =
        MulAut.conj ((subgroupOfEquivOfLe K.le_normalizer) a) := by
      apply MulEquiv.ext
      intro k
      rfl
    intro a b he
    have hh := (bridge a).symm.trans (he.trans (bridge b))
    exact (subgroupOfEquivOfLe K.le_normalizer).injective
      (conj_injective_of_center_eq_bot hzK hh)
  have hm : UN.map φ ≤ KN.map φ := by
    have hz := g.first_mem
    change g.z₁ ∈ (blockU A).map A.subtype at hz
    obtain ⟨a,ha,hea⟩ := hz
    have heG : (a:G) = g.z₁ := hea
    have hfa : f a = α := by
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      apply Subtype.ext
      have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
        rw [←mem_centralizer_singleton_iff.mp (k:H).property,mul_inv_cancel_right]
      calc
        ((f a k:H):G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,heG]
        _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
        _ = ((α k:H):G) := by rw [hα]; group
    have hna : a ≠ 1 := by
      intro he
      have hh := g.order_first
      rw [←heG,he] at hh
      norm_num at hh
    have hi := c.cubic_first.module_image_le_normal_of_nontrivial f
      (MulAut.innerSubgroup K) a ha hna (hfa.symm ▸ hinner)
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hvu⟩ := hu
    have hju : j v = u := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvu
    have hii := hi (mem_map_of_mem f hv)
    change f v ∈ (MulAut.conj : K →* MulAut K).range at hii
    rw [show f v = φ u from congrArg φ hju] at hii
    obtain ⟨k,hk⟩ := hii
    refine ⟨⟨k,K.le_normalizer k.property⟩,k.property,?_⟩
    have hφk : φ ⟨k,K.le_normalizer k.property⟩ = MulAut.conj k := by
      apply MulEquiv.ext
      intro x
      rfl
    exact hφk.trans hk
  obtain ⟨P,hP,_⟩ := g.component_action_normalizer_bound hG K hK
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  obtain ⟨P₀,hP₀⟩ := P.exists_subgroupOf_eq_of_normal KN
  have hP₀S : (P₀ : Subgroup KN).map KN.subtype ≤ (P : Subgroup N) := by
    rintro _ ⟨v,hv,rfl⟩
    rw [hP₀] at hv
    exact hv
  have hUS : UN ≤ (P : Subgroup N) := by
    rw [hP]
    intro u hu
    have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
    have hh : ((u:N):G) ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span ▸ mem_sup_left (hUR hu)
    obtain ⟨v,hv,he⟩ := hh
    have hev : v = (u : H) := H.subtype_injective he
    change (u : H) ∈ (g.P₂ : Subgroup H)
    exact hev ▸ hv
  have hc : ⁅UN,LN⁆ = UN := by
    let q : N →* G := H.subtype.comp N.subtype
    have hqi : Function.Injective q := H.subtype_injective.comp N.subtype_injective
    have hLm : LN.map q = A := by
      rw [show q = H.subtype.comp N.subtype from rfl,←map_map,
        map_subgroupOf_eq_of_le hLN,map_subgroupOf_eq_of_le hLH]
    have hUm : UN.map q = c.U₁ := by
      rw [show q = H.subtype.comp N.subtype from rfl,←map_map,
        map_subgroupOf_eq_of_le hUN,map_subgroupOf_eq_of_le hUH]
    apply map_injective hqi
    rw [map_commutator,hLm,hUm]
    have hi := commutator_isPPerfect_idempotent A (pCoreIn 2 A)
      c.first.short.twoPerfect (isPGroup_pCoreIn 2 A)
      (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
    change ⁅(blockU A).map A.subtype,A⁆ = (blockU A).map A.subtype
    simpa only [pCoreIn,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hi
  have hidx : (normalizer (LN : Set N)).relIndex (P : Subgroup N) ≤ 2 := by
    have hRL : R ≤ normalizer (L : Set H) := by
      intro r hr
      have hrB : (r:G) ∈ ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) := by
        rw [c.baumann]
        exact hr
      apply mem_normalizer_iff.mpr
      intro l
      exact mem_normalizer_iff.mp (c.first.normalizes hrB) l
    have hRN : R.subgroupOf N ≤ normalizer (LN : Set N) := by
      rw [show LN = L.subgroupOf N from rfl,←subgroupOf_normalizer_eq hLN]
      exact comap_mono hRL
    have hRP : R.relIndex (g.P₂ : Subgroup H) = 2 := by
      have hh := relIndex_map_map_of_injective R (g.P₂ : Subgroup H) H.subtype_injective
      have hRH : sourceR d ≤ H := fun r hr => mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
      rw [show R.map H.subtype = sourceR d from map_subgroupOf_eq_of_le hRH] at hh
      exact hh.symm.trans g.second_index
    apply (relIndex_le_of_le_left hRN index_ne_zero_of_finite).trans
    rw [hP]
    change (R.comap N.subtype).relIndex ((g.P₂ : Subgroup H).subgroupOf N) ≤ 2
    rw [relIndex_comap]
    exact (relIndex_le_of_le_right (show ((g.P₂ : Subgroup H).subgroupOf N).map N.subtype ≤
      (g.P₂ : Subgroup H) from by rintro _ ⟨v,hv,rfl⟩; exact hv)
      (by rw [hRP]; decide)).trans hRP.le
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 UN := IsElementaryAbelian.subgroupOf hUN
  have hUK : UN ≤ KN := module_le_normal_factor_of_image KN LN UN P φ hφK hφL
    (fun _ hu => hUL hu) hUS P.isPGroup' P₀ hP₀S hc hm hidx
  intro u hu
  let uN : N := ⟨⟨u,hUH hu⟩,hUN hu⟩
  have huN : uN ∈ UN := by
    change u ∈ c.U₁
    exact hu
  exact mem_map_of_mem H.subtype (hUK huN)

/-- Once the actual first four-group lies in K, its fixed involution and
1.1.5 force K to be normal in the literal second centralizer. -/
theorem SourceCentralizerGeometry.component_normal_of_first_module
    (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hU : c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype) : K.Normal := by
  let H := involutionCentralizer g.z₂
  obtain ⟨a,ha,he⟩ := hU g.first_mem
  let b : H := ⟨g.z₂,mem_centralizer_singleton_iff.mpr rfl⟩
  have hb : b ∈ center H := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp u.property
  let zH : H := ⟨g.z₁*g.z₂,h.mem_intersection.1⟩
  have hea : (a : G) = g.z₁ := he
  have hz : zH = a*b := Subtype.ext (by change g.z₁*g.z₂=(a:G)*g.z₂; rw [hea])
  apply hK.normal_of_inner_moving_actor zH a b ha hb hz
  intro D hD
  obtain ⟨_,_,_,_,_,hd⟩ := h.component_inputs D hD
  apply map_injective H.subtype_injective
  rw [map_commutator,MonoidHom.map_zpowers]
  exact hd

/-- The same actual placement supplies the complete 2.4.33 structure. -/
theorem SourceCentralizerGeometry.component_structure_of_first_module
    (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hU : c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥) :
    K.Normal ∧ K = componentLayer (involutionCentralizer g.z₂) ∧
      generalizedFitting (involutionCentralizer g.z₂) = K ⊔ pCore 2 (involutionCentralizer g.z₂) := by
  obtain ⟨a,ha,he⟩ := hU g.first_mem
  have hea : (a : G) = g.z₁ := he
  exact source_component_structure g.z₂ g.P₂ M (g.z₁*g.z₂) h K hK a ha
    (by rw [hea]) ho

end CFSG.Quasithin.Chapter2.DoubleA3
