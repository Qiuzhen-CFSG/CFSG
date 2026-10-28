module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralizerGeneration
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CoreDihedral
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree

/-!
# The source36 centralizer in the original paired-cubic coordinates

The actual first-block centralizer in R is D × D₈. Transporting this literal
subgroup to the selected involution centralizer and using uniqueness of its
component-centralizing involution forces |D|=1, |R|=64, and C_R(K)≃C₄. This
conclusion is available before the source37 fusion bound. The final consumer
uses the original Sylow images, exchange element and odd-core conclusion to
construct the direct factors and apply the terminal count.

Only the correlated component selection from 32–35, normality in each required
involution centralizer from the first paragraph of 36, and the fusion bound
from 37 remain original-source inputs. Product coordinates, cardinalities,
Sylow indices and conjugator memberships are discharged here.
Source: Aschbacher–Smith, 2.4.36–37, printed pp.549–550.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private noncomputable def intrinsicCentralizerEquiv
    (R L H : Subgroup G) (hRH : R ≤ H) (hLH : L ≤ H) :
    ((R.subgroupOf H) ⊓ centralizer (L.subgroupOf H : Set H) : Subgroup H) ≃*
      (R ⊓ centralizer (L : Set G) : Subgroup G) := by
  let B := R.subgroupOf H ⊓ centralizer (L.subgroupOf H : Set H)
  let f : B →* (R ⊓ centralizer (L : Set G) : Subgroup G) :=
    (H.subtype.comp B.subtype).codRestrict _ (by
      intro r
      refine ⟨r.property.1,?_⟩
      intro l hl
      exact congrArg H.subtype (r.property.2 ⟨l,hLH hl⟩ hl))
  apply MulEquiv.ofBijective f
  constructor
  · intro r t he
    have hh := congrArg (fun a : (R ⊓ centralizer (L:Set G) : Subgroup G) => (a:G)) he
    exact Subtype.ext (Subtype.ext hh)
  · intro r
    let rH : H := ⟨r,hRH r.property.1⟩
    have hrB : rH ∈ B := by
      refine ⟨r.property.1,?_⟩
      intro l hl
      exact Subtype.ext (r.property.2 l hl)
    exact ⟨⟨rH,hrB⟩,rfl⟩

/-- Before the fusion step, the original component-centralizer normality
forces the elementary supplement to vanish and R to have order 64. It also
identifies the literal C_R(K) with the cyclic group of order four. -/
theorem SourceCentralizerGeometry.component_centralizer_cyclic_four
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c) (b : SourceComponentGeometry d)
    (hz : b.z = g.z₂) (hs : b.s = c.s⁻¹) (hu : (b.u:G) ∈ c.U₂)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype)
    (hG : IsQuasithin G)
    (hn : ∀ r : involutionCentralizer b.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer b.z) →
      r ∈ centralizer (b.K : Set (involutionCentralizer b.z)) → orderOf r = 2 →
      centralizer ({(r:G)} : Set G) ≤
        normalizer (b.K.map (involutionCentralizer b.z).subtype : Set G)) :
    Nat.card c.D = 1 ∧ Nat.card (sourceR d) = 64 ∧
      Nonempty (((sourceR d).subgroupOf (involutionCentralizer b.z) ⊓
        centralizer (b.K : Set (involutionCentralizer b.z)) : Subgroup (involutionCentralizer b.z)) ≃*
          Multiplicative (ZMod 4)) := by
  let H := involutionCentralizer b.z
  let L := (d.block.map d.H.subtype).subgroupOf H
  have hLH : d.block.map d.H.subtype ≤ H := hLK.trans (map_subtype_le _)
  have hLKi : L ≤ b.K := by
    intro l hl
    obtain ⟨k,hk,he⟩ := hLK hl
    exact H.subtype_injective he ▸ hk
  obtain ⟨eL⟩ := ChapterC.IsAlternatingBlock.equiv_alternatingFour c.cubic_first
  let eLi : L ≃* alternatingGroup (Fin 4) := (subgroupOfEquivOfLe hLH).trans eL
  have hUR : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have huR : b.u ∈ (sourceR d).subgroupOf H := hUR hu
  have huL : b.u ∈ centralizer (L : Set H) := by
    intro l hl
    exact Subtype.ext (c.commute ((map_subtype_le _) hu) l hl)
  let : IsElementaryAbelian 2 c.D := c.product.2.2.2
  obtain ⟨eC⟩ := c.first_block_centralizer_dihedral
  let eCi := (intrinsicCentralizerEquiv (sourceR d) (d.block.map d.H.subtype)
    H b.thompson_le hLH).trans eC
  have hzR : b.z ∈ sourceR d := hz ▸ hUR g.second_mem
  have hs2R : b.s^2 ∈ sourceR d := by
    rw [hs,inv_pow]
    exact (sourceR d).inv_mem c.exchange_square_mem
  obtain ⟨hD,hC⟩ := b.centralizer_cyclic_four_of_unique L hLKi eLi huR huL eCi
    (b.unique_component_centralizer_involution hG hzR (b.thompson_le hs2R) hn)
  exact ⟨hD,by simpa only [hD,one_mul] using c.thompson_card,hC⟩

/-- The actual paired-cubic coordinates discharge the centralizer-product,
cardinality, Sylow-index, and conjugator inputs of the source36 terminal route.
The correlated component comes from source32–35; hn and hf are precisely the
independently constructed first paragraph of 36 and the fusion bound of 37. -/
theorem SourceCentralizerGeometry.false_of_component_centralizer_normality
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c) (b : SourceComponentGeometry d)
    (hz : b.z = g.z₂) (hs : b.s = c.s⁻¹) (hz₁ : (b.z₁:G) = g.z₁)
    (hu : (b.u:G) ∈ c.U₂) (hx : (b.x:G) = c.x)
    (hP : (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
      (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype)
    (hG : IsQuasithin G)
    (hodd : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hn : ∀ r : involutionCentralizer b.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer b.z) →
      r ∈ centralizer (b.K : Set (involutionCentralizer b.z)) → orderOf r = 2 →
      centralizer ({(r:G)} : Set G) ≤
        normalizer (b.K.map (involutionCentralizer b.z).subtype : Set G))
    (hf : SourceElementarySixteenFusion b) : False := by
  let H := involutionCentralizer b.z
  obtain ⟨_,hR64,⟨eB⟩⟩ := g.component_centralizer_cyclic_four b hz hs hu hLK hG hn
  have hi : (((sourceR d).subgroupOf H).subgroupOf (b.S₁ : Subgroup H)).index = 2 := by
    change ((sourceR d).subgroupOf H).relIndex (b.S₁ : Subgroup H) = 2
    rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le b.thompson_le,hP]
    exact g.second_index
  have hxP : b.x ∈ (b.S₁ : Subgroup H) := by
    have hxm : (b.x:G) ∈ (b.S₁ : Subgroup H).map H.subtype := by
      rw [hP,g.second_span,hx]
      exact mem_sup_right (mem_zpowers c.x)
    obtain ⟨a,ha,he⟩ := hxm
    exact H.subtype_injective he ▸ ha
  have hsR : b.s ∈ normalizer (sourceR d : Set G) := by
    rw [hs]
    apply (normalizer (sourceR d : Set G)).inv_mem
    exact normalizer_le_normalizer_elementaryAbelianMaxJ _
      (((d.S : Subgroup d.H).map d.H.subtype).le_normalizer c.s_mem)
  have hs2R : b.s^2 ∈ sourceR d := by
    rw [hs,inv_pow]
    exact (sourceR d).inv_mem c.exchange_square_mem
  have hHK : H ≤ normalizer (b.K.map H.subtype : Set G) := by
    have hh := b.K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,H.range_subtype] at hh
  have hz₁R : (b.z₁:G) ∈ centralizer (sourceR d : Set G) := hz₁ ▸ g.first_fixed
  obtain ⟨hC,⟨eFull⟩⟩ := b.full_centralizer_of_cyclic_four hi hR64 (hz.symm ▸ hodd) eB
  obtain ⟨P,hPS⟩ := b.exists_component_sylow hi hxP
  obtain ⟨f⟩ := b.exists_source_factors_of_pair_inputs hC eFull P hPS hR64 hsR
    (hHK (b.thompson_le hs2R)) hz₁R hf
  exact b.false_of_source_factors f

end CFSG.Quasithin.Chapter2.DoubleA3
