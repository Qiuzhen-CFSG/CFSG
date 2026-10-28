module
public import Theory.Representation.PSL3Two.NaturalDualGeneration
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Alignment
public import Theory.GroupTheory.CComponent.NormalPair

/-!
# Excluding equality in terminal component alignment

If the opposite component equals either conjugate component, the source
central point lies in its intrinsic two-core. That core is invariant under
the common component stabilizer. Its nonzero intersection with the first
natural--dual support therefore contains the whole support, by the inner
and diagram actions. The second support already lies in the same core.

Both supports consequently lie in the opposite ambient two-core. F.9.2
bounds each critical actor's displacement into the original conjugate
point line, and the fixed supplement contributes no displacement. A
nontrivial involution then violates the proved no-FF bound on the paired
module. This proves properness without an orbit-generation callback.

The component markings, the diagram actor and Z in both supports are
explicit 14.6.20--23 inputs. Their construction and the remaining Sylow
contradiction belong to qt-e-suitable-component-marking; final suitable
choice assembly belongs to qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.24(3), printed p.1040.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

private theorem relative_core_le (H L : Subgroup G) (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) : L.pCoreIn 2 ≤ H.pCoreIn 2 := by
  have hp := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hL.subnormal)
  rw [pCoreIn_subgroupOf 2 L H hLH,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 L).trans hLH)] at hp
  exact hp

private theorem component_support_le_core
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (L : Subgroup G) (hLH : L ≤ D.H) (hL : (L.subgroupOf D.H).IsCComponent) :
    ⁅D.UH,L⁆ ≤ L.pCoreIn 2 := by
  have hUL : D.UH ≤ normalizer (L : Set G) := by
    intro u hu
    obtain ⟨x,hx,rfl⟩ := h.UH_le_QH hu
    have hh := hL.pCore_le_normalizer 2 hx
    rwa [←subgroupOf_normalizer_eq hLH] at hh
  have hLU : L ≤ normalizer (D.UH : Set G) :=
    hLH.trans (le_normalizer_conjugateSpanBy _ _)
  exact le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 D.UH).to_le
      (le_normalizer_iff_commutator_le_left.mp hLU))
    (le_normalizer_iff_commutator_le_right.mp hUL)
    (normalizer_commutator_ge_right D.UH L)

/-- Equality with either conjugate component is impossible. The first
support is generated inside the opposite core by the inner and diagram
actions; both supports would then have only line-valued displacement. -/
theorem placedEndpoint_component_ne
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (K Kplus : Subgroup G) (p : PlacedEndpoint h K Kplus)
    (hb : 3 ≤ h.b) [IsElementaryAbelian 2 D.UH]
    (hKM : K ≤ D.H) (hKplusM : Kplus ≤ D.H)
    (hcomp : (K.subgroupOf D.H).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf D.H).IsCComponent)
    (hZ₁ : D.V₁ ≤ ⁅D.UH,K⁆) (hZ₂ : D.V₁ ≤ ⁅D.UH,Kplus⁆)
    (hpoint : ¬ p.endpoint.conjugate D.V₁ ≤ D.V₁)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hAN : Source.starImage D.H (p.endpoint.conjugate D.UH) ≤ N)
    (hNplus : ∀ a : D.H, QuotientGroup.mk' (pCore 2 D.H) a ∈ N →
      (a : G) ∈ normalizer (Kplus : Set G))
    (hS₁ : c.imageSpace ⁅D.UH,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅D.UH,Kplus⁆ = m.rightEmbedding.range)
    (κ : BinaryLinearThree.Group →* N) (hκ : ∀ k, m.left (κ k) = MulAut.conj k)
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group) :
    Kplus ≠ p.endpoint.conjugate K ∧ Kplus ≠ p.endpoint.conjugate Kplus := by
  let i := p.endpoint
  let s := criticalSection h c
  let R := Kplus.pCoreIn 2
  let Ug := i.conjugate D.UH
  let Zg := i.conjugate D.V₁
  let A := Source.starImage D.H Ug
  have hsup₂ := component_support_le_core h Kplus hKplusM hcompPlus
  have hRU : ∀ n : N, ∀ v ∈ s.image R, ρ n v ∈ s.image R := by
    intro n v hv
    obtain ⟨b,hb'⟩ := QuotientGroup.mk'_surjective (pCore 2 D.H) (n : Source.Hstar D.H)
    have hn : (b : G) ∈ normalizer (R : Set G) :=
      normalizer_le_normalizer_characteristic_image Kplus (pCore 2 Kplus)
        (hNplus b (hb' ▸ n.property))
    obtain ⟨u,hu,rfl⟩ := (s.mem_image R v).mp hv
    rw [←hb',s.conjugates]
    exact ⟨_,(mem_normalizer_iff.mp hn u).mp hu,rfl⟩
  have hUgH : Ug ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (i.large_le hb)
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := starImage_isElementaryAbelian D.H Ug hUgH
  let B := A.subgroupOf N
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  have hBN : B ≠ ⊥ := by
    intro he
    have hp := p.positive.trans_le p.comparison
    have hm := map_subgroupOf_eq_of_le hAN
    change B.map N.subtype = A at hm
    rw [he,Subgroup.map_bot] at hm
    change 0 < rank A at hp
    rw [←hm,Representation.BinaryOffender.rank_bot] at hp
    omega
  obtain ⟨b',hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBN
  let b : N := b'
  have hbB : b ∈ B := b'.property
  have hb1 : b ≠ 1 := fun he => hb' (Subtype.ext he)
  have hb2 : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hbB) hb1
  let τ := ρ.comp N.subtype
  have hlo : 2 ≤ fixedCodim τ (zpowers b) := by
    obtain ⟨he,hr,_,_⟩ := involution_actor_rank_and_fixedCodim τ b hb2
    have hh : rank (zpowers b) < fixedCodim τ (zpowers b) :=
      Nat.lt_of_not_ge (fun hle => m.not_ff
        ((f9_section_faithful _ h s).comp N.subtype_injective) ⟨_,he,hle⟩)
    omega
  have step (L : Subgroup G) (hLH : L ≤ D.H)
      (hL : (L.subgroupOf D.H).IsCComponent) (hZ : D.V₁ ≤ ⁅D.UH,L⁆)
      (he : Kplus = i.conjugate L) : False := by
    have hRQ : R ≤ i.conjugate D.QH := by
      change Kplus.pCoreIn 2 ≤ _
      rw [he,AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj i.representative).injective]
      exact map_mono (relative_core_le D.H L hLH hL)
    have hZgR : Zg ≤ R := by
      change i.conjugate D.V₁ ≤ Kplus.pCoreIn 2
      rw [he,AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj i.representative).injective]
      exact map_mono (hZ.trans (component_support_le_core h L hLH hL))
    have hleft : m.leftEmbedding.range ≤ s.image R := by
      apply m.left_range_le_of_invariant_intersection _ hRU _ κ hκ a ha
      obtain ⟨z,hz,hznot⟩ := SetLike.not_le_iff_exists.mp hpoint
      have hzU : z ∈ D.UH :=
        le_normalizer_iff_commutator_le_left.mp (hKM.trans c.normalized)
          (p.point_support hz)
      let v := (s.quotient ⟨z,hzU⟩).toAdd
      have hv0 : v ≠ 0 := fun hv => hznot ((s.quotient_eq_zero_iff _).mp hv)
      have hvR : v ∈ s.image R := ⟨⟨z,hzU⟩,hZgR hz,rfl⟩
      have hvL : v ∈ m.leftEmbedding.range := by
        rw [←hS₁]
        exact ⟨⟨z,hzU⟩,p.point_support hz,rfl⟩
      obtain ⟨w,hw⟩ := hvL
      apply (Submodule.ne_bot_iff _).mpr
      exact ⟨w,show m.leftEmbedding w ∈ s.image R from hw ▸ hvR,
        fun hz => hv0 (by rw [←hw,hz,map_zero])⟩
    have hright : m.rightEmbedding.range ≤ s.image R := by
      rw [←hS₂]
      exact s.image_mono hsup₂
    have hcomm : ⁅Ug,i.conjugate D.QH⁆ ≤ Zg := by
      have hh := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
        h.commutator_UH_QH_le_point
      rwa [map_commutator] at hh
    have hdisp : ∀ v ∈ s.image R, τ b v - v ∈ s.image Zg := by
      intro v hv
      exact s.displacement_mem _ _ _ hcomm b hbB v ((s.image_mono hRQ) hv)
    have hall : ∀ v, τ b v - v ∈ s.image Zg := by
      intro v
      have hv : v ∈ m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace τ ⊤ := by
        rw [m.span]; trivial
      obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hw
      have hf : τ b z = z := hz ⟨b,mem_top b⟩
      have hh := (s.image Zg).add_mem (hdisp x (hleft hx)) (hdisp y (hright hy))
      simpa only [map_add,hf,add_sub_add_right_eq_sub,add_sub_add_comm] using hh
    have hzdim : Module.finrank (ZMod 2) (s.image Zg) ≤ 1 := by
      have hh := s.image_finrank_le Zg
      have hzcard : Nat.card Zg = 2 :=
        (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
      simpa only [hzcard,show Nat.log 2 2 = 1 from by decide] using hh
    have hhi := (fixedCodim_zpowers_le_of_displacement_mem τ b (s.image Zg) hall).trans hzdim
    omega
  exact ⟨step K hKM hcomp hZ₁,step Kplus hKplusM hcompPlus hZ₂⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
