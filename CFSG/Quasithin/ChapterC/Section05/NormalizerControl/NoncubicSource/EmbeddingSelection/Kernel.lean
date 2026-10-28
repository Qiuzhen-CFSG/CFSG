module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedCore
public import Theory.GroupTheory.CharacteristicTwoCommutatorKernel
/-!
# The exact C.5.13 component kernel in the action quotient

The source core is O₂(N)=P₁, and [P₁,L]=I≤V. The characteristic-two
hypothesis on N therefore forces C_L(V)=O₂(L). This identifies the literal
image of L with its intrinsic two-core quotient and proves injectivity of
the canonical map N/O₂(N)→N/C_N(V) on the L-image. No identification of
the two ambient quotients is assumed.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem source_component_kernel (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let L := conjugateSpanBy K N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let hred := hs.2.2.2.2.2.2.1
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    (q.subgroupMap (L.subgroupOf N)).ker = pCore 2 (L.subgroupOf N) ∧
      Nonempty (((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃*
        DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) ∧
      Function.Injective ((twoCoreToCentralizer (V.subgroupOf N) hred).subgroupMap
        ((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  have hred := hs.2.2.2.2.2.2.1
  have hf := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  let : (L.subgroupOf N).Normal := DualOffender.source_span_normal K N hKN
  obtain ⟨Q,hQ⟩ := hf.2.2
  have hcoreT : (pCore 2 N).map N.subtype ≤ T := hQ ▸ pCoreIn_le_sylow N Q
  have hcoreC : (pCore 2 N).map N.subtype ≤ centralizer (V : Set G) := by
    have hh := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro a ha v hv
    obtain ⟨b,hb,rfl⟩ := ha
    exact congrArg N.subtype (hh hb ⟨v,hs.2.1 hv⟩ hv)
  have hcore : (pCore 2 N).map N.subtype = A.pCoreIn 2 := by
    apply le_antisymm ((le_inf hcoreT hcoreC).trans hs.2.2.2.2.2.1.le)
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
      ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hmoved := DualOffender.noncubic_source_moved_core K T X hK h3 hT hUT hTK
    P hP hA hAX S hS
  have hcomm : ⁅pCore 2 N,L.subgroupOf N⁆ ≤ V.subgroupOf N := by
    apply map_le_map_iff_of_injective N.subtype_injective |>.mp
    rw [map_commutator,hcore,map_subgroupOf_eq_of_le hLN,map_subgroupOf_eq_of_le hs.2.1]
    exact hmoved.2.2.1.symm.le.trans
      (le_normalizer_iff_commutator_le_left.mp (hLN.trans hs.2.2.1))
  have hchar := Chapter1.mem_He_iff.mp hf.2.1
  refine ⟨reduced_component_action_kernel _ _ hred hchar hcomm,?_,
    twoCoreToCentralizer_component_injective _ _ hred hchar hcomm⟩
  have he := reduced_component_action_equiv (V.subgroupOf N) (L.subgroupOf N) hred hchar hcomm
  change Nonempty (((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃*
    DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N))
  rw [DualOffender.closureImage,normalClosure_subgroupOf_eq_conjugateSpanBy K N hKN]
  exact he
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
