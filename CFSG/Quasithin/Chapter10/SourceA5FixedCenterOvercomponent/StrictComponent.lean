module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SourceResidual
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.NormalizerFixedLine
public import CFSG.Quasithin.Chapter10.SourceA5LayerElementComponent

/-!
# The original positive-center A5 component is strictly contained

The cubic residual of the marked point stabilizer moves the first layer
vector. If the containing component equals the original A5 block, its
normalizer fixes that same vector by the Sylow fixed-line argument. This
contradiction upgrades the original element-centralizer component to a
strict overcomponent, retaining its ambient centralizer and normality.

Source: Aschbacher–Smith 10.2.1, printed p.743. The preceding orthogonal
coordinate and original layer-vector markings remain explicit inputs.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The prescribed point stabilizer residual forces the original A5 block
to lie strictly in its actual element-centralizer component. -/
theorem source_a5_fixed_center_strict_containing_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {H : Subgroup G} (hH : H∈Chapter3.HStar (T:Subgroup G) D.maximalLocal)
    (hHN : H≤normalizer (ChapterB.baumann (T:Subgroup G):Set G))
    (hred : IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T:Subgroup G)) H).subgroupOf H))
    (f : H →* BinaryFourPlus.Wreath) (hf : Function.Surjective f)
    (v₁ v₂ t : G) (a b : BinaryFourPlus.Plane) (ha : a≠0) (hb : b≠0)
    (hfix₁ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (a,0)=(a,0) ↔
      (h:G)∈centralizer ({v₁}:Set G))
    (hfix₂ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (0,b)=(0,b) ↔
      (h:G)∈centralizer ({v₂}:Set G))
    (hv₁W : v₁∈conjugateSpanBy (omegaOneCenterAmbient (T:Subgroup G)) H)
    (hv₁L : v₁∈(blockU L).map L.subtype)
    (hv₁T : v₁∈centralizer ((T:Subgroup G)⊓L:Set G))
    (ht : t∈(T:Subgroup G))
    (hv₂ : v₂∈(blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hv₂T : v₂∈(T:Subgroup G)) (hv₂ne : v₂≠1)
    (hv₂L : v₂∈centralizer (L:Set G))
    (hCT : (T:Subgroup G)⊓centralizer ({v₂}:Set G)=
      (T:Subgroup G)⊓normalizer (L:Set G)) :
    ∃ I : Subgroup G, L<I ∧ I≤centralizer ({v₂}:Set G) ∧
      (I.subgroupOf (centralizer ({v₂}:Set G))).IsCComponent ∧
      centralizer ({v₂}:Set G)≤normalizer (I:Set G) := by
  obtain ⟨_,hYX,hTY,hYM,_,hmove⟩ := source_fixed_center_pointResidual_data
    D e hn hout hH hHN f hf v₁ v₂ a b ha hb hfix₁ hfix₂
  rw [hCT] at hTY
  have hWH : conjugateSpanBy (omegaOneCenterAmbient (T:Subgroup G)) H≤H :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hH.1.1.2)
  have hcore := reduced_module_core_centralizes_vector H _ hWH hred hv₁W
  have hnot := source_a5_element_centralizer_not_normalizes_of_moved_vector
    D e hn hout H (pointResidual H v₂) v₁ v₂ hYX hTY hv₁L hv₁T hYM hcore hmove
  obtain ⟨_,I,hLI,hIX,hI,hNI⟩ := source_a5_conjugate_layer_element_component
    D e hn hout ht hv₂ hv₂T hv₂ne hv₂L hCT
  refine ⟨I,lt_of_le_of_ne hLI ?_,hIX,hI,hNI⟩
  intro he
  apply hnot
  rwa [he]

end CFSG.Quasithin.Chapter10
