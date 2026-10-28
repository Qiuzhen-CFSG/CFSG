module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration

/-!
# The constructed covered-six Thompson plane and ambient placement

The source Tᵥ-invariance makes K a block relative to KTᵥ, and the original
Sylow witness places W_K in Tᵥ. The literal quotient comparison then gives
an injective K/O₂(K) → G⁺ with image K⁺ and a two-group plus kernel.
The hexacode calculation constructs the four-group whose image is exactly
J(Tᵥ)⁺ = Baum(Tᵥ)⁺. Its full core preimage defines U₂ inside U(K), with
binary dimension four and vector dimension two over the recovered F₄.

Baumann heredity through the entire plus kernel gives the source normalizer
image equality and the 13.6.5 placement K ∩ N_G(U₂) ≤ Mᵥ. The literal
commutator [V,Lᵥ] lies in U(K), has order four, and is invariant under this
plane normalizer. The final theorem applies these constructions to the
actual earlier flag/local configuration, deriving all Sylow, seed, module
and Baumann-control inputs used here.

Only the genuine earlier source conclusions (including 13.6.6, 13.6.14 and
13.6.20) and the explicitly permitted hexacode model remain as inputs.
There is no assumed quotient comparison, Thompson marking, dimension,
normalizer placement, or invariant-E₄ obstruction. The separate covered-six
exclusion and the construction of the model remain with their source owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926–932, especially the covered-A₆ paragraph of 13.6.22 on p.932.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G]

/-- The constructed source plane, with both literal quotient maps and the original
Thompson/Baumann marking. Every field is an output of `nonempty_sourceMarkedPlane`. -/
structure SourceMarkedPlane (K L T M V : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (m : HexacodeModel h)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) where
  comparison : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz
  comparison_injective : Function.Injective comparison
  comparison_mk : ∀ k : K, comparison (QuotientGroup.mk' (pCore 2 K) k) =
    plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k)
  comparison_range : comparison.range = plusImage K L T z v hL hz K
  restricted_kernel : ((plusMk K L T z v hL hz).comp
    (inclusion (K_le_plusActor K L T v))).ker = pCore 2 K
  plus_kernel : IsPGroup 2 (plusMk K L T z v hL hz).ker
  plus_twoCore : pCore 2 (Gplus K L T z v hL hz) = ⊥
  marking : ThompsonImage.FourGroupMarking K L T z v h hL hz comparison
  plane : Subgroup G
  plane_eq : plane = fixedSubgroup K marking.fourGroup
  plane_le : plane ≤ (blockU K).map K.subtype
  plane_fixed : ambientSubspace K plane = fixedSpace (binaryAction h) marking.fourGroup
  binary_dimension : Module.finrank (ZMod 2) (ambientSubspace K plane) = 4
  field_dimension : Module.finrank Hexacode.F (fieldFixedSpace K h m marking.fourGroup) = 2
  plane_card : Nat.card plane = 16
  normalizer_images :
    plusImage K L T z v hL hz (K ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G)) =
      plusImage K L T z v hL hz (K ⊓ normalizer (plane : Set G))
  placement : K ⊓ normalizer (plane : Set G) ≤ Mv M v
  commutator_le : ⁅V, Lv L v⁆ ≤ (blockU K).map K.subtype
  commutator_card : Nat.card (⁅V, Lv L v⁆ : Subgroup G) = 4
  line_dimension : Module.finrank (ZMod 2) (ambientSubspace K ⁅V, Lv L v⁆) = 2
  line_invariant : subspaceStabilizer (binaryAction h) (ambientSubspace K plane) ≤
    subspaceStabilizer (binaryAction h) (ambientSubspace K ⁅V, Lv L v⁆)

omit [Finite G] in
/-- The constructed core comparison agrees with the original star image followed
by the component star-to-plus map, on every original element of K. -/
theorem SourceMarkedPlane.comparison_star
    {K L T M V : Subgroup G} {z v : G}
    {h : IsExceptionalAhat6Block K} [IsElementaryAbelian 2 (blockU K)]
    {m : HexacodeModel h}
    {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
    (d : SourceMarkedPlane K L T M V z v h m hL hz)
    (hK : K ∈ Yz L T z v) (k : K) :
    d.comparison (QuotientGroup.mk' (pCore 2 K) k) =
      (componentStarToPlus K L T z v hK.1.1 hL hz
        (starImageMap z v K hK.1.1 k) : Gplus K L T z v hL hz) :=
  (d.comparison_mk k).trans (componentStarToPlus_mk K L T z v hK.1.1 hL hz k).symm

/-- Assemble the source marking and ambient placement. Only the genuine earlier
source conclusions and the specified hexacode model are inputs. In particular,
the comparison map, both kernels, four-group and plane are constructed here. -/
theorem nonempty_sourceMarkedPlane
    {K L V T M : Subgroup G} (s : A5Module.Marking L V)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (m : HexacodeModel h)
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (hzT : markedZ s ∈ Tv T (markedV s))
    (hU : IsPGroup 2 (Uv (markedZ s) (markedV s)))
    (hLK : Lv L (markedV s) ≤ K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (markedV s)) (Gv (markedV s)))
    (hc : Gv (markedV s) ⊓ normalizer (ChapterB.baumann (Tv T (markedV s)) : Set G) ≤
      Mv M (markedV s))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (markedV s) ≤ normalizer (V : Set G)) :
    Nonempty (SourceMarkedPlane K L T M V (markedZ s) (markedV s) h m hL hz) := by
  have hb := relative_block_of_invariant K T (markedV s) h hn
  have hW := WK_le_Tv_of_source K L T (markedZ s) (markedV s) hK hn hLK hL hz hzT hU
  let f := coreToGplus K L T (markedZ s) (markedV s) h hK hn hLK hL hz hW hb
  have fi : Function.Injective f :=
    coreToGplus_injective K L T (markedZ s) (markedV s) h hK hn hLK hL hz hW hb
  have hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T (markedZ s) (markedV s) hL hz
        (inclusion (K_le_plusActor K L T (markedV s)) k) :=
    coreToGplus_mk K L T (markedZ s) (markedV s) h hK hn hLK hL hz hW hb
  have hk := plus_kernel_isPGroup K L T (markedZ s) (markedV s) h hK hn hLK hL hz hW hb
  have hcore := SourceContainment.LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
    K L T (markedZ s) (markedV s) hK.1.1 hL hz hSylow
  obtain ⟨a⟩ := ThompsonImage.nonempty_source_fourGroupMarking s h m hK hn hL hz hzT hU hLK
    f fi hf hcore
  have hplace := fixedSubgroup_placement_of_marked_image K L T M (markedZ s) (markedV s)
    h hK hn hLK hL hz hk hc a.fourGroup f hf a.baumann a.normalizes
  have hline := source_commutator_le_block s K T h hK hn hzT hU hLK
  have hconsumer := source_line_invariant_of_placement K h s (fixedSubgroup K a.fourGroup)
    (fixedSubgroup_le K a.fourGroup) hline hplace hML hMV
  refine ⟨{
    comparison := f
    comparison_injective := fi
    comparison_mk := hf
    comparison_range := ThompsonImage.Construction.component_range hL hz f hf
    restricted_kernel := ?_
    plus_kernel := hk
    plus_twoCore := hcore
    marking := a
    plane := fixedSubgroup K a.fourGroup
    plane_eq := rfl
    plane_le := fixedSubgroup_le K a.fourGroup
    plane_fixed := ambientSubspace_fixedSubgroup K h a.fourGroup
    binary_dimension := by rw [ambientSubspace_fixedSubgroup K h]; exact a.fixed_finrank
    field_dimension := fieldFixedSpace_finrank_two K h m a.fourGroup a.fixed_finrank
    plane_card := fixedSubgroup_card K h a.fourGroup a.fixed_finrank
    normalizer_images := source_normalizer_images_eq K L T (markedZ s) (markedV s) h hL hz
      (plus_kernel_le_sylow K L T (markedZ s) (markedV s) hK hn hLK hL hz hk)
      a.fourGroup f fi hf a.baumann a.normalizes
    placement := hplace
    commutator_le := hline
    commutator_card := source_commutator_card s
    line_dimension := hconsumer.1
    line_invariant := hconsumer.2 }⟩
  have he : (plusMk K L T (markedZ s) (markedV s) hL hz).comp
      (inclusion (K_le_plusActor K L T (markedV s))) =
        f.comp (QuotientGroup.mk' (pCore 2 K)) := by
    ext k
    exact (hf k).symm
  rw [he, MonoidHom.ker_comp_of_injective _ _ fi, QuotientGroup.ker_mk']

/-- Apply the marking theorem to the genuine flag/local configuration. The
configuration gives the Sylow and 13.6.5 inputs; 13.6.6 gives the two-group
property of Uᵥ. Only component selection, 13.6.14, 13.6.20 and the original
normalization of L remain as earlier source conclusions. -/
theorem sourceMarkedPlane_of_localConfiguration
    {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (m : HexacodeModel h)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV f.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hML : M ≤ normalizer (L : Set G)) :
    ∃ (hL : Tv (T : Subgroup G) (markedV f.module) ≤
        normalizer (Lv L (markedV f.module) : Set G))
      (hz : Tv (T : Subgroup G) (markedV f.module) ≤ centralizer ({markedZ f.module} : Set G)),
      Nonempty (SourceMarkedPlane K L (T : Subgroup G) M V (markedZ f.module)
        (markedV f.module) h m hL hz) := by
  have hzmem := (Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp f.z_central
  have hzT : markedZ f.module ∈ Tv (T : Subgroup G) (markedV f.module) :=
    ⟨hzmem.1, markedZ_mem_Gv f.module⟩
  have hz : Tv (T : Subgroup G) (markedV f.module) ≤ centralizer ({markedZ f.module} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzmem.2.2 t ht.1)
  have hzOmega : markedZ f.module ∈
      Stellmacher.omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV f.module)) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzT, hzmem.2.1, fun t ht => hzmem.2.2 t ht.1⟩
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV f.module))
      (Gv (markedV f.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  let := internalUv_elementary (T : Subgroup G) (markedZ f.module) (markedV f.module)
    hSylow hzOmega hchar
  have hU : IsPGroup 2 (Uv (markedZ f.module) (markedV f.module)) := by
    have he : (internalUv (markedZ f.module) (markedV f.module)).map
        (Gv (markedV f.module)).subtype = Uv (markedZ f.module) (markedV f.module) :=
      map_subgroupOf_eq_of_le (Uv_le_Gv _ _ (markedZ_mem_Gv f.module))
    rw [← he]
    exact (IsElementaryAbelian.isPGroup 2 (internalUv (markedZ f.module) (markedV f.module))).map _
  have hL : Tv (T : Subgroup G) (markedV f.module) ≤
      normalizer (Lv L (markedV f.module) : Set G) := Mv_normalizes_Lv hTL
  have hc : Gv (markedV f.module) ⊓
      normalizer (ChapterB.baumann (Tv (T : Subgroup G) (markedV f.module)) : Set G) ≤
        Mv M (markedV f.module) := by
    rw [← c.reductions.baumann_eq]
    exact c.reductions.normalizer_baumann
  exact ⟨hL, hz, nonempty_sourceMarkedPlane f.module h m hK hn hL hz hzT hU hLK hSylow
    hc hML (c.reductions.local_centralizer.le.trans inf_le_left)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
