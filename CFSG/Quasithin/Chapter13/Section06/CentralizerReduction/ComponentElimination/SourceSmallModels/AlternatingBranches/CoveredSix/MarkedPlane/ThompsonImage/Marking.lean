module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.ImageGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction

/-!
# The source covered-six Thompson four-group

The genuine A₅ marking and earlier local conclusions construct the full plus
action. Its nontrivial maximum-elementary images all coincide by the concrete
hexacode calculation. Their generated subgroup is the original J(Tᵥ)⁺,
which pulls back through the prescribed core-to-plus injection to a four-group.
Its binary fixed dimension is four, its pointwise kernel is itself, and its
image is also the original Baumann image.

The final application supplies both existing marked-plane consumers: the
literal normalizer-image equality and the invariance of the original line
[V,Lᵥ]. The ambient fixed subgroup has order sixteen and its field coordinates
have vector dimension two. No invariant-E₄ obstruction is used.

The explicit earlier premises are the central seed and A₅ marking (p.926),
the two-group consequence of Uᵥ∈R₂ (p.928), Y_z and O₂(G⁺)=1 (p.929),
Tᵥ-invariance (13.6.14), Lᵥ≤K (13.6.20), and the normalizer bound (13.6.5).
The representation model and compatible quotient injection are the independent
model/comparison inputs. Their ambient discharge remains with the source
assembly; no marking, dimension or normalizer conclusion is an input here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the covered-A₆
paragraph of 13.6.22, printed p.932, with B.4.2(8) and K.1.3.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L V T : Subgroup G}

/-- Construct the four-group on K/O₂(K), with the literal Thompson and Baumann images,
from the marked source data and the prescribed core comparison. -/
theorem nonempty_source_fourGroupMarking
    (s : A5Module.Marking L V) (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)] (m : HexacodeModel h)
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (hzT : markedZ s ∈ Tv T (markedV s))
    (hU : IsPGroup 2 (Uv (markedZ s) (markedV s)))
    (hLK : Lv L (markedV s) ≤ K)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T (markedZ s) (markedV s) hL hz)
    (fi : Function.Injective f)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T (markedZ s) (markedV s) hL hz
        (inclusion (K_le_plusActor K L T (markedV s)) k))
    (hcore : pCore 2 (Gplus K L T (markedZ s) (markedV s) hL hz) = ⊥) :
    Nonempty (FourGroupMarking K L T (markedZ s) (markedV s) h hL hz f) := by
  obtain ⟨d, _⟩ := Construction.exists_source_plusBlockModel s h m hK hn hL hz hzT hU hLK f hf hcore
  exact d.nonempty_fourGroupMarking hK hn hLK fi

/-- The constructed marking discharges both consumers, on the same source commutator.
The field line is projective, with vector dimension two over F₄. -/
theorem exists_source_plane_and_line
    (s : A5Module.Marking L V) (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)] (m : HexacodeModel h)
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (hzT : markedZ s ∈ Tv T (markedV s))
    (hU : IsPGroup 2 (Uv (markedZ s) (markedV s)))
    (hLK : Lv L (markedV s) ≤ K)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T (markedZ s) (markedV s) hL hz)
    (fi : Function.Injective f)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T (markedZ s) (markedV s) hL hz
        (inclusion (K_le_plusActor K L T (markedV s)) k))
    (hcore : pCore 2 (Gplus K L T (markedZ s) (markedV s) hL hz) = ⊥)
    (hk : IsPGroup 2 (plusMk K L T (markedZ s) (markedV s) hL hz).ker)
    (M : Subgroup G)
    (hc : Gv (markedV s) ⊓ normalizer (ChapterB.baumann (Tv T (markedV s)) : Set G) ≤
      Mv M (markedV s))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (markedV s) ≤ normalizer (V : Set G)) :
    ∃ a : FourGroupMarking K L T (markedZ s) (markedV s) h hL hz f,
      Nat.card (fixedSubgroup K a.fourGroup) = 16 ∧
      Module.finrank Hexacode.F (fieldFixedSpace K h m a.fourGroup) = 2 ∧
      plusImage K L T (markedZ s) (markedV s) hL hz
        (K ⊓ normalizer (ChapterB.baumann (Tv T (markedV s)) : Set G)) =
        plusImage K L T (markedZ s) (markedV s) hL hz
          (K ⊓ normalizer (fixedSubgroup K a.fourGroup : Set G)) ∧
      Module.finrank (ZMod 2) (ambientSubspace K ⁅V, Lv L (markedV s)⁆) = 2 ∧
      subspaceStabilizer (binaryAction h) (fixedSpace (binaryAction h) a.fourGroup) ≤
        subspaceStabilizer (binaryAction h) (ambientSubspace K ⁅V, Lv L (markedV s)⁆) := by
  obtain ⟨a⟩ := nonempty_source_fourGroupMarking s h m hK hn hL hz hzT hU hLK f fi hf hcore
  refine ⟨a, fixedSubgroup_card K h a.fourGroup a.fixed_finrank,
    fieldFixedSpace_finrank_two K h m a.fourGroup a.fixed_finrank, ?_, ?_⟩
  · exact CoveredSix.source_normalizer_images_eq K L T (markedZ s) (markedV s) h hL hz
      (plus_kernel_le_sylow K L T (markedZ s) (markedV s) hK hn hLK hL hz hk)
      a.fourGroup f fi hf a.baumann a.normalizes
  · exact source_line_for_marked_image s K T h hK hn hzT hU hLK hL hz hk hc
      a.fourGroup f hf a.baumann a.normalizes hML hMV

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
