module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.FieldModel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ModelObstruction


/-!
# Excluding the covered-A₆ block in the source local configuration

The exceptional-block hypothesis constructs the actual six-dimensional binary
hexacode representation and its three-dimensional F₄ structure on U(K).
The source Thompson/Baumann construction then supplies the four-group A and
its fixed subgroup U₂, whose binary dimension is four: its corresponding
projective F₄-line has vector dimension two.

The concrete plane-normalizer obstruction is transported through the actual
representation isomorphism and the literal ambient relative normalizer.
Thus N_K(U₂) preserves no subgroup of U(K) of order four. The source placement
N_K(U₂) ≤ Mᵥ instead makes it normalize [V,Lᵥ]: Mᵥ normalizes V and normalizes
Lᵥ by characteristicity of the two-residual. The already proved order and
containment of [V,Lᵥ] give the contradiction.

`not_exceptional_of_localConfiguration` constructs the model and marked plane
internally. Its inputs are the genuine flag/local configuration, component
selection, and earlier 13.6.6, 13.6.14 and 13.6.20 conclusions. No representation,
quotient comparison, plane marking, normalizer placement, or invariant-subgroup
obstruction is assumed. Selection of this block alternative by C.1 and assembly
with the other branches of 13.6.22 remain with `AlternatingBranches`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed pp.932–933. The imported concrete action and calculation retain their
ATLAS attribution; see `LICENSES/ATLAS.txt`.
-/

public section

open Subgroup CFSG.Quasithin.ChapterC Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection A5Module
variable {G : Type*} [Group G]

/-- For the original block action, the full ambient relative normalizer of a
four-group fixed plane preserves no subgroup of U(K) of order four.
The representation coordinates are constructed from the block hypothesis. -/
theorem fixedSubgroup_normalizer_no_order_four (K : Subgroup G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (A : Subgroup (K ⧸ pCore 2 K)) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hd : Module.finrank (ZMod 2) (fixedSpace (binaryAction h) A) = 4)
    (Q : Subgroup G) (hQ : Q ≤ (blockU K).map K.subtype) (hc : Nat.card Q = 4) :
    ¬ K ⊓ normalizer (fixedSubgroup K A : Set G) ≤ normalizer (Q : Set G) := by
  obtain ⟨m⟩ := nonempty_hexacodeModel h
  let A' := A.map m.quotientIso.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map m.quotientIso.toMonoidHom
  have hA' : Nat.card A' = 4 := (card_map_of_injective m.quotientIso.injective).trans hA
  apply ambientNormalizer_no_order_four K h m (fixedSubgroup K A) Q
    (fixedSubgroup_le K A) (fixedSubgroup_card K h A hd) hQ hc A' hA'
  rw [ambientSubspace_fixedSubgroup K h]
  exact fixedSpace_map_equivariant (binaryAction h) Hexacode.evenAction
    m.quotientIso.toMonoidHom m.coordinates m.intertwining A

/-- Apply the proved obstruction to the literal source commutator. The two
normalizations come from the constructed placement in Mᵥ. -/
private theorem sourceMarkedPlane_contradiction [Finite G]
    {K L T M V : Subgroup G} {z v : G}
    {h : IsExceptionalAhat6Block K} [IsElementaryAbelian 2 (blockU K)]
    {m : HexacodeModel h}
    {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
    (d : SourceMarkedPlane K L T M V z v h m hL hz)
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M v ≤ normalizer (V : Set G)) : False := by
  let := d.marking.elementary
  apply fixedSubgroup_normalizer_no_order_four K h d.marking.fourGroup
    d.marking.card d.marking.fixed_finrank ⁅V, Lv L v⁆ d.commutator_le d.commutator_card
  rw [← d.plane_eq]
  exact source_commutator_normalized _ d.placement hML hMV

/-- The covered-A₆ case is impossible under the earlier local source conclusions.
The core comparison, original Thompson marking and ambient placement are all
constructed, then the normalizer obstruction is applied to [V,Lᵥ]. -/
theorem not_exceptional_of_source [Finite G]
    {K L V T M : Subgroup G} (s : A5Module.Marking L V)
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
    ¬ IsExceptionalAhat6Block K := by
  intro h
  let := h.1.elementary
  obtain ⟨m⟩ := nonempty_hexacodeModel h
  obtain ⟨d⟩ := nonempty_sourceMarkedPlane s h m hK hn hL hz hzT hU hLK hSylow hc hML hMV
  exact sourceMarkedPlane_contradiction d hML hMV

/-- The covered-A₆ exclusion on the genuine A₅ flag/local configuration.
Here 13.6.6 supplies `hchar`, 13.6.14 supplies `hn`, and 13.6.20 supplies `hLK`.
The configuration supplies the remaining Sylow and 13.6.5 normalizer inputs. -/
theorem not_exceptional_of_localConfiguration [Finite G]
    {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV f.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hML : M ≤ normalizer (L : Set G)) :
    ¬ IsExceptionalAhat6Block K := by
  intro h
  let := h.1.elementary
  obtain ⟨m⟩ := nonempty_hexacodeModel h
  obtain ⟨hL, hz, d⟩ := sourceMarkedPlane_of_localConfiguration f c h m hK hn hLK hchar hTL hML
  exact sourceMarkedPlane_contradiction d.some hML
    (c.reductions.local_centralizer.le.trans inf_le_left)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
