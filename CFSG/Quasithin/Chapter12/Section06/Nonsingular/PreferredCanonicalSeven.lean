module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalIndex

/-!
# The preferred canonical component after both binary linear exclusions

At the same source-preferred escaping point with nontrivial original C_V(L),
the proved index bound is at most two. This excludes both SL4(2) and SL5(2)
using the actual A6 quotient section. Thus an FF witness for the literal
canonical action gives K_v/O2(K_v) isomorphic to A7. The original module,
fixed-space quotient, canonical layers and relative K_v-block are retained.

Constructing the general FF witness and the A7 module identification remains
with this source owner, together with HS/J4 exclusions, splitting and
fixed-space elimination. Earlier invariance/TI retain qt-d-1222-source;
final discharge remains with qt-d-12634-source. Neither 12.6.2 nor12.6.23
is asserted. Source: Aschbacher--Smith 12.6.15--18, printed pp.826--827,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the unchanged preferred point, both higher binary linear models are
excluded. Its canonical component is A7 once the actual FF witness is supplied. -/
theorem SourceHypothesis.exists_preferred_nonsingular_canonical_seven_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧ ChapterC.IsAlternatingBlock (Lv L (w : G)) 6 ∧
      ChapterC.IsBlock ((Kv (w : G)).subgroupOf (Gv (w : G))) ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        let J := Kv (w : G) ⊔ S₀
        let E := reducedTwoSubgroup J
        letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
        let A := ((Lv L (w : G)).subgroupOf (Kv (w : G))).map
          (QuotientGroup.mk' (pCore 2 (Kv (w : G))))
        Tv T (w : G) ≤ S₀ ∧ (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
        generalizedFitting J = pCore 2 J ∧ centralizer (E : Set J) = pCore 2 J ∧
        U (Kv (w : G)) S₀ = E.map J.subtype ∧
        ⁅U (Kv (w : G)) S₀,Lv L (w : G)⁆ = Vv L V (w : G) ∧
        ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ =
          (ChapterC.blockU (Kv (w : G))).map (Kv (w : G)).subtype ∧
        A ≠ ⊤ ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
        ¬ Nonempty (Star (Kv (w : G)) ≃* SL(4,ZMod 2)) ∧
        ¬ Nonempty (Star (Kv (w : G)) ≃* SL(5,ZMod 2)) ∧
        (IsFFModule (ChapterB.InternalThompsonAction.action E) →
          Nonempty (Star (Kv (w : G)) ≃* alternatingGroup (Fin 7))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hCB,S,hTS,hidx,hF,hker,hred,hlocal,hres,hproper,hmodel,hclass⟩ :=
    H.exists_preferred_nonsingular_canonical_layers_of_fixed D hTV hTI hz v hv he
  have hn := H.nonsingular_canonical_binary_exclusions_of_index_two D w hw hTV S hidx
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hCB,S,hTS,hidx,hF,hker,hred,hlocal,hres,hproper,hmodel,
    hn.1,hn.2,fun hff => (hclass hff).resolve_right (fun h => h.elim hn.1 hn.2)⟩
end CFSG.Quasithin.Chapter12.Section06
