module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSevenBlock

/-!
# The preferred canonical A7 block and full moved module

At the unchanged preferred nonsingular point, the original A6 layer V_v
has order 32 and lies in the canonical moved subgroup. Conditional on the
canonical FF witness, the corrected B.5 classifier and the literal A7
quotient therefore give the natural six-dimensional moved module. This
identifies the original K_v as an A7-block, proves |[U,K_v]| = 64, and splits
U as [U,K_v] times its original fixed subgroup.

The FF witness is not constructed here. The remaining HS/J4 exclusions,
group splitting and fixed-space elimination also remain with this source
branch. Earlier invariance/TI retain qt-d-1222-source and final discharge
retains qt-d-12634-source; neither 12.6.2 nor 12.6.23 is asserted.
Source: Aschbacher--Smith, 12.6.18(2), printed p.827, using B.5.1 and I.1.6,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the same preferred point, an FF witness supplies natural coordinates
on the full canonical moved module and the original direct decomposition. -/
theorem SourceHypothesis.exists_preferred_nonsingular_canonical_seven_module_of_fixed
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
          Nonempty (Star (Kv (w : G)) ≃* alternatingGroup (Fin 7)) ∧
          CanonicalSevenMoved E ((Kv (w : G)).subgroupOf J) ∧
          ChapterC.IsAlternatingBlock (Kv (w : G)) 7 ∧
          Nat.card (⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ : Subgroup G) = 64 ∧
          (⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ : Subgroup G) ⊓
            centralizer (Kv (w : G) : Set G) = ⊥ ∧
          U (Kv (w : G)) S₀ = ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ ⊔
            (U (Kv (w : G)) S₀ ⊓ centralizer (Kv (w : G) : Set G))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hCB,S,hTS,hidx,hF,hker,hred,hlocal,hres,hproper,hmodel,hn4,hn5,hseven⟩ :=
    H.exists_preferred_nonsingular_canonical_seven_of_fixed D hTV hTI hz v hv he
  let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
  let J := Kv (w : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (w : G)).subgroupOf J
  have hm : Vv L V (w : G) ≤ ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ := by
    rw [←hlocal]
    exact commutator_mono le_rfl (H.nonsingular_canonical_component D w hw).2.1
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hCB,S,hTS,hidx,hF,hker,hred,hlocal,hres,hproper,hmodel,hn4,hn5,?_⟩
  intro hff
  have hmod := H.nonsingular_canonical_seven_moved D w hw S (hseven hff) hred hm hker hff
  have hshort : ChapterC.IsShort (Kv (w : G)) :=
    hCB.short.of_mulEquiv (subgroupOfEquivOfLe (Kv_le_Gv (w : G)))
  have hblock := nonsingular_canonical_seven_block (w : G) S₀ (map_subtype_le _)
    hshort hker hred hres hmod
  have hp := canonical_seven_moved_properties_map E K hmod J.subtype J.subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (w : G) ≤ J from le_sup_left),←hred] at hp
  exact ⟨hseven hff,hmod,hblock,hp⟩
end CFSG.Quasithin.Chapter12.Section06
