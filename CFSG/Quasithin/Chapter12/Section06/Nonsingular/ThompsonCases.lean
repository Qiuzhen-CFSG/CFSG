module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalThompson
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SmallThompson

/-!
# Thompson generation at the preferred escaping centralizer

Combine the excluded small Thompson branch with local generation from
12.6.9. At the actual preferred point, L_v=K_v forces both
L_v=[L_v,J(T_v)] and L=[L,J(T)]. Neither identity is an extra premise.
The remaining B.5 module argument must prove [R₂(G_v),L_v]=V_v and
contradict the already established nonnormality of V_v. This module does
not assert 12.6.11, 12.6.2 or fixed-space elimination.

The T-invariance and TI premises are earlier source conclusions with
producer qt-d-1222-source and final discharge owner qt-d-12634-source.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
last paragraph of Lemma 12.6.11, printed p.825.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the original preferred escaping point, the equal-residual branch has
both local and global Thompson generation, with no generation premise. -/
theorem SourceHypothesis.exists_preferred_thompson_generation
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L ∧
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L ∧
        Lv L (w : G) = ⁅Lv L (w : G),elementaryAbelianMaxJ (Tv T (w : G))⁆ ∧
        L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) := by
  obtain ⟨w,hw,he,hs,hi,hsmall⟩ :=
    H.exists_preferred_small_thompson_residual_strict D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,?_⟩
  intro heq
  have hJ : ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L :=
    fun h => (hsmall h).ne heq
  exact ⟨hJ,H.nonsingular_thompson_generation D w hw hTV hs hJ⟩
end CFSG.Quasithin.Chapter12.Section06
