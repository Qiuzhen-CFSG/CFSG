module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SevenCore
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredCanonicalFF

/-!
# The preferred A7 core split on the original subgroups

The constructed FF witness and full A7 module identify the same preferred
point's Sylow subgroup as T_v and its core as R_v. The original natural
six-space W=[U,K_v], of order64, is an internal direct factor of R_v;
the complementary factor is exactly C_(T_v)(K_v). The quotient/action
marking, original V_v commutator and LT=LR_v are retained. Uniqueness also
annihilates the common centralizer of L and K_v inside T.

This discharges the A7 two-core splitting and common-centralizer steps
in the nontrivial C_V(L) branch. The A8 extension of the original Q,
remaining HS/J4 exclusions, general12.6.13(3), and fixed-space elimination
are still required. Earlier invariance/TI retain qt-d-1222-source and
final discharge retains qt-d-12634-source. Neither12.6.2 nor12.6.23 is
asserted. Source: Aschbacher--Smith, printed p.828, combined manuscript
of1 March2004, proof of12.6.2 following12.6.18.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At the unchanged preferred point, the actual Sylow is T_v and R_v
splits over the full natural A7 moved module and its literal centralizer.
All core, Sylow and splitting premises are discharged. -/
theorem SourceHypothesis.exists_preferred_nonsingular_seven_core_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Gv (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧
      ChapterC.IsAlternatingBlock (Lv L (w : G)) 6 ∧
      ChapterC.IsAlternatingBlock (Kv (w : G)) 7 ∧
      L ⊔ Rv T L (w : G) = LT T L ∧
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (Kv (w : G) : Set G) = ⊥ ∧
      (Rv T L (w : G)).relIndex (Tv T (w : G)) = 16 ∧
      let J := Kv (w : G) ⊔ Tv T (w : G)
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      let W := (⁅U (Kv (w : G)) (Tv T (w : G)),Kv (w : G)⁆ : Subgroup G)
      let C := Tv T (w : G) ⊓ centralizer (Kv (w : G) : Set G)
      R L (Kv (w : G)) (Tv T (w : G)) (w : G) = Rv T L (w : G) ∧
      Rv T L (w : G) = J.pCoreIn 2 ∧
      U (Kv (w : G)) (Tv T (w : G)) = E.map J.subtype ∧
      ⁅U (Kv (w : G)) (Tv T (w : G)),Lv L (w : G)⁆ = Vv L V (w : G) ∧
      CanonicalSevenMoved E ((Kv (w : G)).subgroupOf J) ∧
      Nat.card W = 64 ∧ Rv T L (w : G) = W ⊔ C ∧ Disjoint W C ∧ ⁅W,C⁆ = ⊥ := by
  obtain ⟨w,hw,hew,hs,hi,hlt,hnot,hctrl,hL,hA,hCB,S,hTS,hidx,hFit,hker,
    hred,hUT,hlocal,hres,hff,⟨eseven⟩,hmod,hblock,hcard,hfixed,hsplitU⟩ :=
    H.exists_preferred_nonsingular_canonical_ff_of_fixed D hTV hTI hz v hv he
  have hcoreT := H.nonsingular_core_le_Tv_of_moved_control D w hw hs hctrl S hTS hred hlocal
  have hcore := H.nonsingular_seven_original_core D w hw hs S hTS eseven hcoreT
  have hnq : ¬ IsQuasisimple (Kv (w : G)) := fun h =>
    hz (H.nonsingular_quasisimple_fixed_eq_bot D w hw h hTV hi hnot)
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D w hw hTV hnq hs hi hnot
  have hQR : Q T L < Rv T L (w : G) := lt_of_le_of_ne (Q_le_Rv H.chosen w)
    (fun heq => hn (heq ▸ H.core_normalizer_le))
  have hS := H.nonsingular_seven_sylow_eq_Tv D w hw hs hi hQR S hTS eseven hcore
  have hR := H.nonsingular_seven_R_eq_core D w hw S eseven
  have hsplit := nonsingular_seven_core_split (w : G) _ (map_subtype_le _) hblock hres hfixed
  have hcent := H.nonsingular_seven_core_centralizer D w hw S eseven
  dsimp only at hR hcent
  rw [hS] at hcore hR hred hlocal hmod hcard hsplit hcent
  rw [←hcore] at hR hsplit hcent
  rw [hcent] at hsplit
  exact ⟨w,hw,hew,⟨S,hS⟩,hi,hlt,hnot,hL,hA,hblock,
    H.nonsingular_original_join D w hw hQR,
    H.nonsingular_common_centralizer_eq_bot_of_join hTV w hnot
      (H.nonsingular_original_join D w hw hQR),
    H.nonsingular_original_Tv_core_index D w hw hs hi hQR,
    hR,hcore,hred,hlocal,hmod,hcard,hsplit⟩


end CFSG.Quasithin.Chapter12.Section06
