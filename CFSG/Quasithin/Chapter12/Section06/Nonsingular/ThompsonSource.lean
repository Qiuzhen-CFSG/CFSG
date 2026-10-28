module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Thompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

/-!
# Original-source Thompson normalizers and the escaping centralizer

The chosen nontrivial V lies in Q, so J(Q) is nontrivial. Characteristicity
of Q in LT and of its elementary Thompson subgroup proves actual LT
normalization. The earlier Section12.2 uniqueness theorem therefore puts
the full ambient N_G(J(Q)) in M, discharging the premise of the local
Thompson argument. All clauses of 12.6.8 follow for the original S and R.

The preferred escaping point inherits these conclusions. In its small
Thompson and equal-residual branch, the actual G_v-conjugate span of V_v
is a strictly larger normal elementary subgroup in Ω₁(Z(O₂(G_v))) and
is moved by J(T_v). The remaining B.5.6 module argument must exclude this
configuration. Neither 12.6.11 nor 12.6.2 nor fixed-space elimination is
asserted here. T-invariance and TI retain their earlier-source producer
qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemmas 12.6.7--8 and 12.6.11, printed pp.824--825.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original normalizer of J(Q) is controlled by the proved earlier
uniqueness theorem. No local Thompson-normalizer premise is assumed. -/
theorem SourceHypothesis.core_thompson_normalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V) :
    normalizer (elementaryAbelianMaxJ (Q T L) : Set G) ≤ M L := by
  have hQne : Q T L ≠ ⊥ := fun he =>
    H.chosen.ne_bot (bot_unique (H.chosen.le_core.trans_eq he))
  have hJQ : elementaryAbelianMaxJ (Q T L) ≤ Q T L := sSup_le fun _ hA => hA.1
  have hnQ : LT T L ≤ normalizer (Q T L : Set G) :=
    (LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (LT T L) (pCore 2 (LT T L)))
  exact H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
    (hJQ.trans (pCoreIn_le 2 _))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup _ (isPGroup_pCoreIn 2 _) hQne)
    (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))

/-- Source 12.6.8 with S an actual Sylow subgroup of G_v. The source
Sylow position is the one constructed in PreferredPoint. -/
theorem SourceHypothesis.nonsingular_small_thompson
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (S : Sylow 2 (Gv (v : G)))
    (hTvS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    S₀ = Tv T (v : G) ∧
      R L (Kv (v : G)) S₀ (v : G) = Rv T L (v : G) ∧
      elementaryAbelianMaxJ (Tv T (v : G)) = elementaryAbelianMaxJ (Rv T L (v : G)) ∧
      elementaryAbelianMaxJ (Rv T L (v : G)) = elementaryAbelianMaxJ (Q T L) ∧
      normalizer (elementaryAbelianMaxJ S₀ : Set G) ≤ M L := by
  exact H.nonsingular_small_thompson_of_normalizer H.core_thompson_normalizer
    D v hv hTv hJ S hTvS

variable [IsElementaryAbelian 2 V]

/-- The small Thompson branch cannot centralize a G_v-invariant overmodule
of the literal V_v once its point centralizer is controlled. This is the
Frattini contradiction in 12.6.11, with its module-theoretic input explicit. -/
theorem SourceHypothesis.small_thompson_moves_normal_overmodule
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (hescape : ¬ Gv (v : G) ≤ M L)
    (hC : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L)
    (U : Subgroup G) (hWU : Vv L V (v : G) ≤ U)
    (hn : Gv (v : G) ≤ normalizer (U : Set G)) :
    ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ centralizer (U : Set G) := by
  exact H.small_thompson_moves_normal_overmodule_of_normalizer H.core_thompson_normalizer
    D v hv hTv hJ hescape hC U hWU hn

/-- The preferred escaping source point carries the Thompson reductions
on the original groups. Under L_w=K_w the earlier reductions supply the
centralizer bound used in the small-case Frattini contradiction. -/
theorem SourceHypothesis.exists_preferred_nonsingular_thompson_reductions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        Gv (w : G) ∈ Chapter1.He G ∧
        ¬ ((Vv L V (w : G)).subgroupOf (Gv (w : G))).Normal) ∧
      (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        ∀ (S : Sylow 2 (Gv (w : G))),
          Tv T (w : G) ≤ (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype →
          (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype = Tv T (w : G) ∧
          R L (Kv (w : G)) (Tv T (w : G)) (w : G) = Rv T L (w : G)) ∧
      (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        Lv L (w : G) = Kv (w : G) →
        ∀ U : Subgroup G, Vv L V (w : G) ≤ U →
          Gv (w : G) ≤ normalizer (U : Set G) →
          ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ centralizer (U : Set G)) ∧
      (¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) := by
  obtain ⟨w,hw,he,hs,hi,hred⟩ :=
    H.exists_preferred_nonsingular_Kv_reductions D hTV hTI v hv hescape
  refine ⟨w,hw,he,hs,hi,fun h => ⟨(hred h).2.1,(hred h).2.2.2⟩,?_,?_,?_⟩
  · intro hJ S hTS
    obtain ⟨hS,hR,_,_,_⟩ := H.nonsingular_small_thompson D w hw hs hJ S hTS
    exact ⟨hS,by simpa only [hS] using hR⟩
  · intro hJ h U hWU hn
    have hc : Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L :=
      (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hred h).2.2.1
    exact H.small_thompson_moves_normal_overmodule D w hw hs hJ he hc U hWU hn
  · exact H.global_thompson_generation_of_local_not_le_core w

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A concrete normal elementary module for the remaining small Thompson
case of 12.6.11. Its strict growth and Thompson movement are proved, while
its exclusion by the earlier module classification remains to be assembled. -/
theorem SourceHypothesis.exists_preferred_nonsingular_small_thompson_module
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        Lv L (w : G) = Kv (w : G) →
        let W := Vv L V (w : G)
        let U := componentOrbit W (Gv (w : G))
        W < U ∧
        U ≤ omegaOneAmbient ((center ((Gv (w : G)).pCoreIn 2)).map
          ((Gv (w : G)).pCoreIn 2).subtype) ∧
        IsElementaryAbelian 2 U ∧ (U.subgroupOf (Gv (w : G))).Normal ∧
        ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ centralizer (U : Set G)) := by
  obtain ⟨w,hw,he,hs,hi,_,_,hmoves,_⟩ :=
    H.exists_preferred_nonsingular_thompson_reductions D hTV hTI v hv hescape
  refine ⟨w,hw,he,hs,hi,?_⟩
  intro hJ heq
  let W := Vv L V (w : G)
  let A := Gv (w : G)
  let U := componentOrbit W A
  have hWA : W ≤ A := (Vv_le_V H.chosen.normalizes _).trans (V_le_Gv w)
  have hWU : W ≤ U := le_componentOrbit W A
  have hUA : U ≤ A := iSup_conjugates_le_of_le_normalizer W A A hWA A.le_normalizer
  have hn : A ≤ normalizer (U : Set G) := le_normalizer_componentOrbit W A
  have hm : ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ centralizer (U : Set G) :=
    hmoves hJ heq U hWU hn
  have hlt : W < U := by
    apply lt_of_le_not_ge hWU
    intro hUW
    exact hm (hJ.trans (H.chosen.core_centralizes.trans
      (Subgroup.centralizer_le (hUW.trans (Vv_le_V H.chosen.normalizes _)))))
  exact ⟨hlt,
    H.small_thompson_closure_le_omega_of_normalizer H.core_thompson_normalizer D w hw hTV hs hJ heq,
    H.small_thompson_closure_elementary_of_normalizer H.core_thompson_normalizer D w hw hTV hs hJ heq,
    (normal_subgroupOf_iff_le_normalizer hUA).mpr hn,hm⟩

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual Q has its full normalizer in M, via its characteristic
nontrivial elementary Thompson subgroup. -/
theorem SourceHypothesis.core_normalizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V) :
    normalizer (Q T L : Set G) ≤ M L :=
  (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans H.core_thompson_normalizer

/-- Apply the original terminal contradiction with the Q-normalizer premise
now supplied by the original source hypotheses. Block, splitting and index
inputs remain obligations of the nonsingular-centralizer assembly. -/
theorem SourceHypothesis.nonsingular_terminal_contradiction
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (S : Subgroup G)
    (v : V) (hv : D.Nonsingular v)
    (hKnot : ¬ Kv (v : G) ≤ M L)
    (hcore : Rv T L (v : G) = (Kv (v : G) ⊔ S).pCoreIn 2)
    (hQ : IsElementaryAbelian 2 (Q T L))
    (hindex : (Q T L).relIndex (Rv T L (v : G)) = 2)
    (r : G) (hr : r ∈ Rv T L (v : G))
    (hcomm : ⁅Rv T L (v : G), zpowers r⁆ = zpowers (v : G)) : False :=
  nonsingular_terminal_contradiction_of_Kv T L V S H.chosen D v hv
    hKnot hcore hQ hindex H.core_normalizer_le r hr hcomm

end CFSG.Quasithin.Chapter12.Section06

