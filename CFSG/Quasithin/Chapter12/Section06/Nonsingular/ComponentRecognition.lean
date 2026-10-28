module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ComponentRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedResidual
/-!
# Recognition of the original nonsingular component

The genuine A₆ quotient of L_v gives a simple-core seed of three-rank two
inside G_v. The cubic residual recognition theorem identifies its containing
C-component with the literal K_v = O^{3′}(G_v^∞). Its relative normality and
quasisimple two-core quotient prove every clause of 12.6.3. Rank addition
also excludes the head's cubic center, giving the simplicity in 12.6.13(2).

The preferred-point application retains the original V, V_v and K_v, and
combines this recognition with the proved strict enlargement and escape.
The earlier T-invariance and TI premises retain producer qt-d-1222-source
and final discharge owner qt-d-12634-source. The remaining quasisimple
exclusions, block construction, splitting and fixed-space elimination are
still required; neither 12.6.2 nor 12.6.23 is asserted here.

Source: Aschbacher--Smith, 12.6.3, 12.6.11 and 12.6.13(2), pp.824--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- All clauses of source 12.6.3 for the original canonical K_v. -/
theorem SourceHypothesis.nonsingular_canonical_component
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    ((Kv (v : G)).subgroupOf (Gv (v : G))).IsCComponent ∧
      Lv L (v : G) ≤ Kv (v : G) ∧
      ((Kv (v : G)).subgroupOf (Gv (v : G))).Normal ∧
      IsQuasisimple (Star (Kv (v : G))) ∧ IsSimpleGroup (Star (Kv (v : G))) := by
  let A := Gv (v : G)
  let B := (Lv L (v : G)).subgroupOf A
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let b : B ≃* Lv L (v : G) := subgroupOfEquivOfLe (Lv_le_Gv L (v : G))
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L (v : G) e
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eB.symm
  have hp : IsPPerfect 2 B := (isPPerfect_embedded_pResidual 2 (CLv L (v : G))).of_surjective
    b.symm.toMonoidHom b.symm.surjective
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient (pCore 2 B) pCore_isPGroup hp
  have hr : 2 ≤ primeRank 3 B := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_equiv 3 eB]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hv2 : orderOf (v : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v.property)
    (fun he => nonsingular_ne_one D hv (Subtype.ext he))
  have hsq : IsSQTK KnownSimple.IsKnownSimple A := H.source.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer hv2)
  have hd : 3 ∣ Nat.card (B ⧸ pCore 2 B) := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hB3 := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 B) pCore_isPGroup hp hd
  obtain ⟨hc,_,hn,hq,hs⟩ := Chapter1.Section02.simple_core_rank_threeResidual_recognition hsq B ht hr hB3
  let R := (primeToResidual 3 (solvableResidual A)).map (solvableResidual A).subtype
  have he : (Kv (v : G)).subgroupOf A = R := by
    change (R.map A.subtype).comap A.subtype = R
    exact comap_map_eq_self_of_injective A.subtype_injective R
  let c : R ≃* Kv (v : G) := R.equivMapOfInjective A.subtype A.subtype_injective
  let := hq
  let := hs
  let eq : (R ⧸ pCore 2 R) ≃* Star (Kv (v : G)) :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  exact ⟨he.symm ▸ hc,Lv_le_Kv_of_A6 L (v : G) e,he.symm ▸ hn,
    IsQuasisimple.of_mulEquiv eq,eq.symm.isSimpleGroup⟩

/-- The preferred escaping point has the recognized canonical component and
strict residual enlargement; no replacement of V_v or of K_v is made. -/
theorem SourceHypothesis.exists_preferred_nonsingular_component_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot⟩ :=
    H.exists_preferred_nonsingular_residual_escape D hTV hTI v hv he
  have hc := H.nonsingular_canonical_component D w hw
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc.1,hc.2.2.2⟩
end CFSG.Quasithin.Chapter12.Section06
