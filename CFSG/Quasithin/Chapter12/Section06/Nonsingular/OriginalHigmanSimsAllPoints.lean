module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalJankoFour
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalRank
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedFreeFusion
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerConjugacy
public import Theory.GroupTheory.FixedElementaryTransport

/-!
# The actual HS central quotient at every original nonsingular point

One preferred escaping point has its full HS cover after the J4 exclusion.
The original fixed-free A8 action is transitive on nonsingular points.
Conjugation transports the canonical centralizer residual itself and its
entire center, giving the same HS quotient at every original point.
This supplies the pointwise markings needed for intersection comparisons;
no new uniform local-classification premise is introduced.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every original nonsingular residual has the literal HS central quotient
if one nonsingular centralizer escapes the original maximal overgroup. -/
theorem SourceHypothesis.original_hs_all_nonsingular_points
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ ∀ w : V, D.Nonsingular w →
      IsQuasisimple (Kv (w : G)) ∧ ¬ Kv (w : G) ≤ M L ∧
      Nonempty (((Kv (w : G)) ⧸ center (Kv (w : G))) ≃*
        Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨hZ,_,u,hu,_,_,hi,_,hnot,_,_,_,hK,hmodels⟩ :=
    H.exists_preferred_nonsingular_quasisimple_escape D hTV hTI v hv he
  have heHS : Nonempty (((Kv (u : G)) ⧸ center (Kv (u : G))) ≃*
      Sporadic.LeechRelated.HS.Carrier) := by
    rcases hmodels with hhs | hj4
    · obtain ⟨_,e,_,_⟩ := hhs
      exact ⟨e⟩
    · obtain ⟨e⟩ := hj4
      exact (H.original_nonsingular_not_jankoFour D u hu hK hTV hi e).elim
  obtain ⟨e⟩ := heHS
  refine ⟨hZ,?_⟩
  intro w hw
  obtain ⟨l,hl⟩ := D.fixed_free_orbit_of_same_form H.chosen hZ u w
    (nonsingular_ne_one D hu) (nonsingular_ne_one D hw) (by simp [hu,hw])
  have hpoint : (MulAut.conj (l : G)) (u : G) = (w : G) := congrArg Subtype.val hl
  have hmap : (Kv (u : G)).map (MulAut.conj (l : G)).toMonoidHom = Kv (w : G) := by
    rw [Kv_map_conjugation,hpoint]
  let c : Kv (u : G) ≃* Kv (w : G) :=
    ((MulAut.conj (l : G)).subgroupMap (Kv (u : G))).trans (MulEquiv.subgroupCongr hmap)
  let := hK
  have hKw : IsQuasisimple (Kv (w : G)) := IsQuasisimple.of_mulEquiv c
  refine ⟨hKw,?_,⟨(QuotientGroup.congr _ _ c (FixedElementary.map_center c)).symm.trans e⟩⟩
  intro hwM
  apply hnot
  intro x hx
  have hxM := hwM (hmap ▸ mem_map_of_mem (MulAut.conj (l : G)).toMonoidHom hx)
  have hlM : (l : G) ∈ M L := L.le_normalizer l.property
  have hh := (M L).mul_mem ((M L).mul_mem ((M L).inv_mem hlM) hxM) hlM
  change (l : G)⁻¹ * ((l : G)*x*(l : G)⁻¹) * (l : G) ∈ M L at hh
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter12.Section06
