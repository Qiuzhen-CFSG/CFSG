module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.ModelMarking

/-!
# Transporting the exact ambient fusion marking

Every local model isomorphism sends t to the unique nonidentity central
element. The normal fusion four V omits t, so its image is the canonical
Klein four in S₄. An involution outside E has odd symmetric coordinate and
is therefore conjugate inside the model to r or tr. If neither is an ambient
z-conjugate, the ambient first class in C is exactly V minus the identity.
This uses actual subgroup inclusions and conjugacy in G throughout.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, the opening of Lemma 4.2, p.39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

public theorem unmarked_central (h : Hypotheses z) (a : SelectedFusionData h)
    {t : G} (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2)
    (e : localCentralizer z t a.g ≃* Model 4) :
    e (centralElement h a htE) = centralInvolution 4 := by
  apply model_central_unique
  · apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (e.toMonoidHom.map_mul x (centralElement h a htE)).symm.trans
      ((congrArg e (mem_center_iff.mp (centralElement_mem_center h a htE) x)).trans
        (e.map_mul _ _))
  · intro he
    have hc := centralElement_order h a htE ht
    have ht1 := e.injective (he.trans e.map_one.symm)
    simp [ht1] at hc

public theorem unmarked_four (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (e : localCentralizer z t a.g ≃* Model 4) :
    (four z t a.g).map e.toMonoidHom = modelFour := by
  let : (four z t a.g).Normal := four_normal h d a t
  let : IsElementaryAbelian 2 (four z t a.g) := four_elementary h a htE
  let : ((four z t a.g).map e.toMonoidHom).Normal :=
    (inferInstance : (four z t a.g).Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 ((four z t a.g).map e.toMonoidHom) :=
    IsElementaryAbelian.map e.toMonoidHom
  apply normal_four_eq_modelFour
  · exact (card_map_of_injective e.injective).trans (four_card h d a htE)
  · rintro ⟨x, hx, he⟩
    apply centralElement_not_four h d a htE ht hnt
    have hxτ : x = centralElement h a htE :=
      e.injective (he.trans (unmarked_central h a htE ht e).symm)
    exact hxτ ▸ hx

public theorem unmarked_first_iff (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (e : localCentralizer z t a.g ≃* Model 4) (x : localCentralizer z t a.g) :
    FirstClass (e x) ↔ x ∈ four z t a.g ∧ x ≠ 1 := by
  rw [modelFour_first, ← unmarked_four h d a htE ht hnt e]
  constructor
  · rintro ⟨⟨y, hy, he⟩, hn⟩
    exact ⟨e.injective he ▸ hy, fun hx => hn (hx ▸ e.map_one)⟩
  · rintro ⟨hx, hn⟩
    exact ⟨mem_map_of_mem e.toMonoidHom hx, fun he => hn (e.injective (he.trans e.map_one.symm))⟩

public theorem outside_involution_odd (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (e : localCentralizer z t a.g ≃* Model 4) (x : localCentralizer z t a.g)
    (hx : x ^ 2 = 1) (hxE : x ∉ eight z t a.g) : Equiv.Perm.sign (e x).2 = -1 := by
  apply (Int.units_eq_one_or _).resolve_left
  intro hs
  have hex2 : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hfour {y : localCentralizer z t a.g} (hy : e y ∈ modelFour) : y ∈ four z t a.g := by
    rw [← unmarked_four h d a htE ht hnt e] at hy
    obtain ⟨v, hv, hvy⟩ := hy
    exact e.injective hvy ▸ hv
  rcases even_involution_plane_or_translate hex2 hs with hxV | hxTV
  · exact hxE (four_le_eight z t a.g (hfour hxV))
  · have hm : centralElement h a htE * x ∈ eight z t a.g := by
      apply four_le_eight z t a.g
      apply hfour
      simpa only [map_mul, unmarked_central h a htE ht e] using hxTV
    have htmem : centralElement h a htE ∈ eight z t a.g := htE
    exact hxE (by simpa only [inv_mul_cancel_left] using
      (eight z t a.g).mul_mem ((eight z t a.g).inv_mem htmem) hm)

/-- An isomorphism of the local group automatically has the exact source
marking once r and tr are known not to be ambient z-conjugates. -/
public theorem local_marking (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) {t : G} (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (e : localCentralizer z t a.g ≃* Model 4)
    (r : localCentralizer z t a.g) (hr : orderOf r = 2) (hrE : r ∉ eight z t a.g)
    (hrn : ¬ IsConj z (ambient z t a.g r))
    (htrn : ¬ IsConj z (ambient z t a.g (centralElement h a htE * r)))
    (x : localCentralizer z t a.g) :
    IsConj z (ambient z t a.g x) ↔ FirstClass (e x) := by
  have hc := unmarked_central h a htE ht e
  have hback {v w : localCentralizer z t a.g} (hv : IsConj (e v) (e w)) :
      IsConj (ambient z t a.g v) (ambient z t a.g w) := by
    have hh := (ambient z t a.g).map_isConj (e.symm.toMonoidHom.map_isConj hv)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh
  constructor
  · intro hf
    have hxord : orderOf x = 2 := by
      obtain ⟨k, hk⟩ := isConj_iff.mp hf
      have hh := (MulAut.conj k).orderOf_eq z
      rw [show (MulAut.conj k) z = ambient z t a.g x from hk,
        orderOf_injective (ambient z t a.g) (ambient_injective z t a.g)] at hh
      exact hh.trans h.involution
    by_cases hxE : x ∈ eight z t a.g
    · apply (unmarked_first_iff h d a htE ht hnt e x).mpr
      refine ⟨⟨hxE, subset_closure ⟨hxE.1, hf⟩⟩, ?_⟩
      intro he
      simp [he] at hxord
    · have hx2 : x ^ 2 = 1 := hxord ▸ pow_orderOf_eq_one x
      have hr2 : r ^ 2 = 1 := hr ▸ pow_orderOf_eq_one r
      have hrs := outside_involution_odd h d a htE ht hnt e r hr2 hrE
      have hxs := outside_involution_odd h d a htE ht hnt e x hx2 hxE
      have her : (e r) ^ 2 = 1 := by rw [← map_pow, hr2, map_one]
      have hex : (e x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
      rcases odd_involution_classes her hrs hex hxs with hh | hh
      · exact (hrn (hf.trans (hback hh).symm)).elim
      · rw [← hc, ← map_mul] at hh
        exact (htrn (hf.trans (hback hh).symm)).elim
  · intro hf
    obtain ⟨hx, hx1⟩ := (unmarked_first_iff h d a htE ht hnt e x).mp hf
    exact d.fusion _ hx.2 (fun he => hx1 ((ambient_injective z t a.g) (he.trans (map_one _).symm)))

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
