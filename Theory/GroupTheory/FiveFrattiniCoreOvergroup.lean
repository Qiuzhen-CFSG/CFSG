module
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.EmbeddedCoreCentralizer
public import Theory.GroupAction.FaithfulSixteen

/-!
# Intrinsic core rigidity in a Sylow-preserving overgroup

Let H embed in a finite characteristic-two group K and contain a Sylow
2-subgroup of K. Suppose H also has characteristic two, its core's center
is central in K, its Frattini quotient has order sixteen and an action
image divisible by five, and its Frattini subgroup lies in its second
center. Then the embedded core is O₂(K).

Pull O₂(K) back into O₂(H). Characteristic-two descent gives a
self-centralizing image modulo the local core's center. The five-action
makes the Frattini quotient irreducible. A proper pullback would lie in
the Frattini subgroup, hence its image in the central quotient would be
central and self-centralizing, forcing the pullback to be the whole core.

Source: the centralizer chain in Aschbacher--Smith 14.2.21, printed
pp.988--989. This argument precedes whole-parabolic recognition.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup

/-- A Sylow-preserving characteristic-two overgroup has the same core when
its embedded core has an irreducible binary four-dimensional Frattini quotient
and its Frattini subgroup lies in the second center. -/
theorem core_eq_of_five_frattini_second_center
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (i : H →* K) (hi : Function.Injective i)
    (S : Sylow 2 K) (hS : (S : Subgroup K) ≤ i.range)
    (hcH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hcK : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hZ : (center (pCore 2 H)).map (i.comp (pCore 2 H).subtype) ≤ center K)
    (hPhi : frattini (pCore 2 H) ≤ upperCentralSeries (pCore 2 H) 2)
    (hV : Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) = 16)
    (hfive : 5 ∣ Nat.card (H ⧸ pCore 2 H)) :
    pCore 2 K = (pCore 2 H).map i := by
  let P := pCore 2 H
  let Q := pCore 2 K
  let f := i.comp P.subtype
  have hf : Function.Injective f := hi.comp P.subtype_injective
  have hQr : Q ≤ i.range := (pCore_isPGroup.le_sylow_of_normal S).trans hS
  have hpre : Q.comap i ≤ P :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  have hQP : Q ≤ P.map i := by
    simpa only [map_comap_eq_self hQr] using map_mono (f := i) hpre
  have hQf : Q ≤ f.range := by
    simpa only [f, MonoidHom.range_comp, range_subtype] using hQP
  let Z := (center P).map f
  have hZc : Z ≤ center K := hZ
  let : Z.Normal := ⟨fun z hz k => by
    simpa only [mem_center_iff.mp (hZc hz) k, mul_inv_cancel_right] using hz⟩
  have hZQ : Z ≤ Q := (hZc.trans (center_le_centralizer _)).trans hcK
  let R := Q.comap f
  have hZR : center P ≤ R := by
    intro z hz
    exact hZQ (mem_map_of_mem f hz)
  have hself : centralizer (R.map (QuotientGroup.mk' (center P)) : Set (P ⧸ center P)) ≤
      R.map (QuotientGroup.mk' (center P)) :=
    ambient_quotient_centralizer_pullback f hf Z (center P) rfl Q hQf
      (centralizer_image_pCore_le_of_central_quotient Z hZc hcK)
  let a : H →* MulAut (P ⧸ frattini P) :=
    (quotientAut (frattini P)).comp (MulAut.conjNormal : H →* MulAut P)
  have ha : a.ker = P := pCore_frattini_action_kernel 2 hcH
  have hfive' : 5 ∣ Nat.card a.range := by
    let e := (QuotientGroup.quotientMulEquivOfEq ha.symm).trans
      (QuotientGroup.quotientKerEquivRange a)
    exact (Nat.card_congr e.toEquiv) ▸ hfive
  have hforward (h : H) (v : P ⧸ frattini P)
      (hv : v ∈ R.map (QuotientGroup.mk' (frattini P))) :
      a h v ∈ R.map (QuotientGroup.mk' (frattini P)) := by
    obtain ⟨x,hx,rfl⟩ := hv
    refine ⟨MulAut.conjNormal h x, ?_, ?_⟩
    · change i (h * (x : H) * h⁻¹) ∈ Q
      simp only [map_mul, map_inv]
      exact (inferInstance : Q.Normal).conj_mem (f x) hx (i h)
    · exact (quotientAut_apply_mk (frattini P) (MulAut.conjNormal h) x).symm
  have hRtop : R = ⊤ := by
    rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five a hfive' hV
        (R.map (QuotientGroup.mk' (frattini P))) (fun h v =>
          ⟨hforward h v, fun hv => by
            have hh := hforward h⁻¹ (a h v) hv
            rw [map_inv] at hh
            change (a h).symm (a h v) ∈ _ at hh
            simpa only [MulEquiv.symm_apply_apply] using hh⟩) with hb | ht
    · have hRPhi : R ≤ frattini P := by
        simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff R).mp hb
      have hRc : R.map (QuotientGroup.mk' (center P)) ≤ center (P ⧸ center P) := by
        rw [map_le_iff_le_comap]
        have he := comap_upperCentralSeries_quotient_center (G := P) 1
        rw [upperCentralSeries_one] at he
        rw [he]
        exact hRPhi.trans hPhi
      apply top_unique
      intro x _
      have hx : QuotientGroup.mk' (center P) x ∈ R.map (QuotientGroup.mk' (center P)) := by
        apply hself
        intro y hy
        exact (mem_center_iff.mp (hRc hy) _).symm
      exact (comap_map_eq_self (f := QuotientGroup.mk' (center P))
        (by simpa only [QuotientGroup.ker_mk'] using hZR)) ▸ hx
    · apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini P))) ht
      simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hh
  apply le_antisymm hQP
  rintro y ⟨x,hx,rfl⟩
  have hh : (⟨x,hx⟩ : P) ∈ R := hRtop ▸ mem_top _
  exact hh

end Subgroup
