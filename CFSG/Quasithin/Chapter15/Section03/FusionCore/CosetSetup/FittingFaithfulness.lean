module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Components
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Layer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Consequences

/-!
# Generalized-Fitting centralization and faithfulness in 15.3.49

Write U = ⟨Z_S^H⟩, Q = O₂(H), and U_C = C_U(Q). The genuine empty
L_f(G,T) hypothesis, A.4.8, and the Frattini bound of 15.3.48 show that
all C-components centralize U_C. Coprime action handles the inverse image
of F(H/Q), hence the inverse image of F*(H/Q) centralizes U_C. This is
O_{2,F*}(H), distinct from F*(H) = Q in this setup.

A displacement homomorphism makes the intersection of the kernel on
U/U_C with this inverse image a normal two-group. A normal subgroup
disjoint from F* is trivial, so H/Q acts faithfully on U/U_C. The actual
action is constructed with its formula on every quotient representative.
The outside-family and Sylow hypotheses make H/Q nontrivial; normal
generation and the order-two bound give [Z_S,Q] = Z. Taking H = M_c
gives 15.3.49(2).

Only the given source conclusions of 15.3.48 and earlier local facts are
inputs. No abelianness of U or V_H and no specialized centralization or
faithfulness premise is assumed. The parent owns the verification of
15.3.48. `FittingFaithfulness.DualApplication` supplies this proved faithful
action to the existing commutator-duality consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(a) through (2), printed p.1142. The C-component route is detailed
in `FittingFaithfulness.Components` and uses A.4.8 without a reduced-witness
or chief-factor premise.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

/-- The fixed core inside H is the intersection with the literal intrinsic
centralizer of O₂(H). -/
theorem fixedCore_subgroupOf_eq {G : Type*} [Group G] (A H : Subgroup G) :
    (fixedCore A H).subgroupOf H = (localSpan A H).subgroupOf H ⊓
      centralizer (pCore 2 H : Set H) := by
  ext x
  change (x : G) ∈ localSpan A H ∧ (x : G) ∈ centralizer (H.pCoreIn 2 : Set G) ↔ _
  constructor
  · rintro ⟨hu, hc⟩
    exact ⟨hu, fun q hq => Subtype.ext (hc q (mem_map_of_mem H.subtype hq))⟩
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (hc q hq)

/-- Computing the span in H gives exactly the relative ambient span. -/
theorem relativeSpan_eq {G : Type*} [Group G] (A H : Subgroup G) (hAH : A ≤ H) :
    localSpan (A.subgroupOf H) ⊤ = (localSpan A H).subgroupOf H := by
  apply (map_injective H.subtype_injective)
  rw [map_localSpan_subgroupOf A H hAH,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hAH)]

/-- The central involutions of a restricted Sylow subgroup are exactly
the ambient central involutions, embedded from H. -/
theorem centralInvolutions_subtype_map {G : Type*} [Group G]
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (centralInvolutions (T.subtype hTH)).map H.subtype = centralInvolutions T := by
  change (omegaOneCenterAmbient ((T : Subgroup G).subgroupOf H)).map H.subtype =
    omegaOneCenterAmbient (T : Subgroup G)
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hTH]

/-- The generalized-Fitting centralization for the local span, proved from
the genuine empty family, characteristic two, and the source Frattini bound. -/
theorem span_generalizedFitting_centralizes
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (A : Subgroup H)
    (hUQ : localSpan A ⊤ ≤ pCore 2 H)
    (hPhi : (frattini (localSpan A ⊤)).map (localSpan A ⊤).subtype ≤ center H)
    (hZ : centralInvolutions (T.subtype hTH) ≤ center H) :
    (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer ((localSpan A ⊤ ⊓ centralizer (pCore 2 H : Set H)) : Set H) := by
  let U := localSpan A ⊤
  let C := U ⊓ centralizer (pCore 2 H : Set H)
  have hCQ : C ≤ pCore 2 H := inf_le_left.trans hUQ
  have hCp : IsPGroup 2 C := pCore_isPGroup.to_le hCQ
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (fun x hx y hy => hx.2 y (hCQ hy))
  have hsq : ∀ c ∈ C, c ^ 2 ∈ center H := by
    intro c hc
    let : Fact (IsPGroup 2 U) := ⟨pCore_isPGroup.to_le hUQ⟩
    exact hPhi (mem_map_of_mem U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨c, hc.1⟩ : U)))
  apply generalizedFitting_preimage_centralizes_of_cComponents (T.subtype hTH) C hCp
    (le_centralizer_iff.mp (inf_le_right : C ≤ centralizer (pCore 2 H : Set H))) hZ
  exact cComponents_centralize_of_emptyLf T H hTH hQ hc hempty C hCQ inf_le_right hsq

/-- Faithfulness in the form consumed by the dual-action argument. The
centralization premise is discharged here, using the standing empty family
and the earlier 15.3.48 conclusions. -/
theorem span_faithful_of_emptyLf
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (A Z : Subgroup H) [Z.Normal]
    (hUQ : localSpan A ⊤ ≤ pCore 2 H)
    (hPhi : (frattini (localSpan A ⊤)).map (localSpan A ⊤).subtype ≤ center H)
    (hZ : centralInvolutions (T.subtype hTH) ≤ center H)
    (hsmall : centralizerModulo ⊤ (localSpan A ⊤) Z ≤ pCore 2 H) :
    ∀ h : H, (∀ u : localSpan A ⊤,
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤))
        ⟨h * u * h⁻¹, (inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h⟩ =
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤)) u) →
      h ∈ pCore 2 H :=
  span_faithful_on_representatives A Z hUQ hsmall
    (span_generalizedFitting_centralizes T H hTH hQ hc hempty A hUQ hPhi hZ)

/-- A kernel equality constructs the faithful action of the actual
core quotient, with its formula on every quotient representative. -/
theorem exists_faithful_quotient_action
    {G : Type*} [Group G] (U C : Subgroup G) [U.Normal] [C.Normal]
    (hker : centralizerModulo ⊤ U C = pCore 2 G) :
    ∃ ρ : (G ⧸ pCore 2 G) →* MulAut (U ⧸ C.subgroupOf U),
      Function.Injective ρ ∧ ∀ g : G, ∀ u : U,
        ρ (QuotientGroup.mk' (pCore 2 G) g) (QuotientGroup.mk' (C.subgroupOf U) u) =
          QuotientGroup.mk' (C.subgroupOf U)
            ⟨g * u * g⁻¹, (inferInstance : U.Normal).conj_mem u u.property g⟩ := by
  let a := quotientAction (⊤ : Subgroup G) U C le_normalizer_of_normal le_normalizer_of_normal
  let f : G →* MulAut (U ⧸ C.subgroupOf U) := a.comp topEquiv.symm.toMonoidHom
  have hf : f.ker = centralizerModulo ⊤ U C := by
    ext g
    change (topEquiv.symm g) ∈ a.ker ↔ g ∈ centralizerModulo ⊤ U C
    rw [quotientAction_ker ⊤ U C le_normalizer_of_normal le_normalizer_of_normal le_top,
      mem_quotientCentralizer_iff ⊤ U C le_top, mem_centralizerModulo_iff]
    simp only [mem_top, true_and]
    rfl
  have he : f.ker = pCore 2 G := hf.trans hker
  let ρ := QuotientGroup.lift (pCore 2 G) f he.symm.le
  refine ⟨ρ, (QuotientGroup.injective_lift_iff _ _ _).mpr he.symm, ?_⟩
  intro g u
  exact quotientAction_apply ⊤ U C le_normalizer_of_normal le_normalizer_of_normal
    (topEquiv.symm g) u

/-- The faithful action is a genuine homomorphism from H/O₂(H) to the
automorphisms of U/C_U(Q), not just a statement about a labelled actor. -/
theorem span_quotient_action_of_emptyLf
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (A Z : Subgroup H) [Z.Normal]
    (hUQ : localSpan A ⊤ ≤ pCore 2 H)
    (hPhi : (frattini (localSpan A ⊤)).map (localSpan A ⊤).subtype ≤ center H)
    (hZ : centralInvolutions (T.subtype hTH) ≤ center H)
    (hZcent : Z ≤ center H)
    (hsmall : centralizerModulo ⊤ (localSpan A ⊤) Z = pCore 2 H) :
    ∃ ρ : CoreQuotient H →* MulAut
        ((localSpan A ⊤) ⧸ (centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤)),
      Function.Injective ρ ∧ ∀ h : H, ∀ u : localSpan A ⊤,
        ρ (QuotientGroup.mk' (pCore 2 H) h)
          (QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤)) u) =
        QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤))
          ⟨h * u * h⁻¹, (inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h⟩ := by
  apply exists_faithful_quotient_action
  apply le_antisymm
  · intro h hh
    apply span_faithful_of_emptyLf T H hTH hQ hc hempty A Z hUQ hPhi hZ hsmall.le h
    intro u
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hi := (centralizer (pCore 2 H : Set H)).inv_mem
      ((mem_centralizerModulo_iff.mp hh).2 u u.property)
    change h * (u : H) * h⁻¹ / (u : H) ∈ centralizer (pCore 2 H : Set H)
    simpa only [commutatorElement_def, mul_inv_rev, inv_inv, div_eq_mul_inv, mul_assoc] using hi
  · intro h hh
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _, fun u hu => ?_⟩
    exact (hZcent.trans (center_le_centralizer _))
      ((mem_centralizerModulo_iff.mp (hsmall.symm ▸ hh)).2 u hu)

/-- Source 15.3.49(a) and the reductions leading to (2), for any local H.
The inputs are genuine standing local hypotheses and the indicated earlier
conclusions of 15.3.48; the parent owns their derivation. All spans, cores,
centralizers and quotient actions here are the actual relative subgroups. -/
theorem local_conclusions
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M H A : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M) (hout : ¬ H ≤ M)
    (hAH : A ≤ H) (hZA : centralInvolutions T ≤ A)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hUQ : localSpan (A.subgroupOf H) ⊤ ≤ pCore 2 H)
    (hPhi : (frattini (localSpan (A.subgroupOf H) ⊤)).map
      (localSpan (A.subgroupOf H) ⊤).subtype ≤ (centralInvolutions T).subgroupOf H)
    (hsmall : ∀ h : H,
      (∀ u ∈ localSpan (A.subgroupOf H) ⊤,
        ⁅u,h⁆ ∈ (centralInvolutions T).subgroupOf H) ↔ h ∈ pCore 2 H) :
    (generalizedFitting (CoreQuotient H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
        centralizer ((fixedCore A H).subgroupOf H : Set H) ∧
    (¬ localSpan A H ≤ (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype) ∧
    ⁅A, H.pCoreIn 2⁆ = centralInvolutions T ∧
    ∃ ρ : CoreQuotient H →* MulAut
        ((localSpan (A.subgroupOf H) ⊤) ⧸
          (centralizer (pCore 2 H : Set H)).subgroupOf (localSpan (A.subgroupOf H) ⊤)),
      Function.Injective ρ ∧ ∀ h : H, ∀ u : localSpan (A.subgroupOf H) ⊤,
        ρ (QuotientGroup.mk' (pCore 2 H) h)
          (QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf
            (localSpan (A.subgroupOf H) ⊤)) u) =
        QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf
          (localSpan (A.subgroupOf H) ⊤))
          ⟨h * u * h⁻¹, (inferInstance : (localSpan (A.subgroupOf H) ⊤).Normal).conj_mem
            u u.property h⟩ := by
  let Z := (centralInvolutions T).subgroupOf H
  let U := localSpan (A.subgroupOf H) ⊤
  let : Z.Normal := layer_normal H (centralInvolutions T) hHZ
  have hZcenter : Z ≤ center H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext ((hHZ h.property z hz).symm)
  have hZrest : centralInvolutions (T.subtype hTH) ≤ center H := by
    intro z hz
    apply hZcenter
    have hm := mem_map_of_mem H.subtype hz
    rwa [centralInvolutions_subtype_map T H hTH] at hm
  have hcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hZA.trans hAH)).toEquiv).trans hZcard
  have hZU : Z ≤ U := by
    intro z hz
    apply Subgroup.subset_closure
    exact ⟨1, mem_top _, z, hZA hz, by simp⟩
  have hQne : pCore 2 H ≠ ⊥ := by
    intro hb
    have hzb : Z = ⊥ := le_bot_iff.mp ((hZU.trans hUQ).trans hb.le)
    have hzn : Z ≠ ⊥ := (one_lt_card_iff_ne_bot Z).mp (by omega)
    exact hzn hzb
  have heq : centralizerModulo ⊤ U Z = pCore 2 H := by
    ext h
    rw [mem_centralizerModulo_iff]
    simpa only [mem_top, true_and] using hsmall h
  have hfit := span_generalizedFitting_centralizes T H hTH hQne hc hempty
    (A.subgroupOf H) hUQ (hPhi.trans hZcenter) hZrest
  have hfaith := span_faithful_of_emptyLf T H hTH hQne hc hempty
    (A.subgroupOf H) Z hUQ (hPhi.trans hZcenter) hZrest heq.le
  have hnon := span_not_le_centralizer_of_faithful (A.subgroupOf H)
    (twoCore_ne_top_of_outside M H T hTH hTM hout) hfaith
  have hb : ⁅A.subgroupOf H, pCore 2 H⁆ ≤ Z := by
    apply commutator_le.mpr
    intro a ha q hq
    apply (mem_centralizerModulo_iff.mp (heq.symm ▸ hq)).2 a
    exact Subgroup.subset_closure ⟨1, mem_top _, a, ha, by simp⟩
  have hcomm := generator_commutator_eq (A.subgroupOf H) Z hcard hb hnon
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fixedCore_subgroupOf_eq, ← relativeSpan_eq A H hAH]
    exact hfit
  · intro hcen
    apply hnon
    intro u hu q hq
    have hua : (u : G) ∈ localSpan A H := by
      rw [← map_localSpan_subgroupOf A H hAH]
      exact mem_map_of_mem H.subtype hu
    obtain ⟨c, hc, he⟩ := hcen hua
    apply Subtype.ext
    have hh := congrArg (fun x : H.pCoreIn 2 => (x : G))
      ((mem_center_iff.mp hc) ⟨q, mem_map_of_mem H.subtype hq⟩)
    change (c : G) = (u : G) at he
    change (q : G) * (c : G) = (c : G) * (q : G) at hh
    simpa only [he, Subgroup.coe_mul] using hh
  · have hm := congrArg (map H.subtype) hcomm
    rw [map_commutator, map_subgroupOf_eq_of_le hAH,
      map_subgroupOf_eq_of_le (hZA.trans hAH)] at hm
    exact hm
  · exact span_quotient_action_of_emptyLf T H hTH hQne hc hempty
      (A.subgroupOf H) Z hUQ (hPhi.trans hZcenter) hZrest hZcenter heq

/-- Source 15.3.49(2), obtained by taking the actual involution centralizer
M_c for H in the preceding local theorem. The parent supplies 15.3.48 for
M_c, which contains C_Y(V) also in the exceptional branch. -/
theorem lemma_15_3_49_2
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M Mc A : Subgroup G)
    (hTMc : (T : Subgroup G) ≤ Mc) (hTM : (T : Subgroup G) ≤ M) (hout : ¬ Mc ≤ M)
    (hAMc : A ≤ Mc) (hZA : centralInvolutions T ≤ A)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hUQ : localSpan (A.subgroupOf Mc) ⊤ ≤ pCore 2 Mc)
    (hPhi : (frattini (localSpan (A.subgroupOf Mc) ⊤)).map
      (localSpan (A.subgroupOf Mc) ⊤).subtype ≤ (centralInvolutions T).subgroupOf Mc)
    (hsmall : ∀ h : Mc,
      (∀ u ∈ localSpan (A.subgroupOf Mc) ⊤,
        ⁅u,h⁆ ∈ (centralInvolutions T).subgroupOf Mc) ↔ h ∈ pCore 2 Mc) :
    ⁅A, Mc.pCoreIn 2⁆ = centralInvolutions T :=
  (local_conclusions T M Mc A hTMc hTM hout hAMc hZA hZcard hMc.le hc hempty
    hUQ hPhi hsmall).2.2.1

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

end
