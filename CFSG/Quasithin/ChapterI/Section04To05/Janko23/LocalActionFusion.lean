module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.SimplicityReduction
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticAction
public import Theory.GroupAction.FiveOnSixteenIrreducible

/-!
# The Janko local core action and the outside-fusion obstruction

The action of H = C_G(z) on the Frattini quotient of its core Q has kernel Q
and image of order sixty. An element of order five in this image acts without
nonidentity fixed points on the quotient of order sixteen. Orbit counting
then excludes every proper nontrivial invariant subgroup. Transport through
the literal quotient and subgroup maps proves `CoreActionIrreducible z`.
No simplicity or involution-class-count assumption is needed.

Together with the returning conjugate, this proves that the local weak closure
contains Q. Thus failure of `HasFusionOutsideCore z` is equivalent to that weak
closure being Q. This distinction is essential: Aschbacher, *Sporadic Groups*,
46.14(5)(b), printed pp. 258–259, gives exactly this equality in the J₂ case.
Consequently outside fusion cannot be required for both branches of I.4.7.
The proof of 46.15 uses a separate normal-closure argument for J₂, appealing
to 8.11 and 47.3(1). For J₃ it uses outside involutions and the single class.
Neither source fusion assertion nor the J₂ simplicity argument is proved here.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.7,
printed p. 418; Aschbacher, *Sporadic Groups*, 46.1 and 46.14–46.15.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Conjugation by the literal involution centralizer on the intrinsic
Frattini quotient of its generalized Fitting subgroup. -/
@[expose] public noncomputable def coreFrattiniAction (z : G) :
    involutionCentralizer z →* MulAut (localCore z ⧸ frattini (localCore z)) :=
  (quotientAut (frattini (localCore z))).comp MulAut.conjNormal

private theorem frattini_action_kernel_of_eq_pCore {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal] (he : Q = pCore 2 H)
    (hc : centralizer (Q : Set H) ≤ Q) :
    ((quotientAut (frattini Q)).comp (MulAut.conjNormal : H →* MulAut Q)).ker = Q := by
  subst Q
  exact pCore_frattini_action_kernel 2 hc

/-- The exact kernel of the local Frattini action is the local core. -/
public theorem HTypeAt.coreFrattiniAction_kernel (h : HTypeAt z) :
    (coreFrattiniAction z).ker = localCore z :=
  frattini_action_kernel_of_eq_pCore _ h.core_eq_pCore
    (centralizer_generalizedFitting_le _)

/-- The intrinsic Frattini quotient of the core has order sixteen. -/
public theorem HTypeAt.core_frattini_quotient_card (h : HTypeAt z) :
    Nat.card (localCore z ⧸ frattini (localCore z)) = 16 := by
  let := h.core_isExtraspecial
  rw [IsExtraspecial.frattini_eq_center_two]
  have hc := card_eq_card_quotient_mul_card_subgroup (center (localCore z))
  rw [h.core_card, IsExtraspecial.center_order_p 2] at hc
  omega

/-- The actual image of the local Frattini action has order sixty. -/
public theorem HTypeAt.coreFrattiniAction_range_card (h : HTypeAt z) :
    Nat.card (coreFrattiniAction z).range = 60 := by
  rw [← index_ker, h.coreFrattiniAction_kernel]
  exact h.quotient_card


/-- The local core has no intermediate H-invariant subgroup above the involution line. -/
public theorem HTypeAt.coreActionIrreducible (h : HTypeAt z) : CoreActionIrreducible z := by
  let := h.core_isExtraspecial
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro R hzR hRQ hnorm
  let H := involutionCentralizer z
  let Q := localCore z
  let V := Q ⧸ frattini Q
  let k : Q →* G := H.subtype.comp Q.subtype
  let q : Q →* V := QuotientGroup.mk' (frattini Q)
  let D : Subgroup Q := R.comap k
  let Dbar : Subgroup V := D.map q
  have hPhiLine : frattini Q ≤ (zpowers z).comap k := by
    rw [IsExtraspecial.frattini_eq_center_two]
    intro x hx
    let e : Q ≃* ambientCore z :=
      Q.equivMapOfInjective H.subtype H.subtype_injective
    have hxZ : e x ∈ center (ambientCore z) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      exact (e.map_mul y x).symm.trans
        ((congrArg e (mem_center_iff.mp hx y)).trans (e.map_mul x y))
    exact h.core_center_image ▸ mem_map_of_mem (ambientCore z).subtype hxZ
  have hPhiD : frattini Q ≤ D := hPhiLine.trans (comap_mono hzR)
  have hkerD : q.ker ≤ D := by
    change (QuotientGroup.mk' (frattini Q)).ker ≤ D
    rw [QuotientGroup.ker_mk']
    exact hPhiD
  have hforward (a : H) (v : V) (hv : v ∈ Dbar) :
      coreFrattiniAction z a v ∈ Dbar := by
    obtain ⟨x, hx, rfl⟩ := hv
    refine mem_map.mpr ⟨MulAut.conjNormal a x, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hnorm a.property) (k x)).mp hx
    · exact (quotientAut_apply_mk (frattini Q) (MulAut.conjNormal a) x).symm
  have hdiv : 5 ∣ Nat.card (coreFrattiniAction z).range := by
    rw [h.coreFrattiniAction_range_card]
    decide
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hdiv
  let A := zpowers (a : MulAut V)
  have hA : Nat.card A = 5 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hAR : A ≤ (coreFrattiniAction z).range := zpowers_le.mpr a.property
  have hforwardA (a : A) (v : V) (hv : v ∈ Dbar) : a • v ∈ Dbar := by
    obtain ⟨b, hb⟩ := hAR a.property
    change (a : MulAut V) v ∈ Dbar
    rw [← hb]
    exact hforward b v hv
  let : IsInvariant A V Dbar := ⟨fun a v => ⟨hforwardA a v, fun hv => by
    simpa only [inv_smul_smul] using hforwardA a⁻¹ (a • v) hv⟩⟩
  have hfixed := SmallNonabelianTwoGroup.order_five_actor_fixed_subgroup_eq_bot
    h.core_frattini_quotient_card A hA
  have hrange : k.range = ambientCore z := by
    dsimp only [k]
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hmap : D.map k = R := by
    dsimp [D]
    rw [map_comap_eq, hrange, inf_eq_right.mpr hRQ]
  rcases invariant_eq_bot_or_top_of_five_actor hA h.core_frattini_quotient_card
      hfixed Dbar with hd | hd
  · have hD : D = frattini Q := by
      rw [← comap_map_eq_self hkerD, show D.map q = ⊥ from hd]
      change q.ker = frattini Q
      exact QuotientGroup.ker_mk' _
    left
    apply le_antisymm _ hzR
    rw [← hmap, hD]
    exact map_le_iff_le_comap.mpr hPhiLine
  · have hD : D = ⊤ := by
      rw [← comap_map_eq_self hkerD, show D.map q = ⊤ from hd, comap_top]
    right
    rw [← hmap, hD, ← MonoidHom.range_eq_map, hrange]


open Theory.GroupTheory.ExtraspecialCentralizerSimplicity

/-- Irreducibility and the returning conjugate put the whole core in the local weak closure. -/
public theorem HTypeAt.ambientCore_le_weakClosure (h : HTypeAt z) :
    ambientCore z ≤ weakClosure z (involutionCentralizer z) := by
  let W := weakClosure z (involutionCentralizer z)
  have hnorm : involutionCentralizer z ≤ normalizer
      ((W ⊓ ambientCore z : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact ⟨(mem_normalizer_iff.mp (le_normalizer_weakClosure z _ hg) x).mp hx.1,
      (mem_normalizer_iff.mp (h.normalizer_core.symm ▸ hg) x).mp hx.2⟩
  have hzW : z ∈ W := subset_closure
    ⟨mem_centralizer_singleton_iff.mpr rfl, IsConj.refl z⟩
  rcases h.coreActionIrreducible (W ⊓ ambientCore z)
      (zpowers_le.mpr ⟨hzW, involution_mem_core⟩) inf_le_right hnorm with he | he
  · exfalso
    apply h.not_weakly_closed
    apply (weakClosure_eq_zpowers_iff z h.involution (ambientCore z) involution_mem_core).mp
    apply le_antisymm
    · rw [← he]
      apply (closure_le _).mpr
      intro t ht
      exact ⟨subset_closure ⟨ambientCore_le z ht.1, ht.2⟩, ht.1⟩
    · exact zpowers_le.mpr (subset_closure ⟨involution_mem_core, IsConj.refl z⟩)
  · exact he ▸ inf_le_left

/-- The outside-fusion obligation is incompatible with weak closure equal to Q.
Aschbacher 46.14(5)(b) asserts this equality for the J₂ branch; that source
assertion is not proved by the present equivalence. -/
public theorem HTypeAt.not_hasFusionOutsideCore_iff (h : HTypeAt z) :
    ¬ HasFusionOutsideCore z ↔ weakClosure z (involutionCentralizer z) = ambientCore z := by
  constructor
  · intro hn
    apply le_antisymm _ h.ambientCore_le_weakClosure
    apply (closure_le _).mpr
    intro t ht
    by_contra htQ
    exact hn ⟨t, ht.1, ht.2, htQ⟩
  · intro he hf
    exact hf.weakClosure_ne he

/-- The proved irreducibility discharges the action premise of the simplicity criterion.
The outside-fusion premise remains explicit; it cannot be supplied in the J₂ branch. -/
public theorem HTypeAt.isSimpleGroup_of_fusionOutsideCore (h : HTypeAt z)
    (hf : HasFusionOutsideCore z) : IsSimpleGroup G :=
  h.isSimpleGroup_of_local_action_fusion h.coreActionIrreducible hf

end CFSG.Quasithin.Janko23
