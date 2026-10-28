module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.Action

/-!
# Lifting the local central-coset orbit calculation

Each noncentral coset of the extraspecial core center consists of two inner
conjugates. Consequently the inverse image of a coset orbit is one H-orbit,
of twice its cardinality. Orbit--stabilizer with |H| = 192 gives centralizer
orders 32 and 16 for quotient orbits of lengths three and six respectively.

The final two theorems apply these facts to the literal `countCandidates` set,
including its ambient subgroup and common-centralizer convention. They are
conditional on `CosetProfile`; establishing that profile from relative
quaternion normality is the remaining geometric task, not an assumption in
the intended source theorem.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 2.3(2)(b).
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace FusionCount.LocalOrbit
@[expose] public def liftCosets (z : G) (S : Set (CentralInvolutionCosets (Core z))) :
    Set (Core z) := {x | ∃ v ∈ S, QuotientGroup.mk' (center (Core z)) x = v.val}
@[expose] public def elementOrbit (z : G) (x : Core z) : Set (Core z) :=
  Set.range (fun a : Centralizer z => MulAut.conjNormal a x)

public theorem liftCosets_card (h : Hypotheses z)
    (S : Set (CentralInvolutionCosets (Core z))) :
    (liftCosets z S).ncard = 2 * S.ncard := by
  classical
  let π := QuotientGroup.mk' (center (Core z))
  let F := Σ v : S, {x : Core z // π x = v.val.val}
  let f : F → liftCosets z S := fun w => ⟨w.2.val, w.1.val, w.1.property, w.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, x, hx⟩ ⟨w, y, hy⟩ he
      have hxy : x = y := congrArg Subtype.val he
      subst y
      have hvw : v = w := Subtype.ext (Subtype.ext (hx.symm.trans hy))
      subst w
      rfl
    · rintro ⟨x, v, hv, he⟩
      exact ⟨⟨⟨v, hv⟩, ⟨x, he⟩⟩, rfl⟩
  have hcenter : Nat.card (center (Core z)) = 2 := by
    let := h.extraspecial
    exact IsExtraspecial.center_order_p 2 (Core z)
  have hfiber (v : S) : Nat.card {x : Core z // π x = v.val.val} = 2 := by
    have he := MonoidHom.fiberEquivKerOfSurjective
      (QuotientGroup.mk'_surjective (center (Core z))) v.val.val
    change Nat.card (π ⁻¹' {v.val.val}) = 2
    rw [Nat.card_congr he, QuotientGroup.ker_mk']
    exact hcenter
  let := Fintype.ofFinite S
  change Nat.card (liftCosets z S) = 2 * Nat.card S
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

public theorem elementOrbit_eq_liftCosets (h : Hypotheses z)
    (x : Core z) (hx : x ^ 2 = 1) (hxZ : x ∉ center (Core z)) :
    elementOrbit z x = liftCosets z (cosetOrbit z (centralInvolutionCoset x hx hxZ)) := by
  let := h.extraspecial
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨cosetAction z a (centralInvolutionCoset x hx hxZ), ⟨a, rfl⟩, ?_⟩
    change QuotientGroup.mk' (center (Core z)) (MulAut.conjNormal a x) =
      (centralInvolutionCosetAction (MulAut.conjNormal a) (centralInvolutionCoset x hx hxZ)).val
    rw [centralInvolutionCosetAction_val]
    exact (quotientAut_apply_mk _ _ _).symm
  · rintro ⟨v, ⟨a, rfl⟩, he⟩
    have he' : QuotientGroup.mk' (center (Core z)) y =
        QuotientGroup.mk' (center (Core z)) (MulAut.conjNormal a x) := by
      change QuotientGroup.mk' (center (Core z)) y =
        (centralInvolutionCosetAction (MulAut.conjNormal a)
          (centralInvolutionCoset x hx hxZ)).val at he
      rw [centralInvolutionCosetAction_val] at he
      exact he.trans (quotientAut_apply_mk _ _ _)
    have hyZ : y ∉ center (Core z) := by
      intro hy
      have hzero := (QuotientGroup.eq_one_iff y).mpr hy
      have hval : (cosetAction z a (centralInvolutionCoset x hx hxZ)).val = 1 :=
        he.symm.trans hzero
      exact (cosetAction z a (centralInvolutionCoset x hx hxZ)).property.1 hval
    obtain ⟨q, hq⟩ := isConj_iff.mp
      (IsExtraspecial.isConj_of_center_quotient_eq hyZ he').symm
    refine ⟨(q : Centralizer z) * a, ?_⟩
    apply Subtype.ext
    have hh := congrArg Subtype.val hq
    change (q : Centralizer z) * (a * (x : Centralizer z) * a⁻¹) *
      (q : Centralizer z)⁻¹ = (y : Centralizer z) at hh
    change ((q : Centralizer z) * a) * (x : Centralizer z) *
      ((q : Centralizer z) * a)⁻¹ = (y : Centralizer z)
    calc
      _ = (q : Centralizer z) * (a * (x : Centralizer z) * a⁻¹) *
          (q : Centralizer z)⁻¹ := by group
      _ = _ := hh

public theorem elementOrbit_card (h : Hypotheses z)
    (x : Core z) (hx : x ^ 2 = 1) (hxZ : x ∉ center (Core z)) :
    (elementOrbit z x).ncard =
      2 * (cosetOrbit z (centralInvolutionCoset x hx hxZ)).ncard := by
  rw [elementOrbit_eq_liftCosets h x hx hxZ, liftCosets_card h]

public theorem elementOrbit_card_mul_centralizer (h : Hypotheses z) (x : Core z) :
    (elementOrbit z x).ncard *
      Nat.card (Centralizer z ⊓ Centralizer ((x : Centralizer z) : G) : Subgroup G) = 192 := by
  let : MulDistribMulAction (Centralizer z) (Core z) :=
    MulDistribMulAction.compHom _ (MulAut.conjNormal : Centralizer z →* MulAut (Core z))
  have horbit : MulAction.orbit (Centralizer z) x = elementOrbit z x := rfl
  have hstab : MulAction.stabilizer (Centralizer z) x =
      centralizer ({(x : Centralizer z)} : Set (Centralizer z)) := by
    ext a
    change MulAut.conjNormal a x = x ↔ a ∈ centralizer ({(x : Centralizer z)} : Set (Centralizer z))
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro he
      have he' := congrArg Subtype.val he
      exact mul_inv_eq_iff_eq_mul.mp he'
    · intro he
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr he)
  have hcard : Nat.card (MulAction.stabilizer (Centralizer z) x) =
      Nat.card (Centralizer z ⊓ Centralizer ((x : Centralizer z) : G) : Subgroup G) := by
    rw [hstab, ← card_map_of_injective (Centralizer z).subtype_injective,
      map_subtype_centralizer_singleton]
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Centralizer z) x)
  rw [Nat.card_prod, horbit, hcard, h.centralizer_card] at hc
  exact hc

private theorem core_center_mem_iff (h : Hypotheses z) (x : Core z) :
    x ∈ center (Core z) ↔ ((x : Centralizer z) : G) = 1 ∨
      ((x : Centralizer z) : G) = z := by
  classical
  constructor
  · intro hx
    have hm := mem_map_of_mem (Core z).subtype hx
    rw [h.core_center_image, mem_zpowers_iff_mem_range_orderOf,
      h.distinguished_order] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using congrArg (fun a : Centralizer z => (a : G)) he.symm)
    · have hH : (x : Centralizer z) = distinguished z := by
        simpa only [pow_one, Subgroup.subtype_apply] using he.symm
      exact Or.inr (congrArg (fun a : Centralizer z => (a : G)) hH)
  · rintro (hx | hx)
    · have he : x = 1 := Subtype.ext (Subtype.ext hx)
      rw [he]
      exact (center (Core z)).one_mem
    · have hm : (x : Centralizer z) ∈ (center (Core z)).map (Core z).subtype := by
        rw [h.core_center_image, show (x : Centralizer z) = distinguished z from Subtype.ext hx]
        exact mem_zpowers _
      obtain ⟨y, hy, he⟩ := hm
      exact (Subtype.ext he : y = x) ▸ hy

private theorem noncentral_involution (h : Hypotheses z)
    (x : Core z) (hx : x ^ 2 = 1) (hxZ : x ∉ center (Core z)) :
    orderOf ((x : Centralizer z) : G) = 2 ∧ ((x : Centralizer z) : G) ≠ z := by
  have hn := not_or.mp (mt (core_center_mem_iff h x).mpr hxZ)
  exact ⟨orderOf_eq_prime (congrArg (fun x : Core z => ((x : Centralizer z) : G)) hx)
    hn.1, hn.2⟩

public theorem mem_countCandidates_iff_cosetOrbit_card (h : Hypotheses z)
    (hp : CosetProfile z) (x : Core z) (hx : x ^ 2 = 1) (hxZ : x ∉ center (Core z)) :
    ((x : Centralizer z) : G) ∈ countCandidates z ↔
      (cosetOrbit z (centralInvolutionCoset x hx hxZ)).ncard = 3 := by
  have hi := noncentral_involution h x hx hxZ
  have hm : ((x : Centralizer z) : G) ∈ coreInG z := ⟨x, x.property, rfl⟩
  have hc := elementOrbit_card_mul_centralizer h x
  rw [elementOrbit_card h x hx hxZ] at hc
  obtain ⟨S, hS, hs, ho⟩ := hp
  have horbit : (cosetOrbit z (centralInvolutionCoset x hx hxZ)).ncard = 3 ∨
      (cosetOrbit z (centralInvolutionCoset x hx hxZ)).ncard = 6 := by
    by_cases hv : centralInvolutionCoset x hx hxZ ∈ S
    · exact Or.inl ((congrArg Set.ncard (hs _ hv)).trans hS)
    · exact Or.inr (ho _ hv)
  constructor
  · intro hmem
    rcases horbit with he | he
    · exact he
    · rw [he] at hc
      have hbound := hmem.2.2.2
      omega
  · intro he
    refine ⟨hm, hi.1, hi.2, ?_⟩
    rw [he] at hc
    omega

/-- The literal candidate set is the ambient image of the lifts of the short
coset orbit. In particular no ambient fusion premise enters the calculation. -/
public theorem countCandidates_eq_image_liftCosets (h : Hypotheses z)
    (S : Set (CentralInvolutionCosets (Core z))) (hS : S.ncard = 3)
    (hs : ∀ v ∈ S, cosetOrbit z v = S)
    (ho : ∀ v ∉ S, (cosetOrbit z v).ncard = 6) :
    countCandidates z = (fun x : Core z => ((x : Centralizer z) : G)) '' liftCosets z S := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  have hp : CosetProfile z := ⟨S, hS, hs, ho⟩
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := hy.1
    let x : Core z := ⟨a, ha⟩
    have hx : x^2=1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (a : G)^2=1
      rw [← hy.2.1]
      exact pow_orderOf_eq_one _
    have hxZ : x ∉ center (Core z) := by
      rw [core_center_mem_iff h x]
      rintro (h1 | hz)
      · have hc := hy.2.1
        change orderOf ((x : Centralizer z) : G) = 2 at hc
        rw [h1, orderOf_one] at hc
        omega
      · exact hy.2.2.1 hz
    let v := centralInvolutionCoset x hx hxZ
    have hv : v ∈ S := by
      by_contra hn
      have hc := (mem_countCandidates_iff_cosetOrbit_card h hp x hx hxZ).mp hy
      rw [ho v hn] at hc
      omega
    exact ⟨x, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, he⟩, rfl⟩
    have hxZ : x ∉ center (Core z) := by
      intro hh
      exact v.property.1 (he.symm.trans ((QuotientGroup.eq_one_iff x).mpr hh))
    obtain ⟨a, ha, hae⟩ := v.property.2
    have hx : x^2=1 := (d.square_eq_of_quotient_eq x a (he.trans hae.symm)).trans ha
    have hv' : centralInvolutionCoset x hx hxZ = v := Subtype.ext he
    apply (mem_countCandidates_iff_cosetOrbit_card h hp x hx hxZ).mpr
    rw [hv', hs v hv, hS]

public theorem countCandidates_card_of_cosetProfile (h : Hypotheses z)
    (hp : CosetProfile z) : (countCandidates z).ncard = 6 := by
  obtain ⟨S, hS, hs, ho⟩ := hp
  have hf : Function.Injective (fun x : Core z => ((x : Centralizer z) : G)) :=
    fun x y he => Subtype.ext (Subtype.ext he)
  rw [countCandidates_eq_image_liftCosets h S hS hs ho,
    Set.ncard_image_of_injective _ hf, liftCosets_card h, hS]

public theorem countCandidates_transitive_of_cosetProfile (h : Hypotheses z)
    (hp : CosetProfile z) : ∀ x ∈ countCandidates z, ∀ y ∈ countCandidates z,
      ∃ a ∈ Centralizer z, a*x*a⁻¹=y := by
  obtain ⟨S, hS, hs, ho⟩ := hp
  have hmem := countCandidates_eq_image_liftCosets h S hS hs ho
  intro x hx y hy
  rw [hmem] at hx hy
  obtain ⟨xx, ⟨v, hv, he⟩, rfl⟩ := hx
  obtain ⟨yy, ⟨w, hw, he'⟩, rfl⟩ := hy
  obtain ⟨d⟩ := h.quaternionCentralProduct
  have hxxZ : xx ∉ center (Core z) := by
    intro hh
    exact v.property.1 (he.symm.trans ((QuotientGroup.eq_one_iff xx).mpr hh))
  obtain ⟨b, hb, hbe⟩ := v.property.2
  have hxx : xx^2=1 := (d.square_eq_of_quotient_eq xx b (he.trans hbe.symm)).trans hb
  have hcv : centralInvolutionCoset xx hxx hxxZ = v := Subtype.ext he
  have hyy : yy ∈ elementOrbit z xx := by
    rw [elementOrbit_eq_liftCosets h xx hxx hxxZ, hcv, hs v hv]
    exact ⟨w, hw, he'⟩
  obtain ⟨a, ha⟩ := hyy
  refine ⟨a, a.property, ?_⟩
  exact congrArg (fun x : Core z => ((x : Centralizer z) : G)) ha
end FusionCount.LocalOrbit
end CFSG.Quasithin.Extraspecial32
