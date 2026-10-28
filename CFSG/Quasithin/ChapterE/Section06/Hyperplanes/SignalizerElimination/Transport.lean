module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Contracts
public import Theory.GroupTheory.CentralTwoQuotientOddCore
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.OddActionCentralTwoKernel

/-!
# Transport through the central two-kernel

The quotient in E.6.20 is a literal central two-quotient.  This file records
the transport steps used by the signalizer lift: odd cores map through a
central two-kernel, and the odd core of a quotient centralizer lifts to the
actual centralizer when its projected actor is elementary abelian. The proof
uses the preimage of the quotient centralizer, its relative normality, and
odd action on the central discrepancy; it does not assume that arbitrary
centralizers commute with this quotient.

The obstruction lemmas isolate a necessary condition for the literal
`CompletedLocalOddClosure` contract: odd cores must be antitone throughout
the interval above U₀, including its top V. Hyperplane balance alone does not
supply this top case. The source has the additional vanishing of O(C_G(V))
from E.6.6(2); see `Globalization.lean` (the local
`hVzero` proof) and the diagnostic in `Transport/Source/README.md`. This
module does not assert `HyperplaneBalance → CompletedLocalOddClosure`.

The corrected completion theorem below retains that full-actor vanishing.
It uses a complement to U₀ in V to lift the order-eight actor to a genuine
conjugation action on G. The resulting signalizer values are the original
odd cores, so completion directly proves oddness upstairs. The quotient
balance theorem independently uses only hyperplane balance and transports
fixed points inside the odd cores, using normalization and their trivial
intersection with the two-kernel. Finally, the image and preimage identities
identify Setup's quotient completion and its internal direct product lift.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.20,
printed pp.252--253 (PDF pp.263--264).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination

variable {G : Type*} [Group G] [Finite G]

theorem pPrimeCore_map_eq_of_central_two_quotient
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (f : H →* K) (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center H) (hZtwo : IsPGroup 2 f.ker) :
    (pPrimeCore 2 H).map f = pPrimeCore 2 K := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup H := pPrimeCore 2 H
  let Q : Subgroup K := O.map f
  have hQnormal : Q.Normal := Subgroup.Normal.map (pPrimeCore_normal (p := 2)) f hf
  let _ : Q.Normal := hQnormal
  have hQodd : Nat.Coprime 2 (Nat.card Q) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd O f) pPrimeCore_coprime_card
  have hQle : Q ≤ pPrimeCore 2 K := le_sSup ⟨inferInstance, hQodd⟩
  apply le_antisymm hQle
  let r : H →* (H ⧸ O) := QuotientGroup.mk' O
  let Z : Subgroup (H ⧸ O) := f.ker.map r
  let _ : Z.Normal := Subgroup.Normal.map (inferInstance : f.ker.Normal) r
    (QuotientGroup.mk'_surjective O)
  have hZcenter : Z ≤ Subgroup.center (H ⧸ O) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
    apply congrArg r
    exact mem_center_iff.mp (hZ hz) g
  have hZtwo' : IsPGroup 2 Z := hZtwo.map r
  have hcorequot : pPrimeCore 2 ((H ⧸ O) ⧸ Z) = ⊥ :=
    pPrimeCore_quotient_eq_bot_of_central_two_subgroup Z hZcenter hZtwo'
      (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
  let qQ : K →* (K ⧸ Q) := QuotientGroup.mk' Q
  let t : H →* (K ⧸ Q) := qQ.comp f
  have hOker : O ≤ t.ker := by
    intro o ho
    change qQ (f o) = 1
    apply (QuotientGroup.eq_one_iff (N := Q) (f o)).2
    exact mem_map_of_mem f ho
  let s : (H ⧸ O) →* (K ⧸ Q) := QuotientGroup.lift O t hOker
  have htker : t.ker = O ⊔ f.ker := by
    apply le_antisymm
    · intro g hg
      have hq : f g ∈ Q := (QuotientGroup.eq_one_iff (N := Q) (f g)).1 hg
      obtain ⟨o, ho, he⟩ := Subgroup.mem_map.mp hq
      have hgo : g * o⁻¹ ∈ f.ker := by
        change f (g * o⁻¹) = 1
        calc
          f (g * o⁻¹) = f g * (f o)⁻¹ := by simp
          _ = f o * (f o)⁻¹ := by rw [he]
          _ = 1 := by simp
      have hfac : g = (g * o⁻¹) * o := by simp
      rw [hfac]
      simpa [sup_comm] using (show (g * o⁻¹) * o ∈ f.ker ⊔ O from
        (f.ker ⊔ O).mul_mem
          ((show f.ker ≤ f.ker ⊔ O from le_sup_left) hgo)
          ((show O ≤ f.ker ⊔ O from le_sup_right) ho))
    · intro g hg
      rcases (Subgroup.mem_sup_of_normal_right (s := O) (t := f.ker)).1 hg with
        ⟨o, ho, z, hz, rfl⟩
      apply (QuotientGroup.eq_one_iff (N := Q) (f (o * z))).2
      rw [map_mul]
      exact Q.mul_mem (mem_map_of_mem f ho)
        (by rw [show f z = 1 from hz]; exact Q.one_mem)
  have hsker : s.ker = Z := by
    rw [show s = QuotientGroup.lift O t hOker by rfl, QuotientGroup.ker_lift, htker]
    rw [Subgroup.map_sup]
    rw [show Subgroup.map (QuotientGroup.mk' O) O = ⊥ by
      exact QuotientGroup.map_mk'_self O]
    simp only [bot_sup_eq]
    rfl
  have htsurj : Function.Surjective t := (QuotientGroup.mk'_surjective Q).comp hf
  have hssurj : Function.Surjective s :=
    QuotientGroup.lift_surjective_of_surjective O t htsurj hOker
  let e : ((H ⧸ O) ⧸ Z) ≃* (K ⧸ Q) :=
    (QuotientGroup.quotientMulEquivOfEq hsker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective s hssurj)
  have hcoreKquot : pPrimeCore 2 (K ⧸ Q) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e, hcorequot, Subgroup.map_bot]
  have hcomap := pPrimeCore_comap_eq_of_surjective_coprime 2 qQ
    (QuotientGroup.mk'_surjective Q)
    (by rw [QuotientGroup.ker_mk']; exact hQodd)
  rw [hcoreKquot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hcomap
  exact hcomap.symm.le

theorem odd_core_centralizes_of_central_two_discrepancy
    {H : Type*} [Group H] [Finite H]
    (Z A D : Subgroup H) (_hZA : Z ≤ A) (hZc : Z ≤ Subgroup.center H)
    [IsElementaryAbelian 2 A]
    (hDnorm : D ≤ normalizer (A : Set H))
    (hdisc : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ * a⁻¹ ∈ Z) :
    (pPrimeCore 2 D).map D.subtype ≤ centralizer (A : Set H) := by
  let E : Subgroup D := pPrimeCore 2 D
  let incD : E →* H := D.subtype.comp E.subtype
  have hEN : ∀ e : E, (D.subtype e : H) ∈ normalizer (A : Set H) := by
    intro e
    exact hDnorm e.val.property
  let incN : E →* normalizer (A : Set H) :=
    incD.codRestrict _ hEN
  let f : E →* MulAut A := A.normalizerMonoidHom.comp incN
  let _ : MulDistribMulAction E A := MulDistribMulAction.compHom A f
  let N : Subgroup A := Z.subgroupOf A
  have hNc : N ≤ Subgroup.center A := by
    intro z hz
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact mem_center_iff.mp (hZc (show (z : H) ∈ Z from hz)) a
  have hNtwo : IsPGroup 2 N :=
    (IsElementaryAbelian.isPGroup 2 A).to_subgroup N
  have hfix : ∀ e : E, ∀ x ∈ N, e • x = x := by
    intro e x hx
    apply Subtype.ext
    change (incD e) * (x : H) * (incD e)⁻¹ = (x : H)
    have hxZ : (x : H) ∈ Z := hx
    calc
      incD e * (x : H) * (incD e)⁻¹ = (x : H) * incD e * (incD e)⁻¹ := by
        rw [show incD e * (x : H) = (x : H) * incD e from
          mem_center_iff.mp (hZc hxZ) (incD e)]
      _ = (x : H) := by simp
  have hquot : ∀ e : E, ∀ a : A, (e • a) * a⁻¹ ∈ N := by
    intro e a
    change ((e • a : A) : H) * (a : H)⁻¹ ∈ Z
    exact hdisc (incD e) e.val.property (a : H) a.property
  have hodd : Odd (Nat.card E) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hfixed : ∀ e : E, ∀ a : A, e • a = a := by
    intro e a
    exact MulDistribMulAction.fixed_of_odd_of_central_two_discrepancy hodd N hNc hNtwo hfix a
      (fun e' => hquot e' a) e
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  let eE : E := ⟨e, he⟩
  change (incD eE) ∈ centralizer (A : Set H)
  intro a ha
  have hxe : eE • (⟨a, ha⟩ : A) = ⟨a, ha⟩ := hfixed eE ⟨a, ha⟩
  have hc := congrArg Subtype.val hxe
  change (incD eE) * (a : H) * (incD eE)⁻¹ = (a : H) at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

theorem oddCentralizer_map_central_two_quotient
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (f : H →* K) (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center H) (hZtwo : IsPGroup 2 f.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hkerA : f.ker ≤ A) :
    ((pPrimeCore 2 (centralizer (A : Set H))).map (centralizer (A : Set H)).subtype).map f =
      (pPrimeCore 2 (centralizer (A.map f : Set K))).map (centralizer (A.map f : Set K)).subtype := by
  let C : Subgroup H := centralizer (A : Set H)
  let Cq : Subgroup K := centralizer (A.map f : Set K)
  let D : Subgroup H := Cq.comap f
  have hCD : C ≤ D := by
    intro x hx
    change f x ∈ Cq
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    simpa only [map_mul, map_inv] using congrArg f (mem_centralizer_iff.mp hx a ha)
  have hDnormA : D ≤ normalizer (A : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx a ha
    have hxa : f (x * a * x⁻¹) = f a := by
      rw [map_mul, map_mul, map_inv]
      have hc := mem_centralizer_iff.mp hx (f a) (mem_map_of_mem f ha)
      calc
        f x * f a * (f x)⁻¹ = f a * f x * (f x)⁻¹ := by rw [← hc]
        _ = f a := by simp
    have hd : x * a * x⁻¹ * a⁻¹ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      calc
        f (x * a * x⁻¹ * a⁻¹) = f (x * a * x⁻¹) * f a⁻¹ := by rw [map_mul]
        _ = f a * f a⁻¹ := by rw [hxa]
        _ = 1 := by simp
    have hda : x * a * x⁻¹ * a⁻¹ ∈ A := hkerA hd
    have hm := A.mul_mem hda ha
    simpa [mul_assoc] using hm
  have hkerD : f.ker ≤ D := by
    intro x hx
    change f x ∈ Cq
    rw [MonoidHom.mem_ker.mp hx]
    exact Cq.one_mem
  let qD : D →* Cq := (f.comp D.subtype).codRestrict Cq (by
    intro d y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact (mem_centralizer_iff.mp d.property) (f a) (mem_map_of_mem f ha))
  have hqDsurj : Function.Surjective qD := by
    intro y
    obtain ⟨x, hx⟩ := hf y.val
    have hxd : x ∈ D := by
      change f x ∈ Cq
      exact by simpa only [hx] using y.property
    refine ⟨⟨x, hxd⟩, ?_⟩
    exact Subtype.ext hx
  have hqDker : qD.ker = f.ker.subgroupOf D := by
    ext x
    constructor
    · intro hx
      have hx' : qD x = 1 := hx
      have hx'' : f (x : H) = 1 := congrArg Subtype.val hx'
      exact (MonoidHom.mem_ker.mp hx'')
    · intro hx
      apply Subtype.ext
      apply MonoidHom.mem_ker.mpr
      exact hx
  have hqDcenter : qD.ker ≤ Subgroup.center D := by
    intro x hx
    have hx' : x ∈ f.ker.subgroupOf D := hqDker ▸ hx
    have hxk : (x : H) ∈ f.ker := (Subgroup.mem_subgroupOf.mp hx')
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hZ hxk) (y : H)
  have hqDtwo : IsPGroup 2 qD.ker := by
    rw [hqDker]
    exact hZtwo.of_equiv (Subgroup.subgroupOfEquivOfLe (G := H) hkerD).symm
  have hmapD : (pPrimeCore 2 D).map qD = pPrimeCore 2 Cq := by
    exact pPrimeCore_map_eq_of_central_two_quotient qD hqDsurj hqDcenter hqDtwo
  let PCH : Subgroup H := (pPrimeCore 2 C).map C.subtype
  let PDH : Subgroup H := (pPrimeCore 2 D).map D.subtype
  have hDnormPCH : D ≤ normalizer (PCH : Set H) := by
    exact (show D ≤ normalizer (C : Set H) from hDnormA.trans
      (normalizer_le_normalizer_centralizer A)).trans
      (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C))
  have hPCHleD : PCH ≤ D := (map_subtype_le (pPrimeCore 2 C)).trans hCD
  let PCD : Subgroup D := PCH.subgroupOf D
  have hPCDnormal : PCD.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPCHleD).2 hDnormPCH
  have hPCDodd : Nat.Coprime 2 (Nat.card PCD) := by
    have hcard : Nat.card PCD = Nat.card (pPrimeCore 2 C) := by
      calc
        Nat.card PCD = Nat.card PCH :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPCHleD).toEquiv
        _ = Nat.card (pPrimeCore 2 C) :=
          Subgroup.card_map_of_injective C.subtype_injective
    rw [hcard]
    exact pPrimeCore_coprime_card
  have hPCDle : PCD ≤ pPrimeCore 2 D := le_sSup ⟨hPCDnormal, hPCDodd⟩
  have hPCHlePDH : PCH ≤ PDH := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPCHleD]
    exact Subgroup.map_mono hPCDle
  have hPDC : PDH ≤ C := by
    exact odd_core_centralizes_of_central_two_discrepancy f.ker A D hkerA hZ hDnormA
      (by
        intro d hd a ha
        apply MonoidHom.mem_ker.mpr
        calc
          f (d * a * d⁻¹ * a⁻¹) = f d * f a * (f d)⁻¹ * (f a)⁻¹ := by simp
          _ = 1 := by
            have hc := mem_centralizer_iff.mp hd (f a) (mem_map_of_mem f ha)
            rw [← hc]
            simp [mul_assoc])
  have hCnormPDH : C ≤ normalizer (PDH : Set H) := by
    exact hCD.trans (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pPrimeCore 2 D)))
  let PDC : Subgroup C := PDH.subgroupOf C
  have hPDCnormal : PDC.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPDC).2 hCnormPDH
  have hPDCodd : Nat.Coprime 2 (Nat.card PDC) := by
    have hcard : Nat.card PDC = Nat.card (pPrimeCore 2 D) := by
      calc
        Nat.card PDC = Nat.card PDH :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPDC).toEquiv
        _ = Nat.card (pPrimeCore 2 D) :=
          Subgroup.card_map_of_injective D.subtype_injective
    rw [hcard]
    exact pPrimeCore_coprime_card
  have hPDCle : PDC ≤ pPrimeCore 2 C := le_sSup ⟨hPDCnormal, hPDCodd⟩
  have hPDHlePCH : PDH ≤ PCH := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPDC]
    exact Subgroup.map_mono hPDCle
  have hPCeq : PCH = PDH := le_antisymm hPCHlePDH hPDHlePCH
  change PCH.map f = (pPrimeCore 2 Cq).map Cq.subtype
  rw [hPCeq]
  change ((pPrimeCore 2 D).map D.subtype).map f = (pPrimeCore 2 Cq).map Cq.subtype
  rw [Subgroup.map_map]
  rw [show f.comp D.subtype = Cq.subtype.comp qD by rfl]
  rw [← hmapD, Subgroup.map_map]

omit [Finite G] in
theorem pPrimeCore_centralizer_subgroupOf_eq {A H : Subgroup G} (hAH : A ≤ H) (hCA : centralizer (A : Set G) ≤ H) :
    ((pPrimeCore 2 (centralizer ((A.subgroupOf H : Subgroup H) : Set H))).map
      ((centralizer ((A.subgroupOf H : Subgroup H) : Set H)).subtype)).map H.subtype =
      (pPrimeCore 2 (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype := by
  let CH : Subgroup H := centralizer ((A.subgroupOf H : Subgroup H) : Set H)
  let CG : Subgroup G := centralizer (A : Set G)
  let f : CH →* CG := (H.subtype.comp CH.subtype).codRestrict CG (by
    intro d y hy
    let yH : H := ⟨y, hAH hy⟩
    have hyH : yH ∈ A.subgroupOf H := hy
    exact congrArg H.subtype (mem_centralizer_iff.mp d.property yH hyH))
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : CG => (z : G)) h
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨⟨(x : G), hCA x.property⟩, ?_⟩, ?_⟩
    · intro a ha
      apply Subtype.ext
      exact mem_centralizer_iff.mp x.property a ha
    · apply Subtype.ext
      rfl
  let e : CH ≃* CG := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have heq : H.subtype.comp CH.subtype = CG.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  dsimp [CH, CG, f] at heq ⊢
  rw [Subgroup.map_map]
  rw [heq, ← Subgroup.map_map]
  have hm := congrArg (Subgroup.map CG.subtype) (pPrimeCore_map_iso 2 e)
  simpa using hm


omit [Finite G] in
/-- Exact recovery for every displayed subspace forces odd-core containment
also at the full actor, which is absent from the hyperplane-balance premise. -/
theorem completedLocalOddClosure_oddCentralizer_le
    {V U₀ A B : Subgroup G} (hcpl : CompletedLocalOddClosure V)
    (hUV : U₀ ≤ V) (hc : subgroupCorank V U₀ = 3)
    (hUA : U₀ < A) (hAB : A ≤ B) (hBV : B ≤ V) :
    oddCentralizer B ≤ oddCentralizer A := by
  rw [← (hcpl U₀ hUV hc).2 A hUA (hAB.trans hBV)]
  exact le_inf (oddCentralizer_le_localOddClosure (hUA.trans_le hAB) hBV)
    ((oddCentralizer_le B).trans (Subgroup.centralizer_le hAB))

omit [Finite G] in
/-- A nonzero full-actor odd core obstructs the stated completion whenever
one subspace above U₀ has trivial odd core. -/
theorem not_completedLocalOddClosure_of_full_actor_core
    {V U₀ A : Subgroup G} (hUV : U₀ ≤ V) (hc : subgroupCorank V U₀ = 3)
    (hUA : U₀ < A) (hAV : A ≤ V)
    (hA : oddCentralizer A = ⊥) (hV : oddCentralizer V ≠ ⊥) :
    ¬ CompletedLocalOddClosure V := by
  intro hcpl
  have h := completedLocalOddClosure_oddCentralizer_le hcpl hUV hc hUA hAV le_rfl
  rw [hA] at h
  exact hV (le_bot_iff.mp h)

variable {V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem index_pow (A : Subgroup G) :
    A.relIndex V = 2 ^ subgroupCorank V A := by
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank V A

private theorem complement_plane {A W : Subgroup G}
    (hAW : A ≤ W) (hW : IsHyperplane V W) (hA : subgroupCorank V A = 2) :
    ∃ W₀ : Subgroup G, IsHyperplane V W₀ ∧ W ⊓ W₀ = A := by
  let : ComplementedLattice (Subgroup V) :=
    ⟨IsElementaryAbelian.exists_isCompl 2 V⟩
  obtain ⟨D, hi, hs⟩ := IsModularLattice.exists_inf_eq_and_sup_eq
    (show A.subgroupOf V ≤ W.subgroupOf V from comap_mono hAW) le_top
  let W₀ := D.map V.subtype
  have hWV : W₀ ≤ V := map_subtype_le _
  have hi' : W ⊓ W₀ = A := by
    have he := congrArg (Subgroup.map V.subtype) hi
    simpa only [map_inf _ _ _ V.subtype_injective,
      map_subgroupOf_eq_of_le hW.1, map_subgroupOf_eq_of_le (hAW.trans hW.1)] using he
  have hDindex : D.index = 2 := by
    have he := relIndex_inf_mul_relIndex (W.subgroupOf V) D (⊤ : Subgroup V)
    rw [inf_top_eq, relIndex_top_right, relIndex_top_right, hi] at he
    have hr : (W.subgroupOf V).relIndex D = 2 := by
      rw [← relIndex_sup_right, sup_comm, hs, relIndex_top_right]
      change W.relIndex V = 2
      rw [index_pow, hW.2, pow_one]
    rw [hr] at he
    change 2 * D.index = A.relIndex V at he
    rw [index_pow, hA] at he
    omega
  refine ⟨W₀, ⟨hWV, ?_⟩, hi'⟩
  have hr : W₀.relIndex V = D.index := by
    simp only [W₀, relIndex, subgroupOf, comap_map_eq, V.ker_subtype, sup_bot_eq]
  rw [subgroupCorank, hr, hDindex]
  decide

private theorem core_plane_le_line (hbal : HyperplaneBalance V) {A W : Subgroup G}
    (hAW : A ≤ W) (hW : IsHyperplane V W) (hA : subgroupCorank V A = 2) :
    oddCentralizer W ≤ oddCentralizer A := by
  obtain ⟨W₀, hW₀, he⟩ := complement_plane hAW hW hA
  simpa only [he] using hbal W W₀ hW hW₀

section Actor
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- The actual inverse image of an actor subspace, embedded back into G. -/
private def liftSpace (q : V →* E) (B : Subgroup E) : Subgroup G :=
  (B.comap q).map V.subtype

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_le (q : V →* E) (B : Subgroup E) : liftSpace q B ≤ V :=
  map_subtype_le _

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_mono (q : V →* E) : Monotone (liftSpace q) :=
  fun _ _ h => map_mono (comap_mono h)

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_sup (q : V →* E) (hq : Function.Surjective q) (A B : Subgroup E) :
    liftSpace q (A ⊔ B) = liftSpace q A ⊔ liftSpace q B := by
  simp only [liftSpace, ← comap_sup_eq _ _ _ hq, Subgroup.map_sup]

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_top (q : V →* E) : liftSpace q ⊤ = V := by
  apply le_antisymm (liftSpace_le q ⊤)
  exact fun x hx => ⟨⟨x, hx⟩, mem_top _, rfl⟩

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_index (q : V →* E) (hq : Function.Surjective q) (B : Subgroup E) :
    (liftSpace q B).relIndex V = B.index := by
  simp only [liftSpace, relIndex, subgroupOf, comap_map_eq, V.ker_subtype, sup_bot_eq]
  exact B.index_comap_of_surjective hq

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_strictMono (q : V →* E) (hq : Function.Surjective q) :
    StrictMono (liftSpace q) := by
  intro A B hAB
  refine lt_of_le_of_ne (liftSpace_mono q hAB.le) ?_
  intro he
  have hc := Subgroup.map_injective V.subtype_injective he
  have he' := congrArg (Subgroup.map q) hc
  simp only [map_comap_eq_self_of_surjective hq] at he'
  exact hAB.ne he'

omit [Finite E] in
private theorem line_order (a : E) (ha : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) a) ha

private theorem line_mem (a x : E) (ha : a ≠ 1) : x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [(isOfFinOrder_of_finite a).mem_zpowers_iff_mem_range_orderOf, line_order a ha]
  simp [show Finset.range 2 = {0, 1} by decide, eq_comm]

omit [Finite E] in
private theorem line_index (hE : Nat.card E = 8) (a : E) (ha : a ≠ 1) :
    (zpowers a).index = 4 := by
  have hm := (zpowers a).index_mul_card
  rw [Nat.card_zpowers, line_order a ha, hE] at hm
  omega

private theorem lines_sup_index (hE : Nat.card E = 8) (a b : E)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    (zpowers a ⊔ zpowers b).index = 2 := by
  have hi : zpowers a ⊓ zpowers b = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rcases (line_mem a x ha).mp hx.1 with hx1 | hxa
    · exact hx1
    · rw [hxa] at hx
      rcases (line_mem b a hb).mp hx.2 with he | he
      · exact (ha he).elim
      · exact (hab he).elim
  have hr : (zpowers a).relIndex (zpowers a ⊔ zpowers b) = 2 := by
    rw [relIndex_sup_left, ← inf_relIndex_right, hi, relIndex_bot_left,
      Nat.card_zpowers, line_order b hb]
  have hm := relIndex_mul_index (show zpowers a ≤ zpowers a ⊔ zpowers b from le_sup_left)
  rw [hr, line_index hE a ha] at hm
  omega

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] in
private theorem lift_line_corank (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (a : E) (ha : a ≠ 1) :
    subgroupCorank V (liftSpace q (zpowers a)) = 2 := by
  rw [subgroupCorank, liftSpace_index q hq, line_index hE a ha]
  decide

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem lift_plane_hyperplane (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (a b : E) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    IsHyperplane V (liftSpace q (zpowers a ⊔ zpowers b)) := by
  refine ⟨liftSpace_le q _, ?_⟩
  rw [subgroupCorank, liftSpace_index q hq, lines_sup_index hE a b ha hb hab]
  decide

private theorem lift_lines_balance (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (hbal : HyperplaneBalance V)
    (a b : E) (ha : a ≠ 1) (hb : b ≠ 1) :
    oddCentralizer (liftSpace q (zpowers a)) ⊓
      centralizer (liftSpace q (zpowers b) : Set G) ≤
        oddCentralizer (liftSpace q (zpowers b)) := by
  by_cases hab : a = b
  · subst b
    exact inf_le_left
  have hW := lift_plane_hyperplane q hq hE a b ha hb hab
  have hcore := core_plane_le_line hbal
    (liftSpace_mono q (show zpowers b ≤ zpowers a ⊔ zpowers b from le_sup_right))
    hW (lift_line_corank q hq hE b hb)
  apply le_trans _ hcore
  apply le_trans _ (oddCentralizer_inter_le
    (liftSpace_mono q (show zpowers a ≤ zpowers a ⊔ zpowers b from le_sup_left)))
  refine le_inf inf_le_left ?_
  intro x hx y hy
  have hca := oddCentralizer_le _ hx.1
  rw [liftSpace_sup q hq] at hy
  have hle : liftSpace q (zpowers a) ⊔ liftSpace q (zpowers b) ≤
      centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · intro z hz
      exact mem_centralizer_singleton_iff.mpr (hca z hz)
    · intro z hz
      exact mem_centralizer_singleton_iff.mpr (hx.2 z hz)
  exact mem_centralizer_singleton_iff.mp (hle hy)

omit [Finite G] [Finite E] [IsElementaryAbelian 2 E] in
/-- An elementary abelian complement gives a section of the actor quotient.
Its conjugation action upstairs is used only on cores centralizing the kernel. -/
private theorem exists_actor_section (q : V →* E) (hq : Function.Surjective q) :
    ∃ s : E →* V, ∀ a, q (s a) = a := by
  obtain ⟨D, hD⟩ := IsElementaryAbelian.exists_isCompl 2 V q.ker
  let r : D →* E := q.comp D.subtype
  have hrinj : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply le_bot_iff.mp
    intro d hd
    apply Subtype.ext
    exact hD.inf_eq_bot.le ⟨hd, d.property⟩
  have hrsurj : Function.Surjective r := by
    intro a
    obtain ⟨v, rfl⟩ := hq a
    have hv : v ∈ q.ker ⊔ D := hD.sup_eq_top.symm ▸ mem_top v
    obtain ⟨z, hz, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hv
    refine ⟨⟨d, hd⟩, ?_⟩
    change q d = q (z * d)
    rw [map_mul, MonoidHom.mem_ker.mp hz, one_mul]
  let e : D ≃* E := MulEquiv.ofBijective r ⟨hrinj, hrsurj⟩
  exact ⟨D.subtype.comp e.symm.toMonoidHom, fun a => e.apply_symm_apply a⟩

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem liftSpace_section (q : V →* E) (s : E →* V) (hs : ∀ a, q (s a) = a)
    (B : Subgroup E) : liftSpace q B =
      liftSpace q ⊥ ⊔ B.map (V.subtype.comp s) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hz : v * (s (q v))⁻¹ ∈ (⊥ : Subgroup E).comap q := by
      change q (v * (s (q v))⁻¹) = 1
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    have hvfac : (v : G) = ((v * (s (q v))⁻¹ : V) : G) * (s (q v) : G) := by
      simp
    change (v : G) ∈ _
    rw [hvfac]
    exact (liftSpace q ⊥ ⊔ B.map (V.subtype.comp s)).mul_mem
      ((show liftSpace q ⊥ ≤ liftSpace q ⊥ ⊔ B.map (V.subtype.comp s) from le_sup_left)
        ⟨_, hz, rfl⟩) ((show B.map (V.subtype.comp s) ≤
          liftSpace q ⊥ ⊔ B.map (V.subtype.comp s) from le_sup_right) ⟨q v, hv, rfl⟩)
  · refine sup_le (liftSpace_mono q bot_le) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨s a, (by change q (s a) ∈ B; rw [hs]; exact ha), rfl⟩

@[reducible] private def sectionAction (s : E →* V) : MulDistribMulAction E G :=
  MulDistribMulAction.compHom G (MulAut.conj.comp (V.subtype.comp s))

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem section_fixed (s : E →* V) (B : Subgroup E) :
    letI := sectionAction s
    FixedPoints.subgroup B G = centralizer (B.map (V.subtype.comp s) : Set G) := by
  let _ := sectionAction s
  ext x
  constructor
  · intro hx y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact mul_inv_eq_iff_eq_mul.mp (hx (⟨a, ha⟩ : B))
  · intro hx b
    apply mul_inv_eq_iff_eq_mul.mpr
    exact hx _ ⟨b, b.property, rfl⟩

omit [Finite G] [IsElementaryAbelian 2 V] [Finite E] [IsElementaryAbelian 2 E] in
private theorem section_fixed_inter (q : V →* E) (s : E →* V) (hs : ∀ a, q (s a) = a)
    (B : Subgroup E) {R : Subgroup G}
    (hR : R ≤ centralizer (liftSpace q ⊥ : Set G)) :
    letI := sectionAction s
    R ⊓ FixedPoints.subgroup B G = R ⊓ centralizer (liftSpace q B : Set G) := by
  rw [section_fixed, liftSpace_section q s hs B]
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    have hle : liftSpace q ⊥ ⊔ B.map (V.subtype.comp s) ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · exact fun z hz => mem_centralizer_singleton_iff.mpr (hR hx z hz)
      · exact fun z hz => mem_centralizer_singleton_iff.mpr (hc z hz)
    exact fun z hz => mem_centralizer_singleton_iff.mp (hle hz)
  · exact fun hx => ⟨hx.1, (Subgroup.centralizer_le (show B.map (V.subtype.comp s) ≤
      liftSpace q ⊥ ⊔ B.map (V.subtype.comp s) from le_sup_right)) hx.2⟩

private def liftedSignalizer (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (hbal : HyperplaneBalance V)
    (s : E →* V) (hs : ∀ a, q (s a) = a) :
    letI := sectionAction s
    Theory.GroupTheory.TwoSignalizerFamily E G := by
  let _ := sectionAction s
  refine {
    subgroup := fun a => oddCentralizer (liftSpace q (zpowers a.val))
    odd := fun a => oddCentralizer_odd _
    solvable := fun a => odd_order_theorem _ (oddCentralizer_odd _)
    invariant := ?_
    le_fixed := ?_
    balance := ?_ }
  · intro a
    constructor
    intro b x
    apply mem_normalizer_iff.mp
    apply centralizer_le_normalizer_oddCentralizer
    exact (V.le_centralizer.trans (Subgroup.centralizer_le (liftSpace_le q _)))
      (s b).property
  · intro a
    rw [section_fixed]
    apply (oddCentralizer_le _).trans
    apply Subgroup.centralizer_le
    rw [liftSpace_section q s hs]
    exact fun x hx => (show _ ≤ liftSpace q ⊥ ⊔ (zpowers a.val).map (V.subtype.comp s) from le_sup_right) hx
  · intro a b
    rw [section_fixed_inter q s hs (zpowers b.val)
      ((oddCentralizer_le _).trans (Subgroup.centralizer_le (liftSpace_mono q bot_le)))]
    exact lift_lines_balance q hq hE hbal a.val b.val a.property b.property

private theorem lifted_closure_complete (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (hbal : HyperplaneBalance V) :
    let R := ⨆ a : {a : E // a ≠ 1}, oddCentralizer (liftSpace q (zpowers a.val))
    Odd (Nat.card R) ∧ ∀ a : {a : E // a ≠ 1},
      R ⊓ centralizer (liftSpace q (zpowers a.val) : Set G) =
        oddCentralizer (liftSpace q (zpowers a.val)) := by
  obtain ⟨s, hs⟩ := exists_actor_section q hq
  let _ := sectionAction s
  let θ := liftedSignalizer q hq hE hbal s hs
  have hc := Glauberman.solvable_two_signalizer_complete θ (by omega)
  have hR : θ.closure ≤ centralizer (liftSpace q ⊥ : Set G) :=
    iSup_le fun a => (oddCentralizer_le _).trans
      (Subgroup.centralizer_le (liftSpace_mono q bot_le))
  refine ⟨hc.1, fun a => ?_⟩
  have he := hc.fixed_eq a
  rw [section_fixed_inter q s hs _ hR] at he
  exact he

private theorem core_lift_le_line (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (hbal : HyperplaneBalance V) (hzero : oddCentralizer V = ⊥)
    (B : Subgroup E) (a : E) (ha : a ≠ 1) (haB : a ∈ B) :
    oddCentralizer (liftSpace q B) ≤ oddCentralizer (liftSpace q (zpowers a)) := by
  have hLB : zpowers a ≤ B := zpowers_le.mpr haB
  have hidx : B.index ≤ 4 := (index_antitone hLB).trans_eq (line_index hE a ha)
  have hd : B.index ∣ 2 ^ 3 := by simpa only [hE, show 2 ^ 3 = 8 by decide] using B.index_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · have hB : B = ⊤ := index_eq_one.mp he
    rw [hB, liftSpace_top, hzero]
    exact bot_le
  · exact core_plane_le_line hbal (liftSpace_mono q hLB)
      ⟨liftSpace_le q B, by rw [subgroupCorank, liftSpace_index q hq, he]; decide⟩
      (lift_line_corank q hq hE a ha)
  · have hB : zpowers a = B := by
      by_contra hn
      have hlt := index_strictAnti (lt_of_le_of_ne hLB hn)
      rw [line_index hE a ha, he] at hlt
      omega
    rw [hB]
  · norm_num [he] at hidx

private theorem completed_of_actor_map (q : V →* E) (hq : Function.Surjective q)
    (hE : Nat.card E = 8) (hbal : HyperplaneBalance V) (hzero : oddCentralizer V = ⊥)
    (U : Subgroup G) (hU : liftSpace q ⊥ = U) :
    (Odd (Nat.card (localOddClosure V U)) ∧ ∀ A : Subgroup G, U < A → A ≤ V →
      localOddClosure V U ⊓ centralizer (A : Set G) = oddCentralizer A) ∧
    (⨆ a : {a : E // a ≠ 1}, oddCentralizer (liftSpace q (zpowers a.val))) =
      localOddClosure V U := by
  let R := ⨆ a : {a : E // a ≠ 1}, oddCentralizer (liftSpace q (zpowers a.val))
  have hc := lifted_closure_complete q hq hE hbal
  have hline (a : E) (ha : a ≠ 1) : U < liftSpace q (zpowers a) := by
    rw [← hU]
    exact liftSpace_strictMono q hq (bot_lt_iff_ne_bot.mpr (by
      intro he
      exact ha (he.le (mem_zpowers a))))
  have hpre (A : Subgroup G) (hUA : U ≤ A) (hAV : A ≤ V) :
      liftSpace q ((A.subgroupOf V).map q) = A := by
    have hk : q.ker ≤ A.subgroupOf V := by
      intro v hv
      exact hUA (hU ▸ (show (v : G) ∈ liftSpace q ⊥ from ⟨v, hv, rfl⟩))
    rw [liftSpace, comap_map_eq, sup_of_le_left hk, map_subgroupOf_eq_of_le hAV]
  have hex (A : Subgroup G) (hUA : U < A) (hAV : A ≤ V) :
      ∃ a : E, a ≠ 1 ∧ a ∈ (A.subgroupOf V).map q := by
    have hn : (A.subgroupOf V).map q ≠ ⊥ := by
      intro he
      have he' := hpre A hUA.le hAV
      rw [he, hU] at he'
      exact hUA.ne he'
    obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hn
    exact ⟨a, (fun he => ha (Subtype.ext he)), a.property⟩
  have hReq : R = localOddClosure V U := by
    apply le_antisymm
    · exact iSup_le fun a => oddCentralizer_le_localOddClosure (hline a.val a.property)
        (liftSpace_le q _)
    · refine iSup_le fun A => ?_
      obtain ⟨a, ha, haA⟩ := hex A.val A.property.1 A.property.2
      rw [← hpre A.val A.property.1.le A.property.2]
      exact (core_lift_le_line q hq hE hbal hzero _ a ha haA).trans
        (le_iSup (fun b : {b : E // b ≠ 1} => oddCentralizer (liftSpace q (zpowers b.val))) ⟨a, ha⟩)
  refine ⟨⟨hReq ▸ hc.1, fun A hUA hAV => le_antisymm ?_ ?_⟩, hReq⟩
  · obtain ⟨a, ha, haA⟩ := hex A hUA hAV
    have hLA : liftSpace q (zpowers a) ≤ A := by
      rw [← hpre A hUA.le hAV]
      exact liftSpace_mono q (zpowers_le.mpr haA)
    have he := hc.2 ⟨a, ha⟩
    change R ⊓ centralizer (liftSpace q (zpowers a) : Set G) = _ at he
    rw [hReq] at he
    refine le_trans ?_ (oddCentralizer_inter_le hLA)
    exact le_inf (he.le.trans' (inf_le_inf_left _ (Subgroup.centralizer_le hLA))) inf_le_right
  · exact le_inf (oddCentralizer_le_localOddClosure hUA hAV) (oddCentralizer_le A)
end Actor

private def actorMap (U : Subgroup G) (hU : U ≤ V) : V →* quotientActor V U :=
  (quotientActorMap V U hU).codRestrict _ (fun v => by
    rw [← quotientActorMap_range V U hU]
    exact ⟨v, rfl⟩)

omit [Finite G] in
private theorem actorMap_surjective (U : Subgroup G) (hU : U ≤ V) :
    Function.Surjective (actorMap U hU) := by
  intro a
  have ha := a.property
  simp only [← quotientActorMap_range V U hU] at ha
  obtain ⟨v, hv⟩ := ha
  exact ⟨v, Subtype.ext hv⟩

omit [Finite G] in
private theorem actorMap_kernel (U : Subgroup G) (hU : U ≤ V) :
    liftSpace (actorMap U hU) ⊥ = U := by
  have he : (actorMap U hU).ker = U.subgroupOf V := by
    rw [← quotientActorMap_ker V U hU]
    ext v
    exact Subtype.ext_iff
  rw [liftSpace, MonoidHom.comap_bot, he, map_subgroupOf_eq_of_le hU]

/-- The source-usable completion statement, retaining the separately proved
vanishing at the full actor. A section of V → V* lets the solvable signalizer
theorem construct the odd closure upstairs. Hyperplane balance absorbs the
rank-two generators, and the full-actor premise handles rank three. Exact
recovery for every larger subspace follows by restriction from a line. -/
theorem completedLocalOddClosure_of_balance_of_fullActorCore_eq_bot
    (hbal : HyperplaneBalance V) (hzero : oddCentralizer V = ⊥) :
    CompletedLocalOddClosure V := by
  intro U hU hc
  let _ := quotientActor_elementary V U hU
  exact (completed_of_actor_map (actorMap U hU) (actorMap_surjective U hU)
    (quotientActor_card_eight V U hU hc) hbal hzero U (actorMap_kernel U hU)).1

private instance elementary_subgroup {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (D : Subgroup E) : IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem odd_map_fixed {H K : Type*} [Group H] [Finite H] [Group K]
    (f : H →* K) (hker : IsPGroup 2 f.ker) (R B : Subgroup H)
    (hodd : Odd (Nat.card R)) (hn : B ≤ normalizer (R : Set H)) :
    (R ⊓ centralizer (B : Set H)).map f =
      R.map f ⊓ centralizer (B.map f : Set K) := by
  have hd : R ⊓ f.ker = ⊥ := by
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    apply Disjoint.eq_bot
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem f hx.1, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg f (hx.2 b hb)
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro b hb
    have hcomm := hy (f b) (mem_map_of_mem f hb)
    have hcR : b * x * b⁻¹ * x⁻¹ ∈ R :=
      R.mul_mem ((mem_normalizer_iff.mp (hn hb) x).mp hx) (R.inv_mem hx)
    have hcK : b * x * b⁻¹ * x⁻¹ ∈ f.ker := by
      change f (b * x * b⁻¹ * x⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      simp [mul_assoc]
    have he : b * x * b⁻¹ * x⁻¹ = 1 := hd.le ⟨hcR, hcK⟩
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)

omit [Finite G] in
private theorem actor_lift_map (U : Subgroup G) (hU : U ≤ V)
    (B : Subgroup (quotientActor V U)) :
    ((liftSpace (actorMap U hU) B).subgroupOf (centralizer (U : Set G))).map
      (QuotientGroup.mk' (quotientKernel U)) = B.map (quotientActor V U).subtype := by
  let H := centralizer (U : Set G)
  let f := QuotientGroup.mk' (quotientKernel U)
  have hVH : V ≤ H := V.le_centralizer.trans (Subgroup.centralizer_le hU)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv, he⟩ := hx
    refine ⟨actorMap U hU v, hv, ?_⟩
    change f (inclusion hVH v) = f x
    exact congrArg f (Subtype.ext he)
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨v, rfl⟩ := actorMap_surjective U hU a
    refine ⟨inclusion hVH v, ?_, rfl⟩
    exact ⟨v, ha, rfl⟩

private theorem actor_lift_core_map (U : Subgroup G) (hU : U ≤ V)
    (B : Subgroup (quotientActor V U)) :
    ((oddCentralizer (liftSpace (actorMap U hU) B)).subgroupOf
      (centralizer (U : Set G))).map (QuotientGroup.mk' (quotientKernel U)) =
        oddCentralizer (B.map (quotientActor V U).subtype) := by
  let _ := quotientActor_elementary V U hU
  let H := centralizer (U : Set G)
  let A := liftSpace (actorMap U hU) B
  let f := QuotientGroup.mk' (quotientKernel U)
  have hAV : A ≤ V := liftSpace_le _ _
  have hUA : U ≤ A := by
    rw [← actorMap_kernel U hU]
    exact liftSpace_mono _ bot_le
  have hAH : A ≤ H := hAV.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU))
  have hCA : centralizer (A : Set G) ≤ H := Subgroup.centralizer_le hUA
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map V.subtype
  let _ : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have he : oddCentralizer (A.subgroupOf H) = (oddCentralizer A).subgroupOf H := by
    have hm := pPrimeCore_centralizer_subgroupOf_eq hAH hCA
    change (oddCentralizer (A.subgroupOf H)).map H.subtype = oddCentralizer A at hm
    rw [← hm]
    simp only [subgroupOf, comap_map_eq, H.ker_subtype, sup_bot_eq]
  have hfc : f.ker ≤ center H := by
    rw [QuotientGroup.ker_mk']
    exact quotientKernel_le_center U
  have hft : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact quotientKernel_isPGroup V U hU
  have hfA : f.ker ≤ A.subgroupOf H := by
    intro x hx
    have hxU : (x : G) ∈ U := (QuotientGroup.eq_one_iff (N := quotientKernel U) x).mp hx
    exact hUA hxU
  have hm := oddCentralizer_map_central_two_quotient f (QuotientGroup.mk'_surjective _)
    hfc hft (A.subgroupOf H) hfA
  change (oddCentralizer (A.subgroupOf H)).map f =
    oddCentralizer ((A.subgroupOf H).map f) at hm
  rw [he] at hm
  exact hm.trans (congrArg oddCentralizer (actor_lift_map U hU B))

/-- Hyperplane balance transports to the odd cores in the literal centralizer
quotient. Only the restricted odd-core fixed points are lifted. -/
theorem quotientBalance_of_hyperplaneBalance
    (hbal : HyperplaneBalance V) (U : Subgroup G) (hU : U ≤ V)
    (hc : subgroupCorank V U = 3) : QuotientBalance V U := by
  let _ := quotientActor_elementary V U hU
  let H := centralizer (U : Set G)
  let q := actorMap U hU
  let f := QuotientGroup.mk' (quotientKernel U)
  have hqt : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact quotientKernel_isPGroup V U hU
  have hmap (a : quotientActor V U) :
      ((oddCentralizer (liftSpace q (zpowers a))).subgroupOf H).map f = quotientValue V U a := by
    have he := actor_lift_core_map U hU (zpowers a)
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, q, f, H, quotientValue] using he
  have hmapA (a : quotientActor V U) :
      ((liftSpace q (zpowers a)).subgroupOf H).map f = zpowers (a : CentralizerQuotient U) := by
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, q, f, H] using actor_lift_map U hU (zpowers a)
  intro a b
  let A := liftSpace q (zpowers a.val)
  let B := liftSpace q (zpowers b.val)
  let R := (oddCentralizer A).subgroupOf H
  have hBnorm : B.subgroupOf H ≤ normalizer (R : Set H) := by
    apply le_normalizer_iff.mpr
    intro b hb x hx
    have hbV : (b : G) ∈ V := liftSpace_le q _ hb
    have hbC : (b : G) ∈ centralizer (A : Set G) :=
      (V.le_centralizer.trans (Subgroup.centralizer_le (liftSpace_le q _))) hbV
    exact (mem_normalizer_iff.mp (centralizer_le_normalizer_oddCentralizer A hbC) (x : G)).mp hx
  have hodd : Odd (Nat.card R) := Nat.coprime_two_left.mp
    ((oddCentralizer_odd A).coprime_two_left.of_dvd_right
      (card_comap_dvd_of_injective (oddCentralizer A) H.subtype H.subtype_injective))
  rw [← hmap a.val, ← hmapA b.val, ← odd_map_fixed f hqt R (B.subgroupOf H) hodd hBnorm,
    ← hmap b.val]
  apply map_mono
  intro x hx
  apply lift_lines_balance q (actorMap_surjective U hU)
    (quotientActor_card_eight V U hU hc) hbal a.val b.val a.property b.property
  refine ⟨hx.1, ?_⟩
  intro b hb
  have hBH : B ≤ H := (liftSpace_le q _).trans
    (V.le_centralizer.trans (Subgroup.centralizer_le hU))
  exact congrArg H.subtype (hx.2 (⟨b, hBH hb⟩ : H) hb)

/-- The actual full closure maps onto Setup's completion. Its preimage is
the product of the central two-kernel and that odd closure, with trivial
intersection. -/
theorem localOddClosure_quotient_image_and_preimage
    (hbal : HyperplaneBalance V) (hzero : oddCentralizer V = ⊥)
    (U : Subgroup G) (hU : U ≤ V) (hc : subgroupCorank V U = 3) :
    let H := centralizer (U : Set G)
    let f := QuotientGroup.mk' (quotientKernel U)
    let X := (localOddClosure V U).subgroupOf H
    X.map f = quotientClosure V U ∧
      (quotientClosure V U).comap f = quotientKernel U ⊔ X ∧
      Disjoint (quotientKernel U) X := by
  let _ := quotientActor_elementary V U hU
  let H := centralizer (U : Set G)
  let f := QuotientGroup.mk' (quotientKernel U)
  let X := (localOddClosure V U).subgroupOf H
  let S := fun a : {a : quotientActor V U // a ≠ 1} =>
    oddCentralizer (liftSpace (actorMap U hU) (zpowers a.val))
  have hgen := (completed_of_actor_map (actorMap U hU) (actorMap_surjective U hU)
    (quotientActor_card_eight V U hU hc) hbal hzero U (actorMap_kernel U hU)).2
  have hS (a : {a : quotientActor V U // a ≠ 1}) : S a ≤ H := by
    apply (oddCentralizer_le _).trans
    apply Subgroup.centralizer_le
    exact (actorMap_kernel U hU).ge.trans (liftSpace_mono _ bot_le)
  have hX : X = ⨆ a, (S a).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (localOddClosure_le V U), Subgroup.map_iSup]
    simp only [map_subgroupOf_eq_of_le (hS _)]
    exact hgen.symm
  have himg : X.map f = quotientClosure V U := by
    rw [hX, Subgroup.map_iSup]
    apply congrArg iSup
    funext a
    exact (actor_lift_core_map U hU (zpowers a.val)).trans
      (congrArg oddCentralizer (MonoidHom.map_zpowers _ _))
  refine ⟨himg, ?_, ?_⟩
  · rw [← himg, comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  · have hodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
      (((completedLocalOddClosure_of_balance_of_fullActorCore_eq_bot hbal hzero U hU hc).1).coprime_two_left.of_dvd_right
          (card_comap_dvd_of_injective (localOddClosure V U) H.subtype H.subtype_injective))
    obtain ⟨n, hn⟩ := (quotientKernel_isPGroup V U hU).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hodd.coprime_two_left.pow_left n


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
