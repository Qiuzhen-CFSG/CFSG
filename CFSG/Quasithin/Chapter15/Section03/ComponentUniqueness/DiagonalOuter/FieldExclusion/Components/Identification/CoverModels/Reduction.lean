module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.Quasithin.Rank

/-!
# The actual two-core quotient in the field-cover argument

The selected component is quasisimple. Its two-core is central, its quotient
is again quasisimple and SQTK, and its simple central quotient is unchanged.
Thus the universal A.3.6 theorem applies to the whole two-core quotient and
its nonquasisimple alternatives are impossible. The odd center embeds in
the quotient center: an element in the kernel has both odd and two-power
order. Consequently its order is coprime to three, or exactly three with
the full A.3.6 three-cover catalogue still retained.

These are reductions, not the selection of the two special-linear covers.
The universal A.3.6 premise is an earlier source theorem, not an assumed
specialized field-cover conclusion.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, A.3.6,
printed pp.43--45; A.3.18, pp.51--52; proof of 15.3.38, p.1137.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.CoverModels
universe u
variable {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
noncomputable def twoCoreCover : PerfectCentralCovering.Cover X (X ⧸ pCore 2 X) where
  toMonoidHom := QuotientGroup.mk' _
  surjective := QuotientGroup.mk'_surjective _
  isPerfect := inferInstance
  ker_le_center := by
    rw [QuotientGroup.ker_mk']
    exact IsQuasisimple.pCore_le_center 2

theorem twoCoreQuasisimple : IsQuasisimple (X ⧸ pCore 2 X) := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  have hne : pCore 2 X ≠ ⊤ := by
    intro h
    have hc : center X = ⊤ := top_unique (h ▸ IsQuasisimple.pCore_le_center (G := X) 2)
    exact Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp hc)
  let : Nontrivial (X ⧸ pCore 2 X) := QuotientGroup.nontrivial_iff.mpr hne
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

private theorem not_fitting_eq_generalized : generalizedFitting X ≠ fittingSubgroup X := by
  intro h
  have ht : generalizedFitting X = ⊤ := top_unique
    (component_le_generalizedFitting X ⊤
      ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩)
  have hf : fittingSubgroup X = ⊤ := h.symm.trans ht
  let : Group.IsNilpotent (⊤ : Subgroup X) := hf ▸ inferInstance
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom) Subgroup.topEquiv.surjective
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  exact Group.IsPerfect.not_isSolvable X inferInstance

noncomputable def oddCenterMap : pPrimeCore 2 (center X) →* center (X ⧸ pCore 2 X) :=
  (((QuotientGroup.mk' (pCore 2 X)).comp (center X).subtype).comp
    (pPrimeCore 2 (center X)).subtype).codRestrict _ (by
      intro z
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) y
      exact (map_mul _ _ _).symm.trans
        ((congrArg (QuotientGroup.mk' _) (mem_center_iff.mp z.val.property y)).trans
          (map_mul _ _ _)))

omit [IsQuasisimple X] in
theorem oddCenterMap_injective : Function.Injective (oddCenterMap (X := X)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  have hx : ((z : center X) : X) ∈ pCore 2 X :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hz)
  have hzord : Nat.Coprime 2 (orderOf z) :=
    (pPrimeCore_coprime_card (p := 2) (G := center X)).of_dvd_right (orderOf_dvd_natCard z)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := X))
  have hdiv : orderOf z ∣ 2 ^ n := by
    rw [← hn]
    have h := orderOf_dvd_natCard (⟨((z : center X) : X), hx⟩ : pCore 2 X)
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe] using h
  have hord : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (hzord.symm.pow_right n) dvd_rfl hdiv
  exact (orderOf_eq_one_iff.mp hord : z = 1)

variable {Y : Type*} [Group Y]
noncomputable def quotientCenterCongr (e : X ≃* Y) :
    (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e).symm ⟨y, hy⟩ |>.property, e.apply_symm_apply y⟩)

open CFSG.Quasithin.Chapter1.Section02
open LocalModels

theorem threeCoverModel_transport {Z : Type*} [Group Z] (e : Y ≃* Z)
    (h : ThreeCoverModel Y) : ThreeCoverModel Z := by
  have hsl (n q : ℕ) (h : IsSL Y n q) : IsSL Z n q := by
    obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := h
    exact ⟨F, hF, hfin, hc, ⟨e.symm.trans f⟩⟩
  have hsu (n q : ℕ) (h : IsSU Y n q) : IsSU Z n q := by
    obtain ⟨F, hF, hfin, J, hc, hj, ⟨f⟩⟩ := h
    exact ⟨F, hF, hfin, J, hc, hj, ⟨e.symm.trans f⟩⟩
  have hthree (S : Type) [Group S] (h : IsThreeCover Y S) : IsThreeCover Z S := by
    let := h.1
    exact ⟨IsQuasisimple.of_mulEquiv e,
      h.2.1.map (fun f => (centerCongr e).symm.trans f),
      h.2.2.map (fun f => (quotientCenterCongr e).symm.trans f)⟩
  cases h with
  | classical b q hq hi =>
      exact .classical b q hq (by cases b <;> [exact hsl _ _ hi; exact hsu _ _ hi])
  | alternating_six hi => exact .alternating_six (hthree _ hi)
  | alternating_seven hi => exact .alternating_seven (hthree _ hi)
  | mathieu hi => exact .mathieu (hthree _ hi)

omit [Finite X] in
private theorem simple_center_card_one [IsSimpleGroup X] : Nat.card (center X) = 1 := by
  let : Nontrivial X := inferInstance
  have hc : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim
  rw [hc, Subgroup.card_bot]

variable {G : Type u} [Group G] [Finite G] {H K : Subgroup G} {v : G}

theorem twoCore_sqtk (d : Input H K v) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
  refine ⟨?_, d.component_sqtk.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (d.component_sqtk.stronglyQuasithin p hp ho)

theorem twoCore_alternatives (d : Input H K v)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B) :
    Nat.card (center (K ⧸ pCore 2 K)) = 1 ∨
      (Nat.card (center (K ⧸ pCore 2 K)) = 3 ∧ ThreeCoverModel (K ⧸ pCore 2 K)) := by
  let := d.quasisimple
  let Q := K ⧸ pCore 2 K
  let : IsQuasisimple Q := twoCoreQuasisimple
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hc : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top, inferInstance⟩).isCComponent
  have ha := (hA36 Q (twoCore_sqtk d) (pCore_quotient_pCore_eq_bot 2) ⊤ hc).1
  have hz := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv
  cases ha with
  | simple _ hs _ =>
      let := hs
      exact Or.inl (hz.symm.trans simple_center_card_one)
  | cover _ hcenter hm =>
      obtain ⟨e⟩ := hcenter
      right
      refine ⟨?_, threeCoverModel_transport topEquiv hm⟩
      exact hz.symm.trans ((Nat.card_congr e.toEquiv).trans (by simp))
  | natural hn => exact (not_fitting_eq_generalized hn.1).elim
  | nilpotent hn => exact (not_fitting_eq_generalized hn.1).elim

theorem oddCenter_alternatives (d : Input H K v)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B) :
    Nat.Coprime 3 (Nat.card (oddCenterIn K)) ∨
      (Nat.card (oddCenterIn K) = 3 ∧ ThreeCoverModel (K ⧸ pCore 2 K)) := by
  let := d.quasisimple
  by_cases h : Nat.Coprime 3 (Nat.card (oddCenterIn K))
  · exact Or.inl h
  right
  have hd : Nat.card (oddCenterIn K) ∣ Nat.card (center (K ⧸ pCore 2 K)) := by
    rw [card_oddCenterIn]
    exact card_dvd_of_injective (oddCenterMap (X := K)) oddCenterMap_injective
  have h3 : 3 ∣ Nat.card (oddCenterIn K) :=
    (Nat.Prime.dvd_iff_not_coprime (by decide : Nat.Prime 3)).mpr h
  rcases twoCore_alternatives d hA36 with hc | ⟨hc, hm⟩
  · have hf : 3 ∣ 1 := hc ▸ h3.trans hd
    norm_num at hf
  · exact ⟨Nat.dvd_antisymm (hc ▸ hd) h3, hm⟩
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.CoverModels
