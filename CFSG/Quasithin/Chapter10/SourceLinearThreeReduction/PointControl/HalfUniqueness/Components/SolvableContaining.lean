module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ContainingQuotients
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ThreeDivisor
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Equality in containing components with solvable proper Sylow overgroups

The prescribed full Sylow in the competing maximal two-local restricts to
an actual full Sylow in each containing component. If every proper Sylow
overgroup of its intrinsic two-core quotient is solvable, this also holds
upstairs. The original nonsolvable local component and that Sylow therefore
generate the containing component; local C-component maximality gives equality.

Apply this to both original factors, keeping the same exchanger and half-join.
Equality for either factor proves distinctness. Equality for both contradicts
the strict containment in the original pair. If either containing quotient
has a cubic divisor, its equality transports that divisor to the original
quotient, and the proved ranked-enlargement contradiction excludes the pair.

SmallContaining supplies the actual model applications. The remaining models,
three-free enlargement, zero-kernel binary-three normalizer and final assembly
remain with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is supplied by
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its final
discharge. No unconditional half-Sylow uniqueness theorem is asserted here.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The literal conjugate equals its containing component; its full Sylow is supplied by the pair. -/
theorem ContainingPair.eq_of_solvable_sylow_quotient
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    (hsol : SolvableSylowOvergroups (K ⧸ pCore 2 K)) :
    L.map (MulAut.conj s).toMonoidHom = K := by
  obtain ⟨S,_,hl⟩ := C.local_sylow_in_containing hs hK hBK
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have hproper : SolvableSylowOvergroups K :=
    isSolvable_proper_sylow_overgroup_of_twoCore_quotient hsol
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups S hl ht le_top
    (SolvableSylowOvergroups.of_equiv topEquiv hproper)
  exact le_antisymm hBK (subgroupOf_eq_top.mp he)

/-- Equality of the first original factor inside H, through its actual intrinsic quotient. -/
theorem ContainingPair.first_eq_of_solvable_sylow_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hsol : SolvableSylowOvergroups (K₁ ⧸ pCore 2 K₁)) : L.subgroupOf H = K₁ := by
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hLK : L ≤ K₁.map H.subtype := by
    have h := map_mono (f := H.subtype) C.first_le
    rwa [map_subgroupOf_eq_of_le C.left_le] at h
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  have h := C.eq_of_solvable_sylow_quotient (one_mem _) ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
    (show L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K₁.map H.subtype by
      simpa only [hid,Subgroup.map_id] using hLK)
    (SolvableSylowOvergroups.of_equiv b hsol)
  rw [hid,Subgroup.map_id] at h
  rw [h,hmap]

/-- Equality of the second original factor, with the same source exchanger. -/
theorem ContainingPair.second_eq_of_solvable_sylow_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hsol : SolvableSylowOvergroups (K₂ ⧸ pCore 2 K₂)) :
    (L.map (MulAut.conj t).toMonoidHom).subgroupOf H = K₂ := by
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hLK : L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
    have h := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le] at h
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have h := C.eq_of_solvable_sylow_quotient C.t_mem ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
    hLK (SolvableSylowOvergroups.of_equiv b hsol)
  rw [h,hmap]

/-- First-factor equality proves distinctness without an odd-prime divisor assumption. -/
theorem ContainingPair.distinct_of_first_solvable_sylow_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hsol : SolvableSylowOvergroups (K₁ ⧸ pCore 2 K₁)) : K₁ ≠ K₂ := by
  intro he
  have h := map_mono (f := H.subtype) C.second_le
  rw [map_subgroupOf_eq_of_le C.right_le,←he,←C.first_eq_of_solvable_sylow_quotient hsol,
    map_subgroupOf_eq_of_le C.left_le] at h
  have hc : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge h (card_map_of_injective (MulAut.conj t).injective).ge
  exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr hc)

/-- The second quotient gives the same distinctness on the original ordered pair. -/
theorem ContainingPair.distinct_of_second_solvable_sylow_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hsol : SolvableSylowOvergroups (K₂ ⧸ pCore 2 K₂)) : K₁ ≠ K₂ := by
  intro he
  subst K₂
  exact C.distinct_of_first_solvable_sylow_quotient hsol rfl

/-- Two solvable-overgroup quotient models force both containments to be equal, contradicting strictness. -/
theorem ContainingPair.impossible_of_solvable_sylow_quotients
    (C : ContainingPair D H t K₁ K₂)
    (hfirst : SolvableSylowOvergroups (K₁ ⧸ pCore 2 K₁))
    (hsecond : SolvableSylowOvergroups (K₂ ⧸ pCore 2 K₂)) : False := by
  rcases C.strict with h | h
  · exact h.ne (C.first_eq_of_solvable_sylow_quotient hfirst)
  · exact h.ne (C.second_eq_of_solvable_sylow_quotient hsecond)

/-- The first containing quotient supplies both distinctness and the original cubic divisor. -/
theorem ContainingPair.impossible_of_first_solvable_sylow_cubic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hsol : SolvableSylowOvergroups (K₁ ⧸ pCore 2 K₁))
    (h3 : 3 ∣ Nat.card (K₁ ⧸ pCore 2 K₁)) : False := by
  let a : L ≃* K₁ := (subgroupOfEquivOfLe C.left_le).symm.trans
    (MulEquiv.subgroupCongr (C.first_eq_of_solvable_sylow_quotient hsol))
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_solvable_sylow_quotient hsol) ((Nat.card_congr b.toEquiv).symm ▸ h3)

/-- The second containing quotient supplies those premises through the literal conjugation map. -/
theorem ContainingPair.impossible_of_second_solvable_sylow_cubic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hsol : SolvableSylowOvergroups (K₂ ⧸ pCore 2 K₂))
    (h3 : 3 ∣ Nat.card (K₂ ⧸ pCore 2 K₂)) : False := by
  let a : L ≃* K₂ := ((MulAut.conj t).subgroupMap L).trans
    ((subgroupOfEquivOfLe C.right_le).symm.trans
      (MulEquiv.subgroupCongr (C.second_eq_of_solvable_sylow_quotient hsol)))
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_solvable_sylow_quotient hsol) ((Nat.card_congr b.toEquiv).symm ▸ h3)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
