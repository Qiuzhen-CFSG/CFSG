module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions.Inversion
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# An actual radical involution acting on the full Fitting section

A.3.6 gives index two for F(L/O₂(L)) in its solvable radical. Restricting
the original Sylow subgroup to L and mapping it onto this quotient lifts
that involution into R ∩ L. The odd Fitting kernel preserves its two-power
order; the inclusion-induced component equivalence identifies its image
in the literal LT/O₂(LT). Both A.3.6 alternatives then invert the entire
Fitting/Frattini section under the original ambient conjugation action.

This proves HasRadicalInverter with no extra hypotheses. Cyclicity of the
whole radical image is a separate source obligation. Conditional on it,
the unique quotient involution inverts the section for every original lift;
the lift theorem proves this by descent through the literal quotient map.
The last theorem identifies its generated subgroup with the actual Ω₁.

Source: Aschbacher--Smith, proof of 13.1.9, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter1.Section02.FittingActions
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The normalizer action restricts to the original inner action on L/O₂(L). -/
theorem localFittingSectionAction_inner (t : L) :
    localFittingSectionAction L (inclusion L.le_normalizer t) =
      FittingActions.fittingFrattiniAction (XiQuotient L)
        (QuotientGroup.mk' (pCore 2 L) t) := by
  have hq : quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion L.le_normalizer t)) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) t) := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (t * a * t⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]
  change quotientAut _ (MulAut.characteristic _
      (quotientAut (pCore 2 L) (L.normalizerMonoidHom (inclusion L.le_normalizer t)))) =
    quotientAut _ (MulAut.characteristic _ (MulAut.conj _))
  rw [hq]

/-- Sylow restriction lifts the radical/Fitting involution into the original T ∩ L. -/
theorem exists_radical_fitting_involution [Finite G] (T : Sylow 2 G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hidx : (fittingSubgroup (XiQuotient L)).relIndex
      (solvableRadical (XiQuotient L)) = 2) :
    ∃ t : L, (t : G) ∈ radicalSylowCentralizer T L ∧
      orderOf (QuotientGroup.mk' (fittingSubgroup (XiQuotient L))
        (QuotientGroup.mk' (pCore 2 L) t)) = 2 := by
  let W := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  obtain ⟨S, hS⟩ : IsSylowIn 2 ((T : Subgroup G) ⊓ L) L :=
    IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
      le_sup_left (inferInstance : (L.subgroupOf W).Normal).isSubnormal
  let K := XiQuotient L
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := QuotientGroup.mk' (fittingSubgroup K)
  let A := (solvableRadical K).map f
  have hA : Nat.card A = 2 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    exact hidx
  let : A.Normal := Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  have hpA : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let S' : Sylow 2 (K ⧸ fittingSubgroup K) :=
    S.mapSurjective ((QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)) (f := f.comp q)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [hA])
  have hzS : (z : K ⧸ fittingSubgroup K) ∈ (S' : Subgroup _) :=
    hpA.le_sylow_of_normal S' z.property
  obtain ⟨t, htS, htz⟩ := hzS
  have htT : (t : G) ∈ (T : Subgroup G) := by
    have ht : (t : G) ∈ (S : Subgroup L).map L.subtype := ⟨t, htS, rfl⟩
    exact (hS ▸ ht).1
  have htRad : q t ∈ solvableRadical K := by
    have hm : q t ∈ A.comap f := by
      change f (q t) ∈ A
      rw [show f (q t) = z from htz]
      exact z.property
    have hle : fittingSubgroup K ≤ solvableRadical K :=
      le_solvableRadical _ inferInstance inferInstance
    simpa only [A, comap_map_eq, f, QuotientGroup.ker_mk', sup_eq_left.mpr hle] using hm
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    infer_instance
  have htRadL : t ∈ solvableRadical L := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _)]
    exact htRad
  refine ⟨t, ?_, ?_⟩
  · rw [radicalSylowCentralizer_eq_inf_radical T hTL]
    exact ⟨htT, radical_le_join_radical hTL (mem_map_of_mem L.subtype htRadL)⟩
  · exact htz ▸ (Subgroup.orderOf_coe z).trans hz

private theorem radical_fitting_index_of_common {A : Type*} [Group A]
    [Group.IsPerfect A] (hc : A36Common A) (hn : ¬ IsQuasisimple A) :
    (fittingSubgroup A).relIndex (solvableRadical A) = 2 := by
  rcases hc.2.2.1 with hi | hz
  · exact hi.2.2
  · let : IsQuasisimple (A ⧸ fittingSubgroup A) := hc.2.1
    exact (hn (show PerfectCentralCovering.Cover A (A ⧸ fittingSubgroup A) from
      { toMonoidHom := QuotientGroup.mk' _
        surjective := QuotientGroup.mk'_surjective _
        isPerfect := inferInstance
        ker_le_center := by rw [QuotientGroup.ker_mk']; exact hz.1.le }).isQuasisimple).elim

/-- The original nonquasisimple local quotient has Fitting index two in its radical. -/
theorem radical_fitting_index_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (fittingSubgroup (XiQuotient L)).relIndex (solvableRadical (XiQuotient L)) = 2 := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  let e := radicalLocalQuotientEquiv hL.1.1
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hL.1.1.1
  let : Group.IsPerfect L := mem_L_isPerfect hL.1.1
  let : Group.IsPerfect (XiQuotient L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : Group.IsPerfect (radicalLocalImage T L) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hi := radical_fitting_index_of_common hc.2
    (fun hs => hn (hs.of_mulEquiv e.symm))
  rw [← relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective,
    map_fitting_equiv, map_solvableRadical_equiv]
  exact hi

/-- The original radical contains a lift of the order-two Fitting-quotient element. -/
theorem radical_fitting_involution_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ t : L, (t : G) ∈ radicalSylowCentralizer T L ∧
      orderOf (QuotientGroup.mk' (fittingSubgroup (XiQuotient L))
        (QuotientGroup.mk' (pCore 2 L) t)) = 2 :=
  exists_radical_fitting_involution T (radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn)
    (radical_fitting_index_source h hL hn)

/-- The full Fitting subgroup of the actual local two-core quotient has odd order. -/
theorem local_fitting_odd_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L) :
    Nat.Coprime 2 (Nat.card (fittingSubgroup (XiQuotient L))) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  let e := radicalLocalQuotientEquiv hL.1.1
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hL.1.1.1
  have he : Nat.card (fittingSubgroup (XiQuotient L)) =
      Nat.card (fittingSubgroup (radicalLocalImage T L)) := by
    rw [← map_fitting_equiv e, card_map_of_injective e.injective]
  rw [he, hc.2.1]
  exact pPrimeCore_coprime_card

/-- An actual element of R ∩ L survives as an involution in LT/O₂(LT) and inverts the full Fitting Frattini section by original conjugation. -/
theorem radical_involution_full_inversion_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ t : L, (t : G) ∈ radicalSylowCentralizer T L ∧
      orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) t)) = 2 ∧
      ∀ x : LocalFittingSection L,
        localFittingSectionAction L (inclusion L.le_normalizer t) x = x⁻¹ := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  let e := radicalLocalQuotientEquiv hL.1.1
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hL.1.1.1
  have hs := RadicalStructure.nonsimple_radical hc
    (fun hs => hn (hs.of_mulEquiv e.symm))
  let : Group.IsPerfect L := mem_L_isPerfect hL.1.1
  let : Group.IsPerfect (XiQuotient L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  obtain ⟨t, htR, ht⟩ := radical_fitting_involution_source h hL hn
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := QuotientGroup.mk' (fittingSubgroup (XiQuotient L))
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact local_fitting_odd_source h hL
  have hpow : ∃ k : ℕ, (q t) ^ (2 ^ k) = 1 := by
    have htT := radicalSylowCentralizer_le (T : Subgroup G) L htR
    obtain ⟨k, hk⟩ := T.isPGroup' (⟨t, htT⟩ : T)
    refine ⟨k, ?_⟩
    have htPow : t ^ (2 ^ k) = 1 := Subtype.ext (congrArg (fun z : T => (z : G)) hk)
    rw [← map_pow, htPow, map_one]
  have hqt : orderOf (q t) = 2 :=
    (f.orderOf_eq_of_prime_power_of_coprime_ker hcop (q t) hpow).symm.trans ht
  refine ⟨t, htR, ?_, ?_⟩
  · have heq : (e (q t) : XiQuotient (L ⊔ (T : Subgroup G))) =
        QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
          (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) t) := rfl
    rw [← heq, Subgroup.orderOf_coe, e.orderOf_eq]
    exact hqt
  · intro x
    rw [localFittingSectionAction_inner]
    exact fitting_inversion_of_a36_equiv e hs _ ht x

/-- The source inverter premise, with all model, quotient-order and action inputs discharged. -/
theorem radical_inverter_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) : HasRadicalInverter T L := by
  obtain ⟨t, htR, _, hi⟩ := radical_involution_full_inversion_source h hL hn
  exact ⟨inclusion L.le_normalizer t, htR, hi⟩

private theorem localFittingSectionAction_eq_of_join_image_eq [Finite G]
    {T : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hTL : T ≤ normalizer (L : Set G))
    (r s : (L ⊔ T : Subgroup G))
    (heq : QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G)) r =
      QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G)) s) :
    localFittingSectionAction L (inclusion (sup_le L.le_normalizer hTL) r) =
      localFittingSectionAction L (inclusion (sup_le L.le_normalizer hTL) s) := by
  have hq : quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hTL) r)) =
      quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hTL) s)) := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [quotientAut_apply_mk, quotientAut_apply_mk]
    apply (radicalLocalQuotientEquiv hL).injective
    apply Subtype.ext
    change QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G))
        (r * inclusion (show L ≤ L ⊔ T from le_sup_left) a * r⁻¹) =
      QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G))
        (s * inclusion (show L ≤ L ⊔ T from le_sup_left) a * s⁻¹)
    simp only [map_mul, map_inv, heq]
  exact congrArg (fun a : MulAut (XiQuotient L) =>
    quotientAut (frattini (fittingSubgroup (XiQuotient L)))
      (MulAut.characteristic (fittingSubgroup (XiQuotient L)) a)) hq


/-- If the radical image is cyclic, every original lift of its unique involution inverts the full section. Cyclicity remains a source premise. -/
theorem radical_involution_inverts_of_cyclic_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hcyc : IsCyclic (radicalTwoCoreImage T L))
    (r : normalizer (L : Set G)) (hr : (r : G) ∈ radicalSylowCentralizer T L)
    (hrW : (r : G) ∈ L ⊔ (T : Subgroup G))
    (hro : orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
      ⟨r, hrW⟩) = 2) (x : LocalFittingSection L) :
    localFittingSectionAction L r x = x⁻¹ := by
  let := hcyc
  obtain ⟨t, htR, hto, hi⟩ := radical_involution_full_inversion_source h hL hn
  let W := L ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 W)
  let tW : W := inclusion le_sup_left t
  have htmem : q tW ∈ radicalTwoCoreImage T L := ⟨tW, htR, rfl⟩
  let z : radicalTwoCoreImage T L := ⟨q tW, htmem⟩
  have hzo : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans hto
  let rW : W := ⟨r, hrW⟩
  have hrmem : q rW ∈ radicalTwoCoreImage T L := ⟨rW, hr, rfl⟩
  have hrr : orderOf (⟨q rW, hrmem⟩ : radicalTwoCoreImage T L) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans hro
  have he : q rW = q tW := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two hrr hzo)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have ha := localFittingSectionAction_eq_of_join_image_eq hL.1.1 hTL rW tW he
  change localFittingSectionAction L r =
    localFittingSectionAction L (inclusion L.le_normalizer t) at ha
  rw [ha]
  exact hi x


private theorem cyclic_omega_eq_zpowers {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (z : A) (hz : orderOf z = 2) : omega₁ A (p := 2) = zpowers z := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro a ha
    have ha2 : a ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using ha
    by_cases ha1 : a = 1
    · exact ha1 ▸ (zpowers z).one_mem
    · rw [IsCyclic.eq_of_orderOf_eq_two (orderOf_eq_prime ha2 ha1) hz]
      exact mem_zpowers z
  · apply zpowers_le.mpr
    exact subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one, hz] using pow_orderOf_eq_one z)


/-- The literal quotient image of an element of L that belongs to R. -/
@[expose] def radicalImageOfLocal {T : Subgroup G} (t : L)
    (ht : (t : G) ∈ radicalSylowCentralizer T L) : radicalTwoCoreImage T L :=
  ⟨QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G))
    (inclusion (show L ≤ L ⊔ T from le_sup_left) t),
      ⟨inclusion (show L ≤ L ⊔ T from le_sup_left) t, ht, rfl⟩⟩


/-- Under cyclicity, the actual inverter generates the first omega subgroup. -/
theorem radical_omega_inversion_of_cyclic_source [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T) (hL : Chapter12.Section02.FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hcyc : IsCyclic (radicalTwoCoreImage T L)) :
    ∃ (t : L) (htR : (t : G) ∈ radicalSylowCentralizer T L),
      orderOf (radicalImageOfLocal (T := (T : Subgroup G)) (L := L) t htR) = 2 ∧
      omega₁ (radicalTwoCoreImage T L) (p := 2) = zpowers (radicalImageOfLocal (T := (T : Subgroup G)) (L := L) t htR) ∧
      ∀ x : LocalFittingSection L,
        localFittingSectionAction L (inclusion L.le_normalizer t) x = x⁻¹ := by
  let := hcyc
  obtain ⟨t, htR, hto, hi⟩ := radical_involution_full_inversion_source h hL hn
  have hzo : orderOf (radicalImageOfLocal (T := (T : Subgroup G)) (L := L) t htR) = 2 :=
    (Subgroup.orderOf_coe (radicalImageOfLocal (T := (T : Subgroup G)) (L := L) t htR)).symm.trans hto
  exact ⟨t, htR, hzo, cyclic_omega_eq_zpowers _ hzo, hi⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
