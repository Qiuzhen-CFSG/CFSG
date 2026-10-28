module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterCentralizerComparison

/-!
# HS recognition conditional on the original overgroup construction

This application uses the supplied higher-rank natural marking and only
the same-ambient 12.2.13 alternatives. Characteristic two identifies both
literal generalized Fitting subgroups. The two source structures then give
HS1--HS2 on the original flag point and seed. I.4.8 remains an explicit,
independently owned recognition premise.

The general consumers retain the overgroup structure explicitly. The final
specialized consumers use either U=O₂(H) or the proved order-four
cubic-centralizer branch. The order-eight alternative now carries the original
outer involution and an actual transfer conjugator into PU outside both P
and U. Both Sylow-centralizer bounds and the characteristic-point
obstruction to matching them are proved. The extremal-representative
and transfer exclusion still remain. These are conditional applications,
not a proof of the final nonextraspecial branch. Source:
Aschbacher--Smith, printed p.1005 and I.4.8 on printed p.418.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- HS1--HS2 from the original natural marking and same-ambient predecessors.
Both source structures remain explicit until their independent constructions finish. -/
theorem type_of_higherRank_local_and_overgroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  let := h.chosen.elementary
  obtain ⟨z, hz, hpoint, hH⟩ := source_point_centralizer F
  have hfit : generalizedFitting F.H = pCore 2 F.H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (F.localKernel_characteristicTwo h.source.simpleQTKE L
        (normalizer (L : Set G)) F.H (h.point_mem_Hz_at F alternatives))
  have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hv : V ≠ ⊥ := by intro he; simp [he] at hc
  have hlocal : IsTwoLocal (normalizer (V : Set G)) :=
    ⟨V, hv, IsElementaryAbelian.isPGroup 2 V, rfl⟩
  obtain ⟨M, hVM, hM⟩ := Finite.exists_le_maximal hlocal
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := F.last ▸ F.invariant 3
  have hfitM := generalizedFitting_eq_pCore_of_sylow_overgroup T
    (normalizer (V : Set G)) M hTV hVM
    (h.source.simpleQTKE.evenCharacteristic T M hM (hTV.trans hVM))
  let e : F.U ≃* pCore 2 F.H :=
    (MulEquiv.subgroupCongr overgroup.closure_core).trans
      ((pCore 2 F.H).equivMapOfInjective F.H.subtype F.H.subtype_injective).symm
  refine ⟨z, hpoint, {
    involution := hz
    elementary := h.chosen.elementary
    seed_card := hc
    centralizer_core := ?_
    centralizer_quotient := ?_
    seed_le_core := ?_
    normalizer_core := ?_
    normalizer_quotient := ?_ }⟩
  · change HigmanSims.CoreShape (generalizedFitting (centralizer ({z} : Set G)))
    rw [← hH, hfit]
    exact localData.core_shape.of_equiv e
  · change Nonempty
      ((centralizer ({z} : Set G) ⧸ generalizedFitting (centralizer ({z} : Set G))) ≃*
        Equiv.Perm (Fin 5))
    rw [← hH]
    obtain ⟨q⟩ := localData.quotient F
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hfit).trans q⟩
  · change V ≤ (generalizedFitting (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype
    rw [← hH, hfit]
    change V ≤ F.H.pCoreIn 2
    rw [← overgroup.closure_core]
    exact le_conjugateSpanBy V F.H
  · rw [hfitM, overgroup.seed_normalizer]
    exact overgroup.homocyclic
  · apply ClassicalGroup.IsPSL.of_mulEquiv _
      (QuotientGroup.quotientMulEquivOfEq hfitM)
    rw [overgroup.seed_normalizer]
    exact h.quotient_model

/-- The separately named conditional I.4.8 application at the actual G,T.
Recognition and the two source structures are not asserted to be constructed. -/
theorem recognition_of_higherRank_local_and_overgroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_higherRank_local_and_overgroup h alternatives F localData overgroup
  exact recognition G ⟨z, V, hz⟩

/-- Conditional terminal assembly with the homocyclic core and equality of the
 two normalizers now discharged by the original 14.3.33(1) construction.
The point-centralizer core and full seed normalizer remain source obligations. -/
theorem overgroupStructure_of_closure_core_and_seed_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (hU : F.U = F.H.pCoreIn 2) (hN : normalizer (V : Set G) = L) :
    OvergroupStructure L F where
  closure_core := hU
  seed_normalizer := hN
  actor_normalizer := (Overgroup.actor_normalizer_eq_seed_normalizer h structural alternatives
    F localData hne).trans hN
  homocyclic := Overgroup.core_homocyclic h structural alternatives F localData hne

/-- HS1--HS2 after the remaining point-core and seed-normalizer assertions.
No homocyclic-core witness is assumed by this specialized consumer. -/
theorem type_of_higherRank_local_core_and_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (hU : F.U = F.H.pCoreIn 2) (hN : normalizer (V : Set G) = L) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_higherRank_local_and_overgroup h alternatives F localData
    (overgroupStructure_of_closure_core_and_seed_normalizer h structural alternatives
      F localData hne hU hN)

/-- The separately conditional HS recognition application after the proved
homocyclic-core construction. I.4.8 and both terminal equalities remain explicit. -/
theorem recognition_of_higherRank_local_core_and_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (hU : F.U = F.H.pCoreIn 2) (hN : normalizer (V : Set G) = L)
    (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_higherRank_local_core_and_normalizer h structural alternatives
    F localData hne hU hN
  exact recognition G ⟨z, V, hz⟩

/-- All remaining overgroup fields follow from Q=U. The source transfer
argument must still prove this point-core equality. -/
theorem overgroupStructure_of_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) (hU : F.U = F.H.pCoreIn 2) :
    OvergroupStructure L F :=
  overgroupStructure_of_closure_core_and_seed_normalizer h structural alternatives F localData hne hU
    (Overgroup.seed_normalizer_eq_actor_of_closure_core h structural alternatives F localData hne hU)

/-- The conditional HS type application now has only the point-core equality
left from 14.3.33; the full normalizer equalities are proved. -/
theorem type_of_higherRank_local_and_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) (hU : F.U = F.H.pCoreIn 2) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_higherRank_local_and_overgroup h alternatives F localData
    (overgroupStructure_of_closure_core h structural alternatives F localData hne hU)

/-- The literal HS carrier follows conditionally from Q=U and I.4.8.
Neither remaining source obligation is asserted here. -/
theorem recognition_of_higherRank_local_and_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) (hU : F.U = F.H.pCoreIn 2)
    (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_higherRank_local_and_closure_core h structural alternatives
    F localData hne hU
  exact recognition G ⟨z, V, hz⟩

/-- The source's order-four cubic-centralizer branch constructs every field of
14.3.33, including both literal normalizer equalities. -/
theorem overgroupStructure_of_cubic_centralizer_card_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 4) :
    OvergroupStructure L F :=
  overgroupStructure_of_closure_core h structural alternatives F localData hne
    (Overgroup.closure_core_of_cubic_centralizer_card_four h structural alternatives
      F localData hne x hx hx3 hc)

/-- The only remaining overgroup branch carries an actual cubic of the original
L₁, its nonabelian order-eight centralizer in Q, and |Q|=128. -/
theorem overgroupStructure_or_outer_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    OvergroupStructure L F ∨ ∃ x : G, x ∈ F.Li L 1 ∧ orderOf x = 3 ∧
      Nat.card (F.H.pCoreIn 2) = 128 ∧
      Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8 ∧
      ¬ IsMulCommutative (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) := by
  obtain ⟨x,hx,hx3⟩ := Overgroup.exists_point_cubic h structural alternatives F localData hne
  rcases Overgroup.closure_core_or_outer_cubic h structural alternatives F localData hne x hx hx3
    with hU | houter
  · exact Or.inl (overgroupStructure_of_closure_core h structural alternatives F localData hne hU)
  · exact Or.inr ⟨x,hx,hx3,houter⟩

/-- The original HS1--HS2 configuration is constructed in the order-four
cubic-centralizer branch, retaining the same point and seed. -/
theorem type_of_higherRank_local_and_cubic_centralizer_card_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 4) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_higherRank_local_and_overgroup h alternatives F localData
    (overgroupStructure_of_cubic_centralizer_card_four h structural alternatives
      F localData hne x hx hx3 hc)

/-- The separately conditional I.4.8 application in the order-four branch.
The independent recognition premise is retained literally. -/
theorem recognition_of_higherRank_local_and_cubic_centralizer_card_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 4)
    (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z,_,hz⟩ := type_of_higherRank_local_and_cubic_centralizer_card_four h structural alternatives
    F localData hne x hx hx3 hc
  exact recognition G ⟨z,V,hz⟩

/-- The genuine order-eight alternative now includes the actual source
involution and transfer conjugator, with rᵍ in PU outside both P and U.
It is retained for the remaining extremal-centralizer exclusion. -/
theorem overgroupStructure_or_outer_transfer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    OvergroupStructure L F ∨ ∃ x r g : G,
      x ∈ F.Li L 1 ∧ orderOf x = 3 ∧
      Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8 ∧
      r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧ orderOf r = 2 ∧
      (∀ l ∈ L, ⁅r,l⁆ ∈ V) ∧ (∀ p ∈ L.pCoreIn 2, r*p*r⁻¹ = p⁻¹) ∧
      g⁻¹*r*g ∈ L.pCoreIn 2 ⊔ F.U ∧ g⁻¹*r*g ∉ L.pCoreIn 2 ∧ g⁻¹*r*g ∉ F.U ∧
      (∀ u ∈ F.U, ¬ IsConj r u) := by
  rcases overgroupStructure_or_outer_cubic h structural alternatives F localData hne with hover | houter
  · exact Or.inl hover
  · obtain ⟨x,hx,hx3,_,hcard,_⟩ := houter
    obtain ⟨r,g,hr,hrL,hr2,hd,hi,hg,hgP,hgU,hno⟩ :=
      Overgroup.exists_outer_involution_and_nonclosure_conjugate h structural alternatives F localData hne x hx hx3 hcard
    exact Or.inr ⟨x,r,g,hx,hx3,hcard,hr,hrL,hr2,hd,hi,hg,hgP,hgU,hno⟩

/-- The remaining outer branch has the source Sylow-centralizer comparison:
C_T(r) has order 128, the actual transfer target has centralizer of order
at most 128, and its conjugator cannot match those centralizers.
The extremal-transfer exclusion remains an obligation of this assembly. -/
theorem overgroupStructure_or_outer_centralizer_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    OvergroupStructure L F ∨ ∃ x r g : G,
      x ∈ F.Li L 1 ∧ orderOf x = 3 ∧
      Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8 ∧
      r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧ orderOf r = 2 ∧
      (∀ l ∈ L, ⁅r,l⁆ ∈ V) ∧
      g⁻¹*r*g ∈ L.pCoreIn 2 ⊔ F.U ∧ g⁻¹*r*g ∉ L.pCoreIn 2 ∧ g⁻¹*r*g ∉ F.U ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({r} : Set G) : Subgroup G) = 128 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({g⁻¹*r*g} : Set G) : Subgroup G) ≤ 128 ∧
      conjugate ((T : Subgroup G) ⊓ centralizer ({r} : Set G)) g ≠
        (T : Subgroup G) ⊓ centralizer ({g⁻¹*r*g} : Set G) := by
  rcases overgroupStructure_or_outer_transfer h structural alternatives F localData hne with hover | houter
  · exact Or.inl hover
  · obtain ⟨x,r,g,hx,hx3,hcard,hr,hrL,hr2,hd,_,hg,hgP,hgU,_⟩ := houter
    have hQ : Nat.card (F.H.pCoreIn 2) = 128 := by
      rw [Overgroup.point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives
        F localData hne x hx hx3,hcard]
    have hT := Overgroup.sylow_card_of_point_core_card F localData hQ
    have hbound := Overgroup.core_closure_nonclosure_sylow_centralizer_bound h structural alternatives
      F localData hne _ hg hgP hgU
    rw [hT] at hbound
    exact Or.inr ⟨x,r,g,hx,hx3,hcard,hr,hrL,hr2,hd,hg,hgP,hgU,
      Overgroup.outer_involution_sylow_centralizer_card h structural alternatives F localData hne
        x hx hx3 hcard r hr hrL hr2 hd,by omega,
      Overgroup.outer_involution_no_centralizer_conjugate h structural alternatives F localData hne
        x hx hx3 hcard r hr hrL hr2 hd g hg hgU⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
