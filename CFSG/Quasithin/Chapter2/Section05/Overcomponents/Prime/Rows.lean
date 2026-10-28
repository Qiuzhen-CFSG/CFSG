module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.LinearSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.J2Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.SymplecticSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.TrialitySource
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonNormalCentralizers
/-!
# The retained prime fixed-component rows in source 2.5.19

The original source Sylow shape excludes A5 fixed components. Central quotient descent then identifies the actual PSL3(4) field row and J2 outer row, and excludes symplectic and triality alternatives. The original quotient action and composite model projection remain explicit. Source: Aschbacher–Smith 2.5.19, printed pp.560–562.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows
open ComponentRefinement ComponentSelection
/-- The two retained quotient rows, with the original actor transported to
the actual linear or J₂ model. -/
@[expose] def PrimeFixedQuotientModels (D : Type*) [Group D] (a : MulAut D) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ e : D ≃* PSL(3,F), Matrix.PSL3Even.InvolutionResidualRows.FieldCase 2 (MulAut.congr e a)) ∨
  (∃ _e : D ≃* Sporadic.LeechRelated.J2.Carrier, ∀ g : D, a ≠ MulAut.conj g)

variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem eight_dvd_source_card
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K) : 8 ∣ Nat.card K := by
  let P : Sylow 2 K := default
  have h := (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape P
  have hd : 8 ∣ Nat.card P := by
    unfold SourceSylowTwoShape at h
    rcases h with h | h
    · obtain ⟨m, hm, ⟨e⟩⟩ := h
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hh : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
      simpa using Nat.mul_dvd_mul_left 2 hh
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, Semidihedral.standardModel_card]
      decide
  exact hd.trans (P : Subgroup K).card_subgroup_dvd_card

/-- The original small source component cannot be A₅: its actual Sylow
shape makes its order divisible by eight. -/
theorem source_not_alternating_five
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K) :
    ¬ Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have h := eight_dvd_source_card c hG hempty hgen hb
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h
  norm_num at h

/-- The original source component descends through the literal central quotient
and any model equivalence, retaining the exact composite projection. -/
theorem source_fixed_component_quotient_model
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E Q : Type*} [Group E] [Group Q] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B)
    (e : (E ⧸ center E) ≃* Q) :
    let b := MulAut.centralQuotientAction e a
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
    ∃ hc : ∀ x, q (a x) = b (q x),
      orderOf b = 2 ∧ IsComponent b.fixedSubgroup (B.map (MulAut.fixedSubgroupMap a b q hc)) ∧
      Nonempty (K ≃* B.map (MulAut.fixedSubgroupMap a b q hc)) := by
  let b := MulAut.centralQuotientAction e a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hc : ∀ x, q (a x) = b (q x) := fun x => (MulAut.centralQuotientAction_apply e a x).symm
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e) (MulAut.centralQuotientAction_injective e) a).trans ha
  let : IsSimpleGroup K := (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.1
  let : IsSimpleGroup B := eK.symm.isSimpleGroup
  let : IsQuasisimple B := hB.2
  have hz : center B = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center B) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h))
  have hk : q.ker ≤ center E := by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp hx)
  obtain ⟨hC, ⟨d⟩⟩ := MulAut.fixedSubgroupMap_component_of_center_eq_bot a b q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk hc B hB hz
  exact ⟨hc, hb2, hC, ⟨eK.trans d⟩⟩

/-- A J₂ central quotient automatically has the outer involution row.
The conclusion retains the original quotient actor and identifies the
original source component, with no outer-action premise. -/
theorem source_j2_quotient_outer
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B)
    (e : (E ⧸ center E) ≃* Sporadic.LeechRelated.J2.Carrier) :
    (∀ g : E ⧸ center E, quotientAut (center E) a ≠ MulAut.conj g) ∧
      Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨hc, haq, hD, ⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  have hout : ∀ g : E ⧸ center E, quotientAut (center E) a ≠ MulAut.conj g := by
    intro g he
    let b := MulAut.congr e (quotientAut (center E) a)
    let f := MulAut.fixedSubgroupCongr e (quotientAut (center E) a)
    let D := B.map (MulAut.fixedSubgroupMap a (quotientAut (center E) a)
      (QuotientGroup.mk' (center E)) hc)
    let C := D.map f.toMonoidHom
    have hC : IsComponent b.fixedSubgroup C := hD.map_equiv f
    have hi : ∃ x, b = MulAut.conj x := ⟨e g, by dsimp [b]; rw [he, MulAut.congr_conj]⟩
    obtain ⟨d⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.inner_component_equiv
      b (((MulAut.congr e).orderOf_eq _).trans haq) hi C hC
    exact source_not_alternating_five c hG hempty hgen hb
      ⟨(eD.trans (f.subgroupMap D)).trans d⟩
  exact ⟨hout, source_outer_j2_component c hG hempty hgen hb a ha B hB eK e hout⟩

/-- The actual binary linear-three quotient forces PSL₃(4), with the
literal field-case mark and the original source component PSL₃(2). -/
theorem source_linear_quotient_field
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL (E ⧸ center E) 3 (2 ^ n))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B) :
    n = 2 ∧ Nonempty (K ≃* Matrix.PSL3Two.PSL) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        ∃ e : (E ⧸ center E) ≃* PSL(3,F),
          Matrix.PSL3Even.InvolutionResidualRows.FieldCase n
            (MulAut.congr e (quotientAut (center E) a)) := by
  obtain ⟨_, haq, hD, ⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  exact source_binary_linear_fixed_component c hG hempty hgen hb hn hm
    _ haq _ hD eD

/-- A symplectic central quotient is impossible for the original nonnormal
component. Its source fixed component would be A₆ and therefore normal. -/
theorem source_nonnormal_not_symplectic_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnK : ¬ (K.subgroupOf H).Normal)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSp (E ⧸ center E) 2 (2 ^ n))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B) : False := by
  obtain ⟨_, haq, hD, ⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  obtain ⟨_, ⟨e⟩, _⟩ := source_symplectic_fixed_component c hG hempty hgen hb hn hm _ haq _ hD eD
  exact hnK (alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) _ ((subgroupOfEquivOfLe c.component_le).trans e) c.component)

/-- Triality remains excluded after taking the literal containing center. -/
theorem source_not_triality_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {n : ℕ} (hn : 0 < n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (E ⧸ center E))
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B) : False := by
  obtain ⟨_, haq, hD, ⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  exact source_not_triality_fixed_component c hG hempty hgen hb hn hm _ haq _ hD eD

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows
