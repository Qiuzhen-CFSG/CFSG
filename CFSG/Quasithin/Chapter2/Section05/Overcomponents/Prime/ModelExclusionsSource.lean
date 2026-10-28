module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusions
/-!
Prime-model exclusions through the literal central quotient. The original fixed component descends injectively, and its prime-field model excludes the alternating, binary linear and Higman–Sims rows. The prime witness remains explicit for both normal and nonnormal source components. Source: Aschbacher–Smith 2.5.19, pp.560–563.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}


omit [Finite G] in
private theorem not_small_alternating_of_prime {p n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p)) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ Nonempty (K ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  exact prime_pslTwo_not_alternating hp hp7 hn ⟨eK.symm.trans e⟩

private theorem fixed_component_in {D : Type*} [Group D] (a : MulAut D)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    IsComponentIn (B.map a.fixedSubgroup.subtype) a.fixedSubgroup := by
  refine ⟨map_subtype_le _, ?_⟩
  have he : (B.map a.fixedSubgroup.subtype).subgroupOf a.fixedSubgroup = B :=
    comap_map_eq_self_of_injective a.fixedSubgroup.subtype_injective _
  rwa [he]

theorem source_alternating_quotient_exclusion_of_prime
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (E ⧸ center E) ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let U := D.map b.fixedSubgroup.subtype
  have hU : IsComponentIn U b.fixedSubgroup := fixed_component_in b D hD
  rcases hn with rfl | rfl
  · exact alternatingGroup.SmallFixedComponents.six_model_no_component e b haq U hU
  · obtain ⟨f⟩ := alternatingGroup.SmallFixedComponents.seven_component_equiv e b haq U hU
    exact not_small_alternating_of_prime hp hp7 eK (Or.inl rfl)
      ⟨eD.trans ((D.equivMapOfInjective b.fixedSubgroup.subtype
        b.fixedSubgroup.subtype_injective).trans f)⟩

theorem source_hs_quotient_exclusion_of_prime
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [IsQuasisimple E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (e : (E ⧸ center E) ≃* _root_.Sporadic.LeechRelated.HS.Carrier) : False := by
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : IsSimpleGroup _root_.Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect _root_.Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let u := MulAut.congr e b
  let f := MulAut.fixedSubgroupCongr e b
  let C := D.map f.toMonoidHom
  have hC : IsComponent u.fixedSubgroup C := hD.map_equiv f
  have hu : orderOf u = 2 := ((MulAut.congr e).orderOf_eq b).trans haq
  let eKC : K ≃* C := eD.trans (f.subgroupMap D)
  by_cases hi : ∃ g, u = MulAut.conj g
  · obtain ⟨v⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.inner_component_equiv u hu hi C hC
    exact not_small_alternating_of_prime hp hp7 eK (Or.inr (Or.inl rfl))
      ⟨eKC.trans v⟩
  · obtain ⟨v⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.outer_component_equiv u hu hi C hC
    exact not_small_alternating_of_prime hp hp7 eK (Or.inr (Or.inr (Or.inr rfl)))
      ⟨eKC.trans v⟩

open BinaryLinear.OuterCyclic
private noncomputable def binaryLinearEquiv {D : Type*} [Group D] {n : ℕ}
    (hn : 0 < n) (hm : ClassicalGroup.IsPSL D n 2) : D ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hc))).trans
    (projectiveEquivLinear hn)⟩

theorem source_binary_quotient_exclusion_of_prime
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) n 2) : False := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  let e := binaryLinearEquiv (by omega : 0 < n) hm
  let f := MulAut.fixedSubgroupCongr e b
  exact binary_fixed_no_prime_component hn hp hp7 (MulAut.congr e b)
    (((MulAut.congr e).orderOf_eq b).trans haq) (D.map f.toMonoidHom) (hD.map_equiv f)
    ((eK.symm.trans eD).trans (f.subgroupMap D))

theorem source_small_quotient_order_exclusion_of_prime
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p) (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B)
    (hcard : Nat.card (E ⧸ center E) = 7920 ∨
      Nat.card (E ⧸ center E) = 95040 ∨ Nat.card (E ⧸ center E) = 5616) : False := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eKB
  let b := quotientAut (center E) a
  let D := B.map (MulAut.fixedSubgroupMap a b (QuotientGroup.mk' (center E)) hc)
  exact fermat_mersenne_pslTwo_no_injective_small_order hp hp7 hcard
    (b.fixedSubgroup.subtype.comp (D.subtype.comp (eK.symm.trans eD).toMonoidHom))
    (b.fixedSubgroup.subtype_injective.comp (D.subtype_injective.comp (eK.symm.trans eD).injective))

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
