module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation.LinearSeparation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.Initial
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# C-component commutation from noncentral A.3.6

Distinct C-components of a finite SQTK group with trivial two-core commute,
assuming only the genuine universal noncentral structural branch of A.3.6.
That input retains both radical alternatives and all common source clauses.
Its construction and final discharge belong to the noncentral A.3.6 assembly.

We restrict to the join of the components, which is perfect and subnormal,
with both components normal. Central Fitting subgroups give ordinary
components by the Fitting-centralizer criterion. In the other cases, the
actual full-core Frattini actions have the common proper Fitting kernel and
prime-plane quotients. The embedded cores are normal in the join, so the
proved action-separation theorem makes the other component centralize each
one. Their product is F = F*, and generalized-Fitting self-centralization
finishes the proof. The homocyclic exponents remain unrestricted.

The last theorem passes this universal A.3.7 conclusion to the actual
Chapter 1 quotient application, proving both inclusions of 1.2.1(2) under
its original SQTK hypothesis on the quotient by the two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition A.3.7 and its proof, printed p.45; Proposition 1.2.1(2), p.503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
universe u

/-- The genuine noncentral branch of A.3.6, uniformly in the ambient group. -/
def NoncentralStructureInput (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK 𝒦 X → pCore 2 X = ⊥ →
    ∀ B : Subgroup X, B.IsCComponent → ¬ fittingSubgroup B ≤ center B →
      (A36Natural B ∨ A36Nilpotent B) ∧ A36Common B

variable {G : Type u} [Group G] [Finite G]

private theorem quasisimple_of_central_fitting {B : Subgroup G}
    (hB : B.IsCComponent) (hf : fittingSubgroup B ≤ center B) : IsQuasisimple B := by
  have hr : solvableRadical B = center B := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center B) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

private theorem core_frattini_card {B : Type u} [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] (hs : A36Natural B ∨ A36Nilpotent B)
    (hd : p ∣ Nat.card (fittingSubgroup B)) :
    Nat.card (pCore p B ⧸ frattini (pCore p B)) ≤ p ^ 2 := by
  rcases hs with hn | hn
  · obtain ⟨_, he, hc⟩ := RadicalStructure.natural_core hn hd
    exact hc ▸ Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  · rw [Nat.card_congr (FittingActions.coreOmegaEquiv (Or.inr hn) hd).toEquiv,
      (RadicalActions.Nilpotent.frattini_shape hn hd).2]

omit [Finite G] in
/-- The common kernel is proper, so the actual embedded core does not
centralize its component. -/
private theorem embedded_core_active {B : Subgroup G} {p : ℕ}
    (hc : A36Common B)
    (hk : (FittingActions.coreFrattiniAction p B).ker = fittingSubgroup B) :
    ⁅(pCore p B).map B.subtype, B⁆ ≠ ⊥ := by
  intro hz
  have hcent : B ≤ centralizer ((pCore p B).map B.subtype : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hz
  have hf : fittingSubgroup B = ⊤ := by
    apply top_unique
    intro b _
    rw [← hk]
    have ha : FittingActions.coreAction p B b = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      have he := hcent b.property x (mem_map_of_mem B.subtype x.property)
      change (b : G) * (x : B) * (b : G)⁻¹ = x
      rw [← he]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    change quotientAut _ (FittingActions.coreAction p B b) = 1
    rw [ha, map_one]
  let : IsQuasisimple (B ⧸ fittingSubgroup B) := hc.2.1
  let : IsSimpleGroup ((B ⧸ fittingSubgroup B) ⧸ center (B ⧸ fittingSubgroup B)) :=
    IsQuasisimple.simple
  let : Nontrivial (B ⧸ fittingSubgroup B) :=
    (QuotientGroup.mk'_surjective (center (B ⧸ fittingSubgroup B))).nontrivial
  have : Subsingleton (B ⧸ fittingSubgroup B) := QuotientGroup.subsingleton_iff.mpr hf
  exact not_subsingleton (B ⧸ fittingSubgroup B) this

private theorem embedded_core_centralizes [Group.IsPerfect G]
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hs : A36Natural B ∨ A36Nilpotent B) (hc : A36Common B)
    (ha : FittingActions.FrattiniActionData B)
    (p : ℕ) [Fact p.Prime] : ⁅(pCore p B).map B.subtype, C⁆ = ⊥ := by
  by_cases hd : p ∣ Nat.card (fittingSubgroup B)
  · let P := (pCore p B).map B.subtype
    let : P.Normal := ConjAct.normal_of_characteristic_of_normal
    let e : pCore p B ≃* P := (pCore p B).equivMapOfInjective
      B.subtype B.subtype_injective
    have hcard : Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
      let eQ := QuotientGroup.congr _ _ e (frattini_map_equiv e)
      rw [← Nat.card_congr eQ.toEquiv]
      exact core_frattini_card hs hd
    obtain ⟨hp, hk, _⟩ := ha.2.2 p hd
    exact centralizes_normal_pGroup hp P (pCore_isPGroup.map B.subtype) hcard
      hB hC hne (embedded_core_active hc hk)
  · have hp : pCore p B = ⊥ := by
      apply card_eq_one.mp
      exact (pCore_isPGroup (p := p) (G := B)).card_eq_or_dvd.resolve_right
        (fun hdP => hd (hdP.trans (card_dvd_of_le (pCore_le_fitting B p))))
    rw [hp, Subgroup.map_bot, commutator_bot_left]

private theorem commutes_of_noncentral [Group.IsPerfect G]
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hn : ¬ fittingSubgroup B ≤ center B)
    (hs : A36Natural B ∨ A36Nilpotent B) (hc : A36Common B) : ⁅B,C⁆ = ⊥ := by
  let : Group.IsPerfect C := hC.perfect
  have h : A36Conclusion B :=
    ⟨hs.elim A36Alternative.natural A36Alternative.nilpotent, hc⟩
  have ha := (FittingActions.strengthened_frattini_actions hG hO hB h).2
    (NoncentralFitting.not_quasisimple_of_noncentral_fitting hn)
  apply commutes_of_centralizes_generalizedFitting B C
  rw [ha.1, commutator_comm, commutator_eq_bot_iff_le_centralizer]
  have heach : ∀ p : (Nat.card B).primeFactors.attach,
      (pCore p.val.val B).map B.subtype ≤ centralizer (C : Set G) := by
    intro p
    rw [← commutator_eq_bot_iff_le_centralizer]
    exact embedded_core_centralizes hB hC hne hs hc ha p.val.val
  have hf : (fittingSubgroup B).map B.subtype ≤ centralizer (C : Set G) := by
    rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact iSup_le heach
  exact le_centralizer_iff.mp hf

private theorem commutes_in_perfect [Group.IsPerfect G]
    {𝒦 : GroupClass.{u}} (h36 : NoncentralStructureInput 𝒦)
    (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    {B C : Subgroup G} [B.Normal] [C.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) : ⁅B,C⁆ = ⊥ := by
  by_cases hb : fittingSubgroup B ≤ center B
  · by_cases hc : fittingSubgroup C ≤ center C
    · exact (show IsComponent G B from
        ⟨hB.subnormal, quasisimple_of_central_fitting hB hb⟩).commutator_eq_bot_of_ne
        ⟨hC.subnormal, quasisimple_of_central_fitting hC hc⟩ hne
    · obtain ⟨hs, hscommon⟩ := h36 G hG hO C hC hc
      rw [commutator_comm]
      exact commutes_of_noncentral hG hO hC hB hne.symm hc hs hscommon
  · obtain ⟨hs, hc⟩ := h36 G hG hO B hB hb
    exact commutes_of_noncentral hG hO hB hC hne hb hs hc

/-- A.3.7 from precisely the universal noncentral structural input of A.3.6. -/
theorem commutator_eq_bot_of_noncentral_structure
    {𝒦 : GroupClass.{u}} (h36 : NoncentralStructureInput 𝒦)
    (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (B C : Subgroup G) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hne : B ≠ C) : ⁅B,C⁆ = ⊥ := by
  let H := B ⊔ C
  let : (cComponentLayer G).Characteristic := cComponentLayer_characteristic
  have hHL : H ≤ cComponentLayer G := sup_le (le_cComponentLayer hB) (le_cComponentLayer hC)
  have hLH : cComponentLayer G ≤ normalizer H :=
    (le_inf (cComponentLayer_le_normalizer hB) (cComponentLayer_le_normalizer hC)).trans
      (normalizer_inf_normalizer_le_normalizer_sup B C)
  let : (H.subgroupOf (cComponentLayer G)).Normal := normal_subgroupOf_of_le_normalizer hLH
  have hHsub : H.IsSubnormal := (inferInstance :
    (H.subgroupOf (cComponentLayer G)).Normal).isSubnormal.trans hHL
      (inferInstance : (cComponentLayer G).Normal).isSubnormal
  have hOH : pCore 2 H = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hHsub, hO, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
  let : Group.IsPerfect B := hB.perfect
  let : Group.IsPerfect C := hC.perfect
  let : Group.IsPerfect H := isPerfect_iff.mpr (le_antisymm H.commutator_le_self
    (sup_le (by
      rw [← commutator_eq_self (H := B)]
      exact commutator_mono le_sup_left le_sup_left) (by
      rw [← commutator_eq_self (H := C)]
      exact commutator_mono le_sup_right le_sup_right)))
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (hHL.trans (cComponentLayer_le_normalizer hB))
  let : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (hHL.trans (cComponentLayer_le_normalizer hC))
  have hB' := hB.subgroupOf (show B ≤ H from le_sup_left)
  have hC' := hC.subgroupOf (show C ≤ H from le_sup_right)
  have hne' : B.subgroupOf H ≠ C.subgroupOf H := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le (show B ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show C ≤ H from le_sup_right)] using
      congrArg (Subgroup.map H.subtype) he
  have hcomm := commutes_in_perfect h36 (hG.subgroup H) hOH hB' hC' hne'
  simpa only [map_commutator, map_subgroupOf_eq_of_le (show B ≤ H from le_sup_left),
    map_subgroupOf_eq_of_le (show C ≤ H from le_sup_right), Subgroup.map_bot] using
    congrArg (Subgroup.map H.subtype) hcomm

/-- The literal universal A.3.7 interface consumed by Chapter 1. -/
theorem universal_A_3_7_of_noncentral_structure
    {𝒦 : GroupClass.{u}} (h36 : NoncentralStructureInput 𝒦) :
    ∀ (X : Type u) [Group X] [Finite X], IsSQTK 𝒦 X → pCore 2 X = ⊥ →
      ∀ B C : Subgroup X, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B,C⁆ = ⊥ := by
  intro X _ _ hX hO B C hB hC hne
  exact commutator_eq_bot_of_noncentral_structure h36 hX hO B C hB hC hne

/-- Both original two-core inclusions of 1.2.1(2), with A.3.7 discharged
and the original SQTK hypothesis on the actual two-core quotient retained. -/
theorem proposition_1_2_1_two_of_noncentral_structure
    {𝒦 : GroupClass.{u}} (h36 : NoncentralStructureInput 𝒦)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    ⁅B,C⁆ ≤ B.pCoreIn 2 ⊓ C.pCoreIn 2 ∧ B.pCoreIn 2 ⊓ C.pCoreIn 2 ≤ pCore 2 G :=
  Chapter1.Section02.proposition_1_2_1_two_of_A_3_7
    (universal_A_3_7_of_noncentral_structure h36) hQ hB hC hne

end CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
