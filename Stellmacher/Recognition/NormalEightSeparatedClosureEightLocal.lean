module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocalData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightSplitting
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightFixed
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Identifying the split local centralizer

An order-four moving plane and the outside conjugate involution generate
a dihedral group of order eight. Once the odd-action fixed factor is shown
to have order two, multiplication identifies the original involution
centralizer with their direct product.

This is the final local identification in Janko–Thompson, Math. Z. 113
(1970), Lemma 3.1, printed p.388. The hypotheses below retain the actual
embedded splitting factors. The final theorem constructs those factors from
the local setup and proves that the fixed factor has order two, discharging
both inputs to the identification.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The concrete splitting with a fixed factor of order two identifies the
local centralizer as `C₂ × D₈`. -/
public theorem centralizer_model_of_localSplitting
    {S : Sylow 2 G} {W : Subgroup S} [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S) (d : CentralizerSetup S W i)
    (s : LocalSplitting d z) (hfixed : Nat.card s.fixed = 2) :
    Nonempty (centralizer ({i} : Set S) ≃*
      (Multiplicative (ZMod 2) × DihedralGroup 4)) := by
  let E := closureInSylow d
  let C := centralizer ({i} : Set S)
  let T := centralizer (E : Set S)
  let A := s.plane
  let B := s.fixed
  let x := s.outside
  let D := A ⊔ zpowers x
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 E := closureInSylow_elementary d
  let : IsElementaryAbelian 2 A := s.plane_elementary
  have hiE : i ∈ E := four_le_closureInSylow hiW d hiW
  have hTC : T ≤ C := centralizer_le (Set.singleton_subset_iff.mpr hiE)
  have hET : E ≤ T := E.le_centralizer
  have hAT : A ≤ T := s.plane_le.trans hET
  have hBT : B ≤ T := le_sup_right.trans s.product.le
  have hxC : x ∈ C := conjugate_closure_le_centralizer S W hW z hzW hzC hz
    i hiW hi hiC d s.mover s.outside_mem_conjugate
  have hxA : x ∉ A := fun hx => s.outside_not_centralizing (hAT hx)
  have hx2 : x ^ 2 = 1 := by
    have hxorder : orderOf x = 2 := s.outside_order
    simpa only [hxorder] using pow_orderOf_eq_one x
  have hDn : x ∈ normalizer (A : Set S) := s.plane_normalized hxC
  have hDcard : Nat.card D = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution A x hx2 hxA hDn, s.plane_card]
  have hBA : B ≤ centralizer (A : Set S) := hBT.trans (centralizer_le s.plane_le)
  have hBx : B ≤ centralizer ({x} : Set S) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (s.outside_centralizes_fixed b hb)
  have hBD : B ≤ centralizer (D : Set S) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hBA)
      (zpowers_le.mpr s.outside_centralizes_fixed)
  have hTcard : Nat.card T = 8 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
      (hBA.trans (Subgroup.centralizer_le_normalizer _))
    rw [s.plane_card, hfixed, s.disjoint.eq_bot, card_bot, s.product, one_mul] at hh
    exact hh.symm
  have hCcard : Nat.card C = 16 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup S) T C bot_le hTC
    simp only [relIndex_bot_left] at hh
    rw [s.index, hTcard] at hh
    exact hh.symm
  have hCgen : T ⊔ zpowers x = C := by
    apply eq_of_le_of_card_ge (sup_le hTC (zpowers_le.mpr hxC))
    rw [card_sup_zpowers_of_normalizing_involution T x hx2 s.outside_not_centralizing
      ((normalizer_le_normalizer_centralizer E)
        (centralizer_le_normalizer_closureInSylow d hxC))]
    rw [hTcard, hCcard]
  have hBDgen : B ⊔ D = C := by
    change B ⊔ (A ⊔ zpowers x) = C
    rw [← sup_assoc, sup_comm B A, s.product, hCgen]
  have hBDdis : Disjoint B D := by
    apply disjoint_iff.mpr
    apply card_eq_one.mp
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
      (hBD.trans (Subgroup.centralizer_le_normalizer _))
    rw [hDcard, hfixed, sup_comm D B, hBDgen, hCcard, inf_comm D B] at hh
    omega
  let AD := A.subgroupOf D
  let : IsElementaryAbelian 2 AD := IsElementaryAbelian.subgroupOf le_sup_left
  have hADcard : Nat.card AD = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ D from le_sup_left)).toEquiv]
    exact s.plane_card
  have hADnoncentral : ¬ AD ≤ center D := by
    intro hcent
    apply s.outside_not_centralizing
    have hAx : A ≤ centralizer ({x} : Set S) := by
      intro a ha
      apply mem_centralizer_singleton_iff.mpr
      exact (congrArg Subtype.val (mem_center_iff.mp
        (hcent (show (⟨a, (le_sup_left : A ≤ D) ha⟩ : D) ∈ AD from ha))
        (⟨x, (le_sup_right : zpowers x ≤ D) (mem_zpowers x)⟩ : D))).symm
    have hTx : T ≤ centralizer ({x} : Set S) := s.product.ge.trans (sup_le hAx hBx)
    intro e he
    exact mem_centralizer_singleton_iff.mp (hTx (hET he))
  obtain ⟨eD⟩ := dihedral_eight_of_noncentral_elementary_four hDcard AD hADcard hADnoncentral
  let eB : B ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hfixed (by
    simp [Nat.card_eq_fintype_card])
  have hcomm (b : B) (a : D) : Commute (b : S) (a : S) :=
    (hBD b.property a a.property).symm
  let f : B × D →* S := B.subtype.noncommCoprod D.subtype hcomm
  have hfrange : f.range = C := (MonoidHom.noncommCoprod_range B.subtype D.subtype hcomm).trans
    (by simpa only [range_subtype] using hBDgen)
  let fC : B × D →* C := f.codRestrict C (fun y => hfrange ▸ ⟨y, rfl⟩)
  have hf : Function.Bijective fC := by
    constructor
    · intro a b hab
      exact mul_injective_of_disjoint hBDdis (congrArg Subtype.val hab)
    · intro c
      obtain ⟨y, hy⟩ := (show (c : S) ∈ f.range from hfrange.symm ▸ c.property)
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨(MulEquiv.ofBijective fC hf).symm.trans (MulEquiv.prodCongr eB eD)⟩

/-- An order-eight closure in the separated local setup has involution
centralizer `C₂ × D₈`. The moving-plane splitting and the order of its fixed
factor are consequences of the local hypotheses, not additional assumptions. -/
public theorem centralizer_model
    (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8) :
    Nonempty (centralizer ({i} : Set S) ≃*
      (Multiplicative (ZMod 2) × DihedralGroup 4)) := by
  obtain ⟨s⟩ := nonempty_localSplitting hN S W hW z hzW hzC hz i hiW hi hiC hno d hc
  exact centralizer_model_of_localSplitting hW z hzW hzC hz i hiW hi hiC d s
    (fixed_card_of_localSplitting S W hW hZ z hzW hzC hz i hiW hi hiC hno d hc s)

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
