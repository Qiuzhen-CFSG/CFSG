module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Source rigidity for the nonsplit Aut(M₁₂) core

The third invariant-core alternative is the literal nonsplit preimage
`C₄ × E₄`.  Its quotient by the marked central involution is elementary of
order eight, but the preimage itself is not elementary.  The square map on
that quotient is a nonzero functional.  This file proves the finite
functional-stabilizer bound directly by the action on the four points outside
its kernel, and then performs the quotient-kernel and cardinality argument
from the source centralizer chain.

The first two alternatives still use the compatible residual movement
contracts in `SourceCoreAction`; this extension leaves those concrete
embeddings as explicit inputs for the source assembly.

Source: Aschbacher--Smith, Lemma 14.2.21, printed pp. 988--989
(`refs/quasithin.pdf`, PDF p. 1005).
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceRigidity

open Subgroup
open scoped IsMulCommutative commutatorElement

private def outsidePermutation
    {E : Type*} [Group E] (K : Subgroup E)
    (A : Subgroup (MulAut E))
    (hstable : ∀ a : A, ∀ x : E, (a : MulAut E) x ∈ K ↔ x ∈ K) :
    A →* Equiv.Perm {x : E // x ∉ K} where
  toFun a := {
    toFun := fun x => ⟨a.val x.val, by
      intro hx
      exact x.property ((hstable a x.val).mp hx)⟩
    invFun := fun x => ⟨(a⁻¹ : A).val x.val, by
      intro hx
      exact x.property ((hstable a⁻¹ x.val).mp hx)⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

private theorem outsidePermutation_injective
    {E : Type*} [Group E] [IsMulCommutative E]
    (K : Subgroup E) (A : Subgroup (MulAut E))
    (hstable : ∀ a : A, ∀ x : E, (a : MulAut E) x ∈ K ↔ x ∈ K)
    (c : E) (hc : c ∉ K) :
    Function.Injective (outsidePermutation K A hstable) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  by_cases hx : x ∈ K
  · have hxc : x * c ∉ K := by
      intro h
      exact hc (by
        simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem hx) h)
    have hc' : (a : MulAut E) c = (b : MulAut E) c := by
      exact congrArg (fun p : Equiv.Perm {x : E // x ∉ K} =>
        (p ⟨c, hc⟩).val) hab
    have hxc' : (a : MulAut E) (x * c) = (b : MulAut E) (x * c) := by
      exact congrArg (fun p : Equiv.Perm {x : E // x ∉ K} =>
        (p ⟨x * c, hxc⟩).val) hab
    rw [map_mul, map_mul, hc'] at hxc'
    exact mul_right_cancel hxc'
  · exact congrArg (fun p : Equiv.Perm {x : E // x ∉ K} =>
      (p ⟨x, hx⟩).val) hab

/-- A functional stabilizer on an elementary eight has order at most 24.
The proof is the functional/plane stabilizer calculation: the stabilizer
preserves the kernel of the functional and acts faithfully on the four points
outside that kernel. -/
public theorem functional_stabilizer_card_le_twentyfour
    {E C : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group C] (s : E →* C) (hsurj : Function.Surjective s)
    (hE : Nat.card E = 8) (hC : Nat.card C = 2)
    (A : Subgroup (MulAut E))
    (hstable : ∀ a : A, ∀ x : E, s ((a : MulAut E) x) = s x) :
    Nat.card A ≤ 24 := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  have hindex : s.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, hC]
  have hker : Nat.card s.ker = 4 := by
    have h := s.ker.card_mul_index
    rw [hindex, hE] at h
    omega
  let X := {x : E // x ∉ s.ker}
  have hX : Nat.card X = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE, hker]
  have hXpos : 0 < Nat.card X := by rw [hX]; decide
  obtain ⟨c, hc⟩ : ∃ c : E, c ∉ s.ker := by
    obtain ⟨c⟩ := (Nat.card_pos_iff.mp hXpos).1
    exact ⟨c.val, c.property⟩
  let r := outsidePermutation s.ker A (by
    intro a x
    change s ((a : MulAut E) x) = 1 ↔ s x = 1
    rw [hstable])
  have hr : Function.Injective r :=
    outsidePermutation_injective s.ker A (by
      intro a x
      change s ((a : MulAut E) x) = 1 ↔ s x = 1
      rw [hstable]) c hc
  have hcard := Nat.card_le_card_of_injective r hr
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm X), Fintype.card_perm,
    ← Nat.card_eq_fintype_card, hX] at hcard
  exact hcard

/-- The source centralizer chain gives faithfulness of the actual quotient
conjugation action.  The proof transports the kernel through the quotient:
trivial action puts every commutator in `Z`, the chain puts the represented
element in the image of `Q/Z`, and `Z ≤ Q` puts the original element in `Q`. -/
public theorem quotient_action_injective_of_source_chain
    {D : Type*} [Group D] [Finite D]
    (Q Z : Subgroup D) [Q.Normal] [Z.Normal]
    (hZQ : Z ≤ Q)
    (ρ : D ⧸ Q →* MulAut (Q ⧸ Z.subgroupOf Q))
    (happly : ∀ d : D, ∀ q : Q,
      ρ (QuotientGroup.mk' Q d) (QuotientGroup.mk' (Z.subgroupOf Q) q) =
        QuotientGroup.mk' (Z.subgroupOf Q)
          ⟨d * (q : D) * d⁻¹,
            (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩)
    (hchain : Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z)) :
    Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Q x
  have hcomm : ∀ q : Q, d * (q : D) * d⁻¹ * (q : D)⁻¹ ∈ Z := by
    intro q
    have heq : QuotientGroup.mk' (Z.subgroupOf Q)
        ⟨d * (q : D) * d⁻¹,
          (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩ =
        QuotientGroup.mk' (Z.subgroupOf Q) q := by
      rw [← happly d q]
      exact congrArg (fun a : MulAut (Q ⧸ Z.subgroupOf Q) =>
        a (QuotientGroup.mk' (Z.subgroupOf Q) q)) (MonoidHom.mem_ker.mp hx)
    have hdiv := (QuotientGroup.eq_iff_div_mem).mp heq
    change d * (q : D) * d⁻¹ * (q : D)⁻¹ ∈ Z
    have hdiv' := hdiv
    change ((⟨d * (q : D) * d⁻¹,
      (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩ : Q) / q : Q).val ∈ Z at hdiv'
    simpa [div_eq_mul_inv] using hdiv'
  have hcentral : (QuotientGroup.mk' Z) d ∈
      Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hq' : QuotientGroup.mk' Z (d * (q : D) * d⁻¹) =
        QuotientGroup.mk' Z (q : D) := by
      apply (QuotientGroup.eq_iff_div_mem).2
      simpa [div_eq_mul_inv] using hcomm ⟨q, hq⟩
    have he : QuotientGroup.mk' Z d * QuotientGroup.mk' Z (q : D) *
        (QuotientGroup.mk' Z d)⁻¹ = QuotientGroup.mk' Z (q : D) := by
      simpa only [map_mul, map_inv] using hq'
    change QuotientGroup.mk' Z (q : D) * QuotientGroup.mk' Z d =
      QuotientGroup.mk' Z d * QuotientGroup.mk' Z (q : D)
    calc
      QuotientGroup.mk' Z (q : D) * QuotientGroup.mk' Z d =
          (QuotientGroup.mk' Z d * QuotientGroup.mk' Z (q : D) *
            (QuotientGroup.mk' Z d)⁻¹) * QuotientGroup.mk' Z d := by
              rw [he]
      _ = QuotientGroup.mk' Z d * QuotientGroup.mk' Z (q : D) := by
        simp [mul_assoc]
  obtain ⟨q, hq, hdq⟩ := hchain hcentral
  have hz : d / q ∈ Z := (QuotientGroup.eq_iff_div_mem).mp hdq.symm
  have hdqQ : d / q ∈ Q := hZQ hz
  have hdQ : d ∈ Q := by
    simpa [div_eq_mul_inv] using Q.mul_mem hdqQ hq
  exact (QuotientGroup.eq_one_iff d).2 hdQ

/-- Construct the literal conjugation action on `Q/Z` from the two normality
hypotheses.  The displayed formula is the source action before its quotient
by `Q`; this is the map to which `QuotientGroup.lift` is applied in the
nonsplit branch. -/
public theorem actual_quotient_conjugation_action
    {D : Type*} [Group D]
    (Q Z : Subgroup D) [Q.Normal] [Z.Normal]
    [IsMulCommutative (Q ⧸ Z.subgroupOf Q)] :
    ∃ θ : D →* MulAut (Q ⧸ Z.subgroupOf Q),
      ∀ d : D, ∀ q : Q,
        θ d (QuotientGroup.mk' (Z.subgroupOf Q) q) =
          QuotientGroup.mk' (Z.subgroupOf Q)
            ⟨d * (q : D) * d⁻¹,
              (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩ := by
  have hDQ : (⊤ : Subgroup D) ≤ Subgroup.normalizer (Q : Set D) := by
    rw [Subgroup.normalizer_eq_top]
  have hDZ : (⊤ : Subgroup D) ≤ Subgroup.normalizer (Z : Set D) := by
    rw [Subgroup.normalizer_eq_top]
  obtain ⟨θ₀, hθ₀⟩ := Subgroup.exists_quotient_conjugation_action
    (⊤ : Subgroup D) Q Z hDQ hDZ (inferInstance : (Z.subgroupOf Q).Normal)
  refine ⟨θ₀.comp (Subgroup.topEquiv.symm : D ≃* (⊤ : Subgroup D)), ?_⟩
  intro d q
  change θ₀ (⟨d, trivial⟩ : (⊤ : Subgroup D))
      (QuotientGroup.mk' (Z.subgroupOf Q) q) = _
  exact hθ₀ ⟨d, trivial⟩ q

/-- The normality action descends through `D/Q` when `Q/Z` is abelian.
The kernel proof is the commutator calculation, so the quotient actor is
constructed rather than supplied as an abstract action. -/
public theorem quotient_conjugation_action_of_normal
    {D : Type*} [Group D]
    (Q Z : Subgroup D) [Q.Normal] [Z.Normal]
    [IsMulCommutative (Q ⧸ Z.subgroupOf Q)] :
    ∃ ρ : D ⧸ Q →* MulAut (Q ⧸ Z.subgroupOf Q),
      ∀ d : D, ∀ q : Q,
        ρ (QuotientGroup.mk' Q d) (QuotientGroup.mk' (Z.subgroupOf Q) q) =
          QuotientGroup.mk' (Z.subgroupOf Q)
            ⟨d * (q : D) * d⁻¹,
              (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩ := by
  obtain ⟨θ, hθ⟩ := actual_quotient_conjugation_action Q Z
  have hcomm : _root_.commutator Q ≤ Z.subgroupOf Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Z.subgroupOf Q)).mp inferInstance
  have hker : Q ≤ θ.ker := by
    intro q hq
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
    let q' : Q := ⟨q, hq⟩
    have hu : ⁅q', u⁆ ∈ Z.subgroupOf Q :=
      hcomm (Subgroup.commutator_mem_commutator (show q' ∈ (⊤ : Subgroup Q) from trivial)
        (show u ∈ (⊤ : Subgroup Q) from trivial))
    rw [hθ]
    apply (QuotientGroup.eq_iff_div_mem).2
    convert hu using 1
    apply Subtype.ext
    simp [q', commutatorElement_def, div_eq_mul_inv]
  let ρ := QuotientGroup.lift Q θ hker
  refine ⟨ρ, ?_⟩
  intro d q
  change (QuotientGroup.lift Q θ hker) (QuotientGroup.mk' Q d)
      (QuotientGroup.mk' (Z.subgroupOf Q) q) = _
  rw [show (QuotientGroup.lift Q θ hker) (QuotientGroup.mk' Q d) = θ d from
    QuotientGroup.lift_mk' Q hker d]
  exact hθ d q

/-! The nonsplit third branch.  The square functional is the only
finite-model input: its invariance bounds the actual quotient actor, and the
source centralizer chain makes that actor faithful. -/

public theorem nonsplit_third_branch_eq
    {D : Type*} [Group D] [Finite D]
    (H Q Z : Subgroup D) [Q.Normal] [Z.Normal]
    [IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q)]
    (hQH : Q ≤ H) (hZQ : Z ≤ Q)
    (hQcard : Nat.card Q = 16) (hHcard : Nat.card H = 384)
    (hEcard : Nat.card (Q ⧸ Z.subgroupOf Q) = 8)
    (hZcard : Nat.card Z = 2)
    (ρ : D ⧸ Q →* MulAut (Q ⧸ Z.subgroupOf Q))
    (happly : ∀ d : D, ∀ q : Q,
      ρ (QuotientGroup.mk' Q d) (QuotientGroup.mk' (Z.subgroupOf Q) q) =
        QuotientGroup.mk' (Z.subgroupOf Q)
          ⟨d * (q : D) * d⁻¹,
            (inferInstance : Q.Normal).conj_mem (q : D) q.property d⟩)
    (hchain : Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z))
    (s : (Q ⧸ Z.subgroupOf Q) →* Z.subgroupOf Q)
    (hsurj : Function.Surjective s)
    (hpres : ∀ a : D ⧸ Q, ∀ x : Q ⧸ Z.subgroupOf Q,
      s (ρ a x) = s x) :
    H = (⊤ : Subgroup D) := by
  classical
  let hρinj : Function.Injective ρ :=
    quotient_action_injective_of_source_chain Q Z hZQ ρ happly hchain
  have hZsubcard : Nat.card (Z.subgroupOf Q) = 2 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv).trans hZcard
  have hρcard : Nat.card ρ.range = Nat.card (D ⧸ Q) := by
    have hker : ρ.ker = (⊥ : Subgroup (D ⧸ Q)) :=
      (MonoidHom.ker_eq_bot_iff ρ).2 hρinj
    let e₀ : D ⧸ Q ≃* (D ⧸ Q) ⧸ ρ.ker :=
      (QuotientGroup.quotientBot).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker).symm
    let e : D ⧸ Q ≃* ρ.range :=
      e₀.trans (QuotientGroup.quotientKerEquivRange ρ)
    exact (Nat.card_congr e.toEquiv).symm
  have hstable : ∀ a : ρ.range, ∀ x : Q ⧸ Z.subgroupOf Q,
      s (a.1 x) = s x := by
    rintro ⟨a, ⟨b, rfl⟩⟩ x
    exact hpres b x
  have hquot_le : Nat.card (D ⧸ Q) ≤ 24 := by
    have hstab := functional_stabilizer_card_le_twentyfour s hsurj
      hEcard hZsubcard ρ.range hstable
    rw [hρcard] at hstab
    exact hstab
  let qmap : D →* D ⧸ Q := QuotientGroup.mk' Q
  let S : Subgroup (D ⧸ Q) := H.map qmap
  have hQsubcard : Nat.card (Q.subgroupOf H) = 16 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv).trans hQcard
  have hindex : (Q.subgroupOf H).index = Nat.card S := by
    simpa only [qmap, QuotientGroup.ker_mk', Subgroup.relIndex] using
      (Subgroup.relIndex_ker H qmap)
  have hScard : Nat.card S = 24 := by
    have hmul := (Q.subgroupOf H).card_mul_index
    rw [hQsubcard, hindex, hHcard] at hmul
    omega
  have htopcard : Nat.card (D ⧸ Q) = 24 := by
    have hmul := S.card_mul_index
    rw [hScard] at hmul
    have hle := hquot_le
    have hidxne : S.index ≠ 0 := by
      intro hzero
      have hzero' : Nat.card (D ⧸ Q) = 0 := by
        simpa [hzero] using hmul.symm
      exact (Nat.card_pos (α := D ⧸ Q)).ne' hzero'
    have hidxpos : 0 < S.index := Nat.pos_of_ne_zero hidxne
    omega
  have hStop : S = (⊤ : Subgroup (D ⧸ Q)) := by
    apply Subgroup.eq_top_of_card_eq
    simpa [htopcard] using hScard
  have hkerQ : qmap.ker ≤ H := by
    change (QuotientGroup.mk' Q).ker ≤ H
    rw [QuotientGroup.ker_mk']
    exact hQH
  have hcomap : Subgroup.comap qmap S = H :=
    Subgroup.comap_map_eq_self hkerQ
  have hcomaptop : Subgroup.comap qmap (⊤ : Subgroup (D ⧸ Q)) = ⊤ := by
    exact Subgroup.comap_top qmap
  have hHtop : H = (⊤ : Subgroup D) := by
    rw [← hcomap, hStop, hcomaptop]
  exact hHtop

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceRigidity
