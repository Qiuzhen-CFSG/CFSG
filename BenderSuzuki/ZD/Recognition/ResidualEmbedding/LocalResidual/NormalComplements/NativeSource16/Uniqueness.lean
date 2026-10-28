module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Roots

/-!
# Uniqueness in the marked-root centralizer

For a maximal distinguished trace Γ, a four-group W centralizing the
root ⟨Γ,t⟩ has exactly the same trace at each nonidentity element. The
actual local-circle calculation puts every [C_K(w),t] in ⟨Γ,t⟩. Four-centralizer
generation then puts K there, contradicting the original generation theorem.
The centralizer of the root therefore has no involution other than u.

Source: GLS IV, Chapter 2, Lemma 16.4(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The maximal trace centralizer contains no elementary four. This uses
original minimality, action and generation, with no model-containment premise. -/
public theorem source16_no_four_centralizing_marked_root
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (_huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t)
    (hWt : W ≤ centralizer ({t} : Set G))
    (hWΓ : W ≤ centralizer (residualCentralizerTrace Z M u)) : False := by
  have hrank : TwoRankAtLeastTwo (residualPairStabilizer M t) := by
    refine ⟨W.subgroupOf (residualPairStabilizer M t), ?_, ?_⟩
    · rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv]
      exact hW
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian x.val.val x.property
  have hΓB : closure (residualCentralizerTrace Z M u) ≤ centralizer ({u} : Set G) := by
    apply (closure_le _).mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mpr hx.2.2.eq
  have hzΓ : z ∈ residualCentralizerTrace Z M u := ⟨hz,hzM,hzu⟩
  have hK : residualCommutator M t ≤ closure (residualCentralizerTrace Z M u) ⊔ zpowers t := by
    rw [residualPair_four_generation h.disconnected ht htM W hW hWD hWt]
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hwi : PFAppendixIII.IsInvolution (w : G) :=
      ⟨hw, elemPow_eq_one_of_isElementaryAbelian (w : G) w.property⟩
    have hzw : Commute z (w : G) := hWΓ w.property z hzΓ
    have htw : Commute t (w : G) := (mem_centralizer_singleton_iff.mp (hWt w.property)).symm
    have hwC := residualInvolution_centralizer_not_le h.disconnected r ht htM hwi (hWD w.property)
    have hns := involutionCentralizer_circle_nonsolvable_of_pair_twoRank
      h r ha ht htM hrank hwi (hWD w.property).1 hwC
    have htrace : residualCentralizerTrace Z M u = residualCentralizerTrace Z M w := by
      apply residualCentralizerTrace_eq_of_maximal hmax (hWD w.property) hwi
      intro x hx
      exact ⟨hx.1,hx.2.1,hWΓ w.property x hx⟩
    rw [htrace]
    exact source16_fixed_commutator_le_trace_root h r ha hz hzM ht htM hwi hzw htw hns
  exact residualCommutator_not_le_involution_centralizer h.disconnected r hg hz hzM ht htM
    hu hzu htu (hK.trans (sup_le hΓB (zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr htu.eq))))

private theorem involution_zpowers_cases {u v : G}
    (hu : PFAppendixIII.IsInvolution u) (hv : v ∈ zpowers u) : v = 1 ∨ v = u := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hu.sq_eq_one hu.ne_one] at hv
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hv
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

/-- Lemma 16.4(a), at the literal maximal marked root. The selected u is
central in B, so any different involution would give the excluded four. -/
public theorem source16_unique_involution_marked_root_centralizer
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    {v : G} (hv : PFAppendixIII.IsInvolution v)
    (hvu : Commute v u)
    (hvroot : v ∈ centralizer
      (closure (residualCentralizerTrace Z M u) ⊔ zpowers t : Subgroup G)) : v = u := by
  by_contra hne
  let R := closure (residualCentralizerTrace Z M u) ⊔ zpowers t
  have huroot : u ∈ centralizer (R : Set G) := by
    rw [mem_centralizer_iff]
    have hh : R ≤ centralizer ({u} : Set G) := sup_le
      ((closure_le _).mpr (fun x hx => mem_centralizer_singleton_iff.mpr hx.2.2.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htu.eq))
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hh hx)
  have hzR : z ∈ R := (show closure (residualCentralizerTrace Z M u) ≤ R from le_sup_left)
    (subset_closure ⟨hz,hzM,hzu⟩)
  have htR : t ∈ R := (show zpowers t ≤ R from le_sup_right) (mem_zpowers t)
  have hvM : v ∈ M := h.disconnected.centralizer_le hz hzM
    (mem_centralizer_singleton_iff.mpr (hvroot z hzR).symm)
  have hvt : Commute v t := (hvroot t htR).symm
  have hvD : v ∈ residualPairStabilizer M t := by
    refine ⟨hvM, v, hvM, ?_⟩
    change t⁻¹ * v * (t⁻¹)⁻¹ = v
    rw [(h.disconnected.involutions t ht).inv_eq_self]
    rw [hvt.symm.eq, mul_inv_cancel_right]
  let W := zpowers u ⊔ zpowers v
  let : IsElementaryAbelian 2 (zpowers u) := IsElementaryAbelian.zpowers_of_pow_eq_one hu.sq_eq_one
  let : IsElementaryAbelian 2 (zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hv.sq_eq_one
  have hvCu : v ∈ centralizer (zpowers u : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp
      ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hvu.symm.eq)) hx)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hvCu)
  have hW : Nat.card W = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers u) v hv.sq_eq_one
      (fun hh => (involution_zpowers_cases hu hh).elim hv.ne_one hne)
      (Subgroup.centralizer_le_normalizer _ hvCu), Nat.card_zpowers,
      orderOf_eq_prime hu.sq_eq_one hu.ne_one]
  have hWroot : W ≤ centralizer (R : Set G) :=
    sup_le (zpowers_le.mpr huroot) (zpowers_le.mpr hvroot)
  exact source16_no_four_centralizing_marked_root h r ha hg hz hzM ht htM hu huD hzu htu hmax
    W hW (sup_le (zpowers_le.mpr huD) (zpowers_le.mpr hvD))
    (fun w hw => mem_centralizer_singleton_iff.mpr (hWroot hw t htR).symm)
    (fun w hw x hx => hWroot hw x ((show closure (residualCentralizerTrace Z M u) ≤ R from le_sup_left)
      (subset_closure hx)))

end BenderSuzuki.ZD
