module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OutsideSelection.Reduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentSupplementPrimeCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.Quasithin.Rank

/-!
# The initial quasisimple overgroup in the proof of 1.3.8

For H = ⟨K,T⟩ with K in the genuine local C-component family, the actual
image of K in H/O₂(H) is isomorphic to K/O₂(K). If this quotient is
quasisimple and its center has order prime to p, the component-supplement
argument gives Oₚ(H/O₂(H)) = 1, even when T permutes the components.

The noncyclic odd quotient of X then prevents X from being normal in H.
Since M = N_G(X), this proves H ≰ M. All normality used in this argument is
relative to H; nonnormality of X is derived, rather than assumed.

The last theorem assembles this argument from the genuine universal A.3.6
implication. Its common conclusions imply |Z(K/O₂(K))| = 1 or 3 in the
quasisimple case, and p > 3 excludes both. A.3.6 remains an explicit
prerequisite: the arbitrary group-class parameter alone does not identify
its simple sections with the known catalogue. Consequently this module
provides a conditional reduction, not the unconditional 1.3.8 source step.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, pp.513–514; Proposition 1.3.4, pp.509–510; the
quasisimple branch and common assertions of A.3.6, pp.43–44, whose center
bound uses the multiplier list I.1.3.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding
universe u

/-- The actual image of the local C-component in the two-core quotient. -/
noncomputable def initialComponentQuotientEquiv {G : Type*} [Group G] [Finite G]
    {T K : Subgroup G} (hK : K ∈ Chapter1.L G T) :
    XiQuotient K ≃* (K.subgroupOf (K ⊔ T)).map (QuotientGroup.mk' (pCore 2 (K ⊔ T : Subgroup G))) := by
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ T from le_sup_left)
  exact (QuotientGroup.congr (pCore 2 (K.subgroupOf (K ⊔ T)))
    (pCore 2 K) e (pCore_map_iso 2 e)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.1)

/-- The intrinsic component center bound kills the overgroup's odd core,
including the case that T permutes the C-components. -/
theorem initial_quotient_pCore_eq_bot_of_center_primeFree
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T K : Subgroup G} (hp : Odd p) (hK : K ∈ Chapter1.L G T)
    (hq : IsQuasisimple (XiQuotient K))
    (hz : ¬ p ∣ Nat.card (center (XiQuotient K))) :
    pCore p (XiQuotient (K ⊔ T)) = ⊥ := by
  let H := K ⊔ T
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.subgroupOf H
  let C := B.map q
  let S := (T.subgroupOf H).map q
  let e : XiQuotient K ≃* C := initialComponentQuotientEquiv hK
  let _ := hq
  have hC : IsComponent (XiQuotient H) C :=
    ⟨hK.1.subnormal.map (QuotientGroup.mk'_surjective _), IsQuasisimple.of_mulEquiv e⟩
  have hS : IsPGroup 2 S := (isSylowIn_iff.mp hK.2.1).1.comap_subtype.map q
  have hgen : C ⊔ S = ⊤ := by
    dsimp only [C, S, B]
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pCore 2 H))
  have hc : ¬ p ∣ Nat.card (center C) := by
    rw [← Nat.card_congr (centerCongr e).toEquiv]
    exact hz
  exact pCore_eq_bot_of_component_two_supplement hp hC hS hgen hc

/-- The initial overgroup lies outside M once the source's center bound is
supplied. This is a conditional reduction, not the full source theorem. -/
theorem Configuration.initial_not_le_of_center_primeFree
    {G : Type*} [Group G] [Finite G] {p : ℕ} {T X P L₀ M K : Subgroup G}
    (h : Configuration p T X P L₀ M) (hK : K ∈ Chapter1.L G T)
    (hq : IsQuasisimple (XiQuotient K)) (hXT : X ⊔ T ≤ K ⊔ T)
    (hz : ¬ p ∣ Nat.card (center (XiQuotient K))) : ¬ K ⊔ T ≤ M := by
  intro hHM
  let _ : Fact p.Prime := ⟨h.prime⟩
  have hcore := initial_quotient_pCore_eq_bot_of_center_primeFree h.odd hK hq hz
  have hcyc : IsCyclic (pCore p (XiQuotient (K ⊔ T))) := by
    rw [hcore]
    infer_instance
  exact not_normal_of_cyclic_quotient_pCore h.quotient (le_sup_left.trans hXT) hcyc
    (normal_subgroupOf_of_le_normalizer (hHM.trans h.normalizer_radical.le))

/-- In the quasisimple branch, the common A.3.6 conclusions force the
center to have order one or three; its F* = F alternative is impossible. -/
theorem center_card_of_quasisimple_A36Common
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hc : Section02.A36Common Q) :
    Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 3 := by
  rcases hc.2.2.1 with h | h
  · have ht : generalizedFitting Q = ⊤ := by
      apply top_unique
      apply component_le_generalizedFitting
      exact ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
    have hf : fittingSubgroup Q = ⊤ := h.1.trans ht
    have hs : Group.IsSolvable Q := Group.isSolvable_of_surjective
      (f := (fittingSubgroup Q).subtype) (by rw [hf]; exact topEquiv.surjective)
    let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
    let _ : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
    exact (Group.IsPerfect.not_isSolvable Q hs).elim
  · simpa only [h.1] using h.2.2

/-- Assembly from the genuine universal earlier A.3.6 implication. That
implication remains an explicit prerequisite; SQTK with an arbitrary class κ
does not supply a classification of its quasisimple sections. -/
theorem Configuration.initial_not_le_of_A36
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK κ A → pCore 2 A = ⊥ → ∀ C : Subgroup A,
      C.IsCComponent → Section02.A36Conclusion C)
    {p : ℕ} {T X P L₀ M K : Subgroup G}
    (h : Configuration p T X P L₀ M) (hK : K ∈ Chapter1.L G T)
    (hq : IsQuasisimple (XiQuotient K)) (hXT : X ⊔ T ≤ K ⊔ T) :
    ¬ K ⊔ T ≤ M := by
  have hH : IsSQTK κ (K ⊔ T : Subgroup G) := sqtk_of_mem_H hG hK.2.2
  have hQ : IsSQTK κ (XiQuotient (K ⊔ T)) := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro r hr ho
    let _ : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin r hr ho)
  let B := K.subgroupOf (K ⊔ T)
  let C := B.map (QuotientGroup.mk' (pCore 2 (K ⊔ T : Subgroup G)))
  let e : XiQuotient K ≃* C := initialComponentQuotientEquiv hK
  let _ := hq
  let _ : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
  let _ : Group.IsNilpotent (pCore 2 (K ⊔ T : Subgroup G)) := pCore_isNilpotent
  have hc : Section02.A36Common C :=
    (hA36 _ hQ (pCore_quotient_pCore_eq_bot 2) C (hK.1.map_quotient _)).2
  have hz := center_card_of_quasisimple_A36Common hc
  rw [← Nat.card_congr (centerCongr e).toEquiv] at hz
  apply Configuration.initial_not_le_of_center_primeFree h hK hq hXT
  rcases hz with hz | hz
  · rw [hz]
    exact h.prime.not_dvd_one
  · rw [hz]
    intro hd
    have hp := Nat.le_of_dvd (by decide : 0 < 3) hd
    have := h.large
    omega

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
