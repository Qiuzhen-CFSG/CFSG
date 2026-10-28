module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Odd divisibility and perfect sections in modified residuals

A finite surjection carries each prime residual onto the target residual.
A perfect subgroup lies in every prime residual. Combining these facts with
the genuine fixed-group comparison across the central two-kernel preserves
a perfect section through both operations in Notation 16.5.5. Separately,
two-kernels preserve arbitrary odd divisibility, including powers of three.

The marked-actor transport identifies a projected inner action with a literal
involution of the specified quotient model, preserving its Sylow-center mark.
These are the comparison steps for the J4 and Ru rows in the proof of
Aschbacher–Smith 16.5.6(4), printed p.1197, using 16.1.5(9),(11), p.1172.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.Intersections
open CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
open SylowSymmetry.ReverseDelta.Comparison
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis

private theorem perfect_residual_top {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (p : ℕ) [Fact p.Prime] : pResidual p P = ⊤ := by
  apply (pResidual_eq_top_iff p P).mpr
  intro N hN hp
  let := hN
  have hs : Subsingleton (P ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

private def residualMap {A B : Type*} [Group A] [Group B] (p : ℕ)
    (f : A →* B) : pResidual p A →* pResidual p B :=
  (f.comp (pResidual p A).subtype).codRestrict _ fun x =>
    map_pResidual_le p f (mem_map_of_mem f x.property)

private theorem residualMap_surjective {A B : Type*} [Group A] [Group B]
    [Finite A] (p : ℕ) (f : A →* B) (hf : Function.Surjective f) :
    Function.Surjective (residualMap p f) := by
  intro y
  have hy : y.val ∈ (pResidual p A).map f := by
    rw [map_pResidual_of_surjective p f hf]
    exact y.property
  obtain ⟨x, hx, he⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

private def perfectIntoResidual {P Q : Type*} [Group P] [Group Q]
    [Finite P] [Group.IsPerfect P] (p : ℕ) [Fact p.Prime] (j : P →* Q) :
    P →* pResidual p Q :=
  j.codRestrict _ fun x => map_pResidual_le p j
    (mem_map_of_mem j (by rw [perfect_residual_top p]; trivial))

private theorem perfectIntoResidual_injective {P Q : Type*} [Group P] [Group Q]
    [Finite P] [Group.IsPerfect P] (p : ℕ) [Fact p.Prime] (j : P →* Q)
    (hj : Function.Injective j) : Function.Injective (perfectIntoResidual p j) :=
  fun _ _ h => hj (congrArg Subtype.val h)

/-- A short exact sequence gives its order without a splitting assumption. -/
theorem extension_card {K C Q : Type*} [Group K] [Group C] [Group Q]
    (d : GroupExtension K C Q) : Nat.card C = Nat.card Q * Nat.card K := by
  rw [card_eq_card_quotient_mul_card_subgroup d.rightHom.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      d.rightHom_surjective).toEquiv, ← d.range_inl_eq_ker_rightHom,
    ← Nat.card_congr (MonoidHom.ofInjective d.inl_injective).toEquiv]

/-- Odd divisibility, including prime powers, survives the two-residual. -/
private theorem coprime_dvd_residual_iff {C : Type*} [Group C] [Finite C]
    (p n : ℕ) [Fact p.Prime] (hn : Nat.Coprime n p) :
    n ∣ Nat.card (pResidual p C) ↔ n ∣ Nat.card C := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_quotient_pResidual (G := C) p)
  rw [← (pResidual p C).card_mul_index, index_eq_card, ha]
  exact (hn.pow_right a).dvd_mul_right.symm

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} [IsQuasisimple L]

/-- The two-kernels preserve all odd divisibility, including the cubic power
which distinguishes the two J4 rows. -/
theorem odd_dvd_twoResidual_iff_fixed (hodd : pPrimeCore 2 L = ⊥)
    {S : Type*} [Group S] [Finite S] (e : L ⧸ center L ≃* S)
    (u : normalizer (L : Set G)) (n : ℕ) (hn : Nat.Coprime n 2) :
    n ∣ Nat.card (involutionTwoResidual L u.val) ↔
      n ∣ Nat.card (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup := by
  obtain ⟨k, _, hk, he⟩ := twoResidual_card_factor hodd e u
  have hz : IsPGroup 2 (center L) := by
    rw [IsQuasisimple.center_eq_pCore hodd]
    exact pCore_isPGroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hz
  have hnk : Nat.Coprime n k := (hn.pow_right a).of_dvd_right (ha ▸ hk)
  rw [he, hnk.dvd_mul_left]
  exact coprime_dvd_residual_iff 2 n hn

/-- A genuine perfect section of the model fixed group survives both residual
operations upstairs. No perfectness of the upstairs residual is assumed. -/
theorem perfect_section_dvd_modified (hodd : pPrimeCore 2 L = ⊥)
    {S : Type*} [Group S] [Finite S] (e : L ⧸ center L ≃* S)
    (u : normalizer (L : Set G)) {Q P : Type*} [Group Q] [Group P]
    [Finite Q] [Finite P] [Group.IsPerfect P]
    (f : (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup →* Q)
    (hf : Function.Surjective f) (j : P →* Q) (hj : Function.Injective j) :
    Nat.card P ∣ Nat.card (modifiedCentralizerResidual L u.val) := by
  let hXL := (SylowSymmetry.ReverseDelta.residual_le L u.val).trans inf_le_left
  let b := centralImageModelEquiv hodd e u.property
  let g : involutionTwoResidual L u.val →* pResidual 2 Q :=
    (residualMap 2 f).comp (b.toMonoidHom.comp (centralImageMap hXL))
  have hg : Function.Surjective g :=
    (residualMap_surjective 2 f hf).comp
      (b.surjective.comp (centralImageMap_surjective hXL))
  let j2 := perfectIntoResidual 2 j
  have hj2 : Function.Injective j2 := perfectIntoResidual_injective 2 j hj
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [card_map_of_injective (subtype_injective _)]
    exact (card_dvd_of_injective (perfectIntoResidual 3 j2)
      (perfectIntoResidual_injective 3 j2 hj2)).trans
      (card_dvd_of_surjective _ (residualMap_surjective 3 g hg))
  · exact (card_dvd_of_injective j2 hj2).trans (card_dvd_of_surjective g hg)

/-- Innerness of involutory model automorphisms supplies a literal model
involution and transports exactly the Sylow-center mark on the projected actor. -/
theorem marked_model_involution {S : Type*} [Group S] [Finite S]
    (e : L ⧸ center L ≃* S)
    (hinner : ∀ a : MulAut S, orderOf a = 2 → ∃ x : S, a = MulAut.conj x)
    (u : normalizer (L : Set G))
    (hu : orderOf (actionMap (L := L) le_rfl u) = 2) :
    ∃ x : S, orderOf x = 2 ∧
      MulAut.centralQuotientAction e (L.normalizerMonoidHom u) = MulAut.conj x ∧
      (IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔ TwoCentral x) := by
  have ha : orderOf (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)) = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) _).trans
      ((action_order u).trans hu)
  obtain ⟨k, hk⟩ := (MulAut.centralQuotientAction_inner_iff e _).mp (hinner _ ha)
  let q := QuotientGroup.mk' (center L) k
  have he : (componentImageEquiv L q : ActionQuotient L) = actionMap (L := L) le_rfl u := by
    rw [componentImageEquiv_mk]
    apply actionHom_injective
    rw [actionHom_component, actionHom_actionMap, hk]
  have hq : orderOf q = 2 := by
    rw [← he, orderOf_submonoid, (componentImageEquiv L).orderOf_eq] at hu
    exact hu
  refine ⟨e q, (e.orderOf_eq q).trans hq, ?_, ?_⟩
  · rw [hk, MulAut.centralQuotientAction_conj]
  · rw [← he, twoCentral_componentImage_iff, hq]
    simp only [true_and]
    exact ⟨fun h => h.map e, fun h => by simpa only [e.symm_apply_apply] using h.map e.symm⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis
