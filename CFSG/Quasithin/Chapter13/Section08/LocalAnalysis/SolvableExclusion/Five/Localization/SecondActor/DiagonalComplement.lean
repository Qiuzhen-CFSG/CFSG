module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A complementary involution on two normalized five-factors

An elementary abelian two-subgroup E acts by conjugation on at most two
subgroups of order five. Suppose that the joint action is faithful, |E| > 2,
and an order-two subgroup U acts nontrivially on the first factor and
centralizes the others. Then there are exactly two factors, and
B = E ∩ C(Q₀) is an order-two direct complement to U, acting nontrivially
on the second factor.

The restricted normalizer homomorphism has the expected centralizer kernel.
Its nonidentity values all act by inversion, so a faithful restriction has
at most two actors. Multiplying by a noncentral element of U puts any actor
into B. Joint faithfulness then gives disjointness, excludes one factor,
and makes the second restriction faithful on B. No pairwise commutation
hypothesis on the five-factors is needed.

This is the conditional algebraic construction of the starred complement
in Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.13,
`refs/quasithin.pdf`, printed p.951 / PDF p.968. The source application must
supply factor normalization and faithfulness and lift B to the original group.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor.DiagonalComplement
variable {K : Type*} [Group K] [Finite K]

private def restriction (E Q : Subgroup K) (hn : E ≤ normalizer (Q : Set K)) :
    E →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hn)

omit [Finite K] in
private theorem restriction_eq_one (E Q : Subgroup K)
    (hn : E ≤ normalizer (Q : Set K)) (x : E) :
    restriction E Q hn x = 1 ↔ (x : K) ∈ centralizer (Q : Set K) := by
  constructor
  · intro h y hy
    have he := congrArg Subtype.val (congrArg (fun f : MulAut Q => f ⟨y, hy⟩) h)
    change (x : K) * y * (x : K)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    ext y
    change (x : K) * (y : K) * (x : K)⁻¹ = (y : K)
    rw [← h y y.property, mul_inv_cancel_right]

private theorem restriction_nontrivial_unique (E Q : Subgroup K)
    (hp : (Nat.card Q).Prime) (hsq : ∀ x ∈ E, x ^ 2 = 1)
    (hn : E ≤ normalizer (Q : Set K)) (x y : E)
    (hx : restriction E Q hn x ≠ 1) (hy : restriction E Q hn y ≠ 1) :
    restriction E Q hn x = restriction E Q hn y := by
  have hinv (z : E) (hz : restriction E Q hn z ≠ 1) :
      ∀ q ∈ Q, (z : K) * q * (z : K)⁻¹ = q⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one Q hp z
      (hsq z z.property) (hn z.property) with hc | hi
    · exact False.elim (hz ((restriction_eq_one E Q hn z).mpr
        (fun q hq => (hc q hq).symm)))
    · exact hi
  ext q
  exact (hinv x hx q q.property).trans (hinv y hy q q.property).symm

private theorem faithful_card_le_two (E Q : Subgroup K)
    (hp : (Nat.card Q).Prime) (hsq : ∀ x ∈ E, x ^ 2 = 1)
    (hn : E ≤ normalizer (Q : Set K))
    (hfaith : E ⊓ centralizer (Q : Set K) = ⊥) : Nat.card E ≤ 2 := by
  classical
  let f := restriction E Q hn
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    have hc := (restriction_eq_one E Q hn x).mp hx
    have hm : (x : K) ∈ E ⊓ centralizer (Q : Set K) := ⟨x.property, hc⟩
    simpa only [hfaith, mem_bot, Subgroup.coe_one] using hm
  let b : E → Bool := fun x => decide (f x = 1)
  have hb : Function.Injective b := by
    intro x y h
    apply hf
    have he : f x = 1 ↔ f y = 1 := decide_eq_decide.mp h
    by_cases hx : f x = 1
    · exact hx.trans (he.mp hx).symm
    · exact restriction_nontrivial_unique E Q hp hsq hn x y hx
        (fun hy => hx (he.mpr hy))
  simpa using Nat.card_le_card_of_injective b hb

omit [Finite K] in
private theorem joint_kernel_eq_bot {s : ℕ} (Q : Fin s → Subgroup K)
    (E D : Subgroup K) (hDE : D ≤ E)
    (hfaith : E ⊓ centralizer ((⨆ i, Q i : Subgroup K) : Set K) = ⊥)
    (hc : ∀ i, D ≤ centralizer (Q i : Set K)) : D = ⊥ := by
  have hcs : D ≤ centralizer ((⨆ i, Q i : Subgroup K) : Set K) :=
    le_centralizer_iff.mpr (iSup_le fun i => le_centralizer_iff.mp (hc i))
  exact le_antisymm ((le_inf hDE hcs).trans hfaith.le) bot_le

/-- Construct the complementary order-two subgroup on the second factor.
The count, the complement, its order and both action clauses are conclusions;
normalization and joint faithfulness are the explicit algebraic inputs. -/
public theorem exists_complement {s : ℕ} (hspos : 0 < s) (hsle : s ≤ 2)
    (Q : Fin s → Subgroup K) (hQ : ∀ i, Nat.card (Q i) = 5)
    (E U : Subgroup K) [IsElementaryAbelian 2 E]
    (hUE : U ≤ E) (hU : Nat.card U = 2) (hE : 2 < Nat.card E)
    (hn : ∀ i, E ≤ normalizer (Q i : Set K))
    (hfaith : E ⊓ centralizer ((⨆ i, Q i : Subgroup K) : Set K) = ⊥)
    (hfirst : ⁅U, Q ⟨0, hspos⟩⁆ ≠ ⊥)
    (hrest : ∀ i : Fin s, i.val ≠ 0 → ⁅U, Q i⁆ = ⊥) :
    s = 2 ∧ ∃ (i : Fin s) (B : Subgroup K), i.val ≠ 0 ∧ B ≤ E ∧
      Nat.card B = 2 ∧ E = U ⊔ B ∧ Disjoint U B ∧ ⁅U, B⁆ = ⊥ ∧
      ⁅B, Q ⟨0, hspos⟩⁆ = ⊥ ∧ ⁅B, Q i⁆ ≠ ⊥ := by
  classical
  let z : Fin s := ⟨0, hspos⟩
  have hp (i : Fin s) : (Nat.card (Q i)).Prime := by rw [hQ]; decide
  have hsq : ∀ x ∈ E, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian x hx
  let B : Subgroup K := E ⊓ centralizer (Q z : Set K)
  have hBE : B ≤ E := inf_le_left
  have hBC : B ≤ centralizer (Q z : Set K) := inf_le_right
  have hu : ¬ U ≤ centralizer (Q z : Set K) :=
    fun h => hfirst (commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨u, huU, huC⟩ := Set.not_subset.mp hu
  let uE : E := ⟨u, hUE huU⟩
  let f := restriction E (Q z) (hn z)
  have hfu : f uE ≠ 1 := fun h => huC ((restriction_eq_one E (Q z) (hn z) uE).mp h)
  have hprod : E = U ⊔ B := by
    apply le_antisymm _ (sup_le hUE hBE)
    intro x hx
    by_cases hc : x ∈ centralizer (Q z : Set K)
    · exact (show B ≤ U ⊔ B from le_sup_right) ⟨hx, hc⟩
    · have hfx : f ⟨x, hx⟩ ≠ 1 := fun h =>
        hc ((restriction_eq_one E (Q z) (hn z) ⟨x, hx⟩).mp h)
      have heq := restriction_nontrivial_unique E (Q z) (hp z) hsq (hn z)
        uE ⟨x, hx⟩ hfu hfx
      have hker : f (uE⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, heq, inv_mul_cancel]
      have hb : u⁻¹ * x ∈ B := ⟨E.mul_mem (E.inv_mem (hUE huU)) hx,
        (restriction_eq_one E (Q z) (hn z) (uE⁻¹ * ⟨x, hx⟩)).mp hker⟩
      simpa only [mul_inv_cancel_left] using (U ⊔ B).mul_mem
        ((show U ≤ U ⊔ B from le_sup_left) huU)
        ((show B ≤ U ⊔ B from le_sup_right) hb)
  have hdisj : Disjoint U B := by
    apply disjoint_iff.mpr
    apply joint_kernel_eq_bot Q E (U ⊓ B) (inf_le_left.trans hUE) hfaith
    intro i
    by_cases hi : i.val = 0
    · have hiz : i = z := Fin.ext hi
      subst i
      exact inf_le_right.trans hBC
    · exact inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp (hrest i hi))
  have hBne : B ≠ ⊥ := by
    intro hb
    have heu : E = U := by simpa only [hb, sup_bot_eq] using hprod
    rw [heu, hU] at hE
    omega
  have hs : s = 2 := by
    by_contra h
    have hsone : s = 1 := by omega
    apply hBne
    apply joint_kernel_eq_bot Q E B hBE hfaith
    intro i
    have hiz : i = z := Fin.ext (by have := i.isLt; dsimp [z]; omega)
    simpa only [hiz] using hBC
  let i : Fin s := ⟨1, by omega⟩
  have hi : i.val ≠ 0 := by change 1 ≠ 0; omega
  have hBfaith : B ⊓ centralizer (Q i : Set K) = ⊥ := by
    apply joint_kernel_eq_bot Q E _ (inf_le_left.trans hBE) hfaith
    intro j
    by_cases hj : j.val = 0
    · have hjz : j = z := Fin.ext hj
      subst j
      exact inf_le_left.trans hBC
    · have hji : j = i := Fin.ext (by have := j.isLt; dsimp [i]; omega)
      subst j
      exact inf_le_right
  have hBcard : Nat.card B = 2 := by
    have hle := faithful_card_le_two B (Q i) (hp i)
      (fun x hx => hsq x (hBE hx)) (hBE.trans (hn i)) hBfaith
    have hlt := (B.one_lt_card_iff_ne_bot).mpr hBne
    omega
  have hmove : ⁅B, Q i⁆ ≠ ⊥ := by
    intro hc
    apply hBne
    have hle := commutator_eq_bot_iff_le_centralizer.mp hc
    simpa only [inf_eq_left.mpr hle] using hBfaith
  refine ⟨hs, i, B, hi, hBE, hBcard, hprod, hdisj, ?_, ?_, hmove⟩
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      (hUE.trans ((le_centralizer E).trans (centralizer_le hBE)))
  · exact commutator_eq_bot_iff_le_centralizer.mpr hBC

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor.DiagonalComplement
