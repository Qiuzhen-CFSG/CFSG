module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Action
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension

/-!
# The mixed linear extension cannot be the marked star quotient

The original outside order-p element remains outside with order p after
quotienting by Oₚ′(H): a p-prime kernel absorbs no such outside element into
a normal component. In A.3.16's mixed linear circle, the proved scalar twisted
norm and projective descent instead put every cube-one element in its literal
inner component. A marked isomorphism of the actual star pair therefore
contradicts the given outside cubic. Both quotient and component maps are
retained; no replacement of the actor is assumed to preserve its order.
Source: Aschbacher–Smith A.3.16–18, printed pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

/-- The specified split actor retains its exact order and stays outside the
component in the actual prime-to-p-core quotient. -/
theorem star_actor {K : Subgroup H} [K.Normal] {p : ℕ} (hp : p.Prime)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    orderOf (starMap p H a) = p ∧ starMap p H a ∉ starComponent p K := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : starMap p H a ∉ starComponent p K := by
    intro hi
    apply haK
    exact prime_element_mem_of_image_mem (starMap p H)
      (by rw [starMap, QuotientGroup.ker_mk']; exact pPrimeCore_coprime_card) K a ha hi
  refine ⟨orderOf_eq_prime ?_ (fun he => hn (he ▸ (starComponent p K).one_mem)), hn⟩
  rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]

/-- A marked identification of the original star extension with the mixed
linear circle is impossible. The actual quotient map carries the original
order-three actor to an outside cubic; twisted-norm nonsplitting puts it back
in the marked component. -/
theorem not_marked_linearCircle_star
    {K : Subgroup H} [K.Normal]
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ (6 * n)) (c : Fˣ) (hc : Noncube c)
    (e : Star 3 H ≃* linearCircle F n c) :
    (starComponent 3 K).map e.toMonoidHom ≠ linearCircleComponent F n c := by
  intro he
  have ha' := star_actor Nat.prime_three a ha haK
  have hpow : e (starMap 3 H a) ^ 3 = 1 := by
    have hh : starMap 3 H a ^ 3 = 1 := by simpa only [ha'.1] using pow_orderOf_eq_one (starMap 3 H a)
    rw [← map_pow, hh, map_one]
  have hm := linearCircle_cube_one_mem_component hn hF c hc (e (starMap 3 H a)) hpow
  rw [← he] at hm
  obtain ⟨x, hx, heq⟩ := hm
  exact ha'.2 (e.injective heq ▸ hx)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
