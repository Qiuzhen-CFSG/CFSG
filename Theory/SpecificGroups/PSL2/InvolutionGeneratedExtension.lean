module
public import Theory.SpecificGroups.PSL2.BinaryOuterGeometry
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
/-!
# Binary rank-one involution-generated extensions

An outer involution acting faithfully on PSL2(2^r) fixes the actual
half-degree PSL2 subgroup. Its two-core is trivial and it has more than
one element, so the fixed subgroup cannot be a two-group. Thus every
involution with two-group ambient centralizer lies in the original normal
PSL2 subgroup; if involutions generate, the extension is trivial.

Source: Aschbacher--Smith E.2.7, printed p.220, outer-extension inspection.
-/

public section
open Subgroup
namespace Theory.PSL2.BinaryOuterGeometry
variable {G : Type*} [_root_.Group G] [Finite G]

omit [Finite G] in
/-- A binary rank-one layer has no outer involution with a two-group
centralizer in the ambient faithful extension. -/
theorem involution_mem_of_centralizer_isTwoGroup
    (L : Subgroup G) [L.Normal] {r : ℕ} (e : L ≃* BinaryGroup r)
    (hCL : centralizer (L : Set G) = ⊥) (hr : 2 ≤ r)
    (t : G) (ht : t ^ 2 = 1) (hc : IsPGroup 2 (centralizer ({t} : Set G))) :
    t ∈ L := by
  by_contra hn
  obtain ⟨m,hm,_,⟨f⟩⟩ := outer_fixed_model L e hCL hr t ht hn
  have hp : IsPGroup 2 (BinaryGroup m) := (hc.to_le inf_le_right).of_equiv f
  have hz : pCore 2 (BinaryGroup m) = ⊥ := Atlas.RankOneFieldAutomorphisms.psl_twoCore_eq_bot
  have htop : (⊤ : Subgroup (BinaryGroup m)) ≤ pCore 2 (BinaryGroup m) :=
    le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
  have hone : Nat.card (BinaryGroup m) = 1 := by
    have hbot : (⊤ : Subgroup (BinaryGroup m)) = ⊥ := le_bot_iff.mp (hz ▸ htop)
    have hcard := congrArg (fun S : Subgroup (BinaryGroup m) => Nat.card S) hbot
    simpa only [Subgroup.card_top, Subgroup.card_bot] using hcard
  have hq : 2 ≤ Nat.card (BinaryField m) := Finite.one_lt_card (α := BinaryField m)
  have hcard : Nat.card (BinaryGroup m) =
      Nat.card (BinaryField m) * (Nat.card (BinaryField m) ^ 2 - 1) := by
    rw [← Nat.card_congr (sl2QuotientEquiv (BinaryField m)).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup]
  have hs : 1 ≤ Nat.card (BinaryField m)^2-1 := by nlinarith
  have hlarge : 2 ≤ Nat.card (BinaryGroup m) := by
    rw [hcard]
    exact (by omega : 2 ≤ Nat.card (BinaryField m)).trans
      (Nat.le_mul_of_pos_right _ hs)
  omega

omit [Finite G] in
/-- Involution generation eliminates every faithful outer extension of a
binary rank-one group with two-group involution centralizers. -/
theorem eq_top_of_involution_generated
    (L : Subgroup G) [L.Normal] {r : ℕ} (e : L ≃* BinaryGroup r)
    (hCL : centralizer (L : Set G) = ⊥) (hr : 2 ≤ r)
    (hgen : closure {g : G | g ^ 2 = 1} = ⊤)
    (hc : ∀ t : G, orderOf t = 2 → IsPGroup 2 (centralizer ({t} : Set G))) :
    L = ⊤ := by
  apply top_unique
  rw [←hgen]
  apply (closure_le _).mpr
  intro t ht
  change t ∈ L
  by_cases ht1 : t = 1
  · simpa only [ht1] using L.one_mem
  exact involution_mem_of_centralizer_isTwoGroup L e hCL hr t ht
    (hc t (orderOf_eq_prime ht ht1))

end Theory.PSL2.BinaryOuterGeometry
