module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight.Action
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer

/-!
# The exact centralizer order of the source eight

For the p.688 branch of Aschbacher–Smith, Proposition 6.2.13, the actual
quaternion factors give `C_P(U) = U`. Thus the `P`-image on `U` has order
four. The actual Sylow-three subgroup cannot centralize `U`, since its
centralizer in `P` is `Z(P)`, so the full image order is divisible by twelve.
Fixing `Z(P)` bounds it by twenty-four. The only possible centralizer orders
are sixteen and thirty-two; the latter would give a normal subgroup of order
four in the genuine quotient `H/P ≃ S₃ × C₂`, which has no such subgroup.

The only action input is `NaturalFourOrbit`, whose source producer is the
G.6.4(2) argument in `qt-6-02-m22-branch`. No recognition theorem, split
extension, elementary sixteen, or symmetric-four quotient is used.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
variable {H : Type*} [Group H] [Finite H] {P S : Subgroup H} [P.Normal]

/-- The quaternion factors make the elementary eight self-centralizing in `P`. -/
public theorem sourceEight_intersection_core_centralizer
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P) :
    P ⊓ centralizer (sourceEight S : Set H) = sourceEight S := by
  let U := sourceEight S
  have hUP : U ≤ P := sourceEight_le_core P S hSP
  let := sourceEight_elementary h ha hS
  let := IsElementaryAbelian.subgroupOf (p := 2) hUP
  have hUc : Nat.card (U.subgroupOf P) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans (sourceEight_card h ha hZS)
  obtain ⟨d⟩ := h.plusType
  have he := inf_centralizer_elementary_eight_of_quaternion_factors
    d.left d.right (U.subgroupOf P) d.left_model d.right_model d.intersection_card
    d.commute hUc (by rw [d.span]; exact le_top)
  rw [d.span, top_inf_eq] at he
  apply le_antisymm
  · intro x hx
    have hm : (⟨x, hx.1⟩ : P) ∈ centralizer (U.subgroupOf P : Set P) := by
      intro y hy
      exact Subtype.ext (hx.2 y hy)
    rw [he] at hm
    exact hm
  · exact le_inf hUP (le_centralizer U)

private theorem card_inf_ker_mul_card_map {G K : Type*} [Group G] [Group K]
    (A : Subgroup G) (f : G →* K) :
    Nat.card (A ⊓ f.ker : Subgroup G) * Nat.card (A.map f) = Nat.card A := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ f.ker) A bot_le inf_le_left
  rwa [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, relIndex_ker] at hc

/-- The `P`-action and the Sylow-three action force divisibility by twelve. -/
public theorem sourceEightAction_card_multiple_twelve
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P) :
    12 ∣ Nat.card (sourceEightAction S).range := by
  let f := sourceEightAction S
  have hP : Nat.card P = 32 := by obtain ⟨d⟩ := h.plusType; exact d.card
  have hPi : Nat.card (P.map f) = 4 := by
    have hc := card_inf_ker_mul_card_map P f
    rw [sourceEightAction_ker, sourceEight_intersection_core_centralizer h ha hS hZS hSP,
      sourceEight_card h ha hZS, hP] at hc
    omega
  have h4 : 4 ∣ Nat.card f.range := hPi ▸ card_dvd_of_le (P.map_le_range f)
  obtain ⟨X, hX⟩ := h.sylowThreeCentralizer
  have hXc : Nat.card X = 3 := by
    rw [Sylow.card_eq_multiplicity, h.card]
    decide +kernel
  have hXi : Nat.card ((X : Subgroup H).map f) = 3 := by
    have hd := (X : Subgroup H).card_map_dvd f
    rw [hXc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · have hb := card_eq_one.mp h1
      have hfix : (X : Subgroup H) ≤ centralizer (sourceEight S : Set H) := by
        rw [← sourceEightAction_ker]
        exact (Subgroup.map_eq_bot_iff _).mp hb
      have hu : sourceEight S ≤ coreCenter P := by
        rw [coreCenter, ← hX]
        refine le_inf (sourceEight_le_core P S hSP) ?_
        intro u hu x hx
        exact (hfix hx u hu).symm
      have hc := card_le_of_le hu
      rw [sourceEight_card h ha hZS, coreCenter_card h] at hc
      omega
    · exact h3
  have h3 : 3 ∣ Nat.card f.range := hXi ▸ card_dvd_of_le ((X : Subgroup H).map_le_range f)
  exact (show Nat.Coprime 4 3 by decide).mul_dvd_of_dvd_of_dvd h4 h3

private theorem normal_four_impossible
    (N : Subgroup (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) [N.Normal]
    (hc : Nat.card N = 4) : False := by
  let f := MonoidHom.fst (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))
  let B := N.map f
  have hf : Function.Surjective f := fun x => ⟨(x, 1), rfl⟩
  let : B.Normal := Subgroup.Normal.map inferInstance f hf
  have hb4 : Nat.card B ∣ 4 := hc ▸ N.card_map_dvd f
  have hb6 : Nat.card B ∣ 6 := by
    have hd := B.card_subgroup_dvd_card
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
    rwa [h6] at hd
  have hb2 : Nat.card B ∣ 2 := by simpa using Nat.dvd_gcd hb4 hb6
  have he : ∀ x : Equiv.Perm (Fin 3), x ∈ center (Equiv.Perm (Fin 3)) → x = 1 := by
    intro x hx
    have hcheck : ∀ x : Equiv.Perm (Fin 3), (∀ y, y * x = x * y) → x = 1 := by
      decide +kernel
    exact hcheck x (mem_center_iff.mp hx)
  have hB : B = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hb2 with h1 | h2
    · exact card_eq_one.mp h1
    · apply le_bot_iff.mp
      intro x hx
      exact he x (central_of_normal_card_two B h2 hx)
  have hfst (x : N) : (x : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)).1 = 1 := by
    have hm : f x ∈ B := mem_map.mpr ⟨x, x.property, rfl⟩
    rwa [hB, mem_bot] at hm
  have hi : Function.Injective (fun x : N => (x : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)).2) := by
    intro x y heq
    apply Subtype.ext
    exact Prod.ext ((hfst x).trans (hfst y).symm) heq
  have hn := Nat.card_le_card_of_injective _ hi
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  rw [hc, h2] at hn
  omega

/-- Normality of the centralizer excludes order thirty-two in the actual quotient. -/
public theorem sourceEight_centralizer_card
    (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P) :
    Nat.card (centralizer (sourceEight S : Set H)) = 16 := by
  let f := sourceEightAction S
  have h12 := sourceEightAction_card_multiple_twelve h ha hS hZS hSP
  have h24 := sourceEightAction_card_dvd_twentyfour h ha hS hZS
  have hrpos := Nat.card_pos (α := f.range)
  have hrle := Nat.le_of_dvd (by decide : 0 < 24) h24
  have hcases : Nat.card f.range = 12 ∨ Nat.card f.range = 24 := by
    obtain ⟨n, hn⟩ := h12
    dsimp only [f] at hrpos hrle ⊢
    omega
  have hc := f.ker.card_mul_index
  rw [index_ker, sourceEightAction_ker, h.card] at hc
  rcases hcases with hr | hr
  · have hF : Nat.card (centralizer (sourceEight S : Set H)) = 32 := by
      rw [hr] at hc; omega
    obtain ⟨e⟩ := h.quotient
    let q := e.toMonoidHom.comp (QuotientGroup.mk' P)
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective P)
    have hk : q.ker = P := by
      ext x
      change e (QuotientGroup.mk' P x) = 1 ↔ x ∈ P
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    let F := centralizer (sourceEight S : Set H)
    let N := F.map q
    let : N.Normal := Subgroup.Normal.map inferInstance q hq
    have hn : Nat.card N = 4 := by
      have hi := card_inf_ker_mul_card_map F q
      rw [hk, inf_comm, sourceEight_intersection_core_centralizer h ha hS hZS hSP,
        sourceEight_card h ha hZS, hF] at hi
      change 8 * Nat.card N = 32 at hi
      omega
    exact (normal_four_impossible N hn).elim
  · rw [hr] at hc
    omega
end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
