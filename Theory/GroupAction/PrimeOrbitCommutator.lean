module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Index

/-!
# Commutator lines and generating prime orbits

Suppose a group of prime order acts on a finite group with trivial fixed
subgroup. If the orbit of an element generates the group, its commutator
subgroup with the whole group cannot have order two. Indeed, two distinct
translates of that line intersect trivially: equality would fix its unique
nonidentity element under a generator of the acting group. Commutators of
two orbit elements lie in both lines, so all orbit elements commute.

This source-independent argument supplies the commutator-line obstruction
for the quotient by the center in Parrott, *A characterization of the Tits'
simple group* (1972), pp.673–674, property (d).
-/

namespace Theory.GroupAction
open Subgroup
open scoped commutatorElement

private theorem order_two_line_eq_of_common_nonidentity
    {G : Type*} [Group G] (L R : Subgroup G)
    (hL : Nat.card L = 2) (hR : Nat.card R = 2)
    {x : G} (hxL : x ∈ L) (hxR : x ∈ R) (hx : x ≠ 1) : L = R := by
  have hgen (S : Subgroup G) (hS : Nat.card S = 2) (hxS : x ∈ S) :
      S = zpowers x := by
    apply le_antisymm
    · obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hS
      intro y hy
      by_cases hy1 : y = 1
      · exact hy1 ▸ (zpowers x).one_mem
      have heq : (⟨y, hy⟩ : S) = ⟨x, hxS⟩ :=
        (hu _ (fun h => hy1 (congrArg Subtype.val h))).trans
          (hu _ (fun h => hx (congrArg Subtype.val h))).symm
      have hyx : y = x := congrArg Subtype.val heq
      rw [hyx]
      exact mem_zpowers x
    · exact zpowers_le.mpr hxS
  exact (hgen L hL hxL).trans (hgen R hR hxR).symm

/-- A generating orbit under a prime-order action with trivial fixed subgroup
cannot have an order-two commutator line. -/
public theorem commutator_zpowers_card_ne_two_of_prime_orbit
    {A G : Type*} [Group A] [Group G] [Finite G]
    [MulDistribMulAction A G] {p : ℕ} [Fact p.Prime]
    (hA : Nat.card A = p) (hfixed : FixedPoints.subgroup A G = ⊥)
    (b : G) (hgen : closure (Set.range (fun a : A => a • b)) = ⊤) :
    Nat.card ↥(⁅zpowers b, (⊤ : Subgroup G)⁆) ≠ 2 := by
  intro htwo
  let L := ⁅zpowers b, (⊤ : Subgroup G)⁆
  let α := MulDistribMulAction.toMulAut A G
  have hmap (a : A) : L.map (α a).toMonoidHom =
      ⁅zpowers (a • b), (⊤ : Subgroup G)⁆ := by
    rw [map_commutator, MonoidHom.map_zpowers,
      map_top_of_surjective (α a).toMonoidHom (α a).surjective]
    rfl
  have hmove (a : A) (ha : a ≠ 1) : L.map (α a).toMonoidHom ≠ L := by
    intro heq
    obtain ⟨x, hx, huniq⟩ := (Nat.card_eq_two_iff' (1 : L)).mp htwo
    have hxne : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
    have hax : a • (x : G) ∈ L :=
      heq.le (mem_map_of_mem (α a).toMonoidHom x.property)
    have haxne : a • (x : G) ≠ 1 := by
      intro h
      exact hxne ((α a).injective (h.trans (α a).map_one.symm))
    have haxeq : a • (x : G) = x := congrArg Subtype.val
      ((huniq ⟨_, hax⟩ (fun h => haxne (congrArg Subtype.val h))).trans
        (huniq x hx).symm)
    have hstab : MulAction.stabilizer A (x : G) = ⊤ := by
      apply top_unique
      rw [← zpowers_eq_top_of_prime_card hA ha]
      exact zpowers_le.mpr haxeq
    have hxfix : (x : G) ∈ FixedPoints.subgroup A G := by
      intro c
      exact show c ∈ MulAction.stabilizer A (x : G) from hstab ▸ mem_top c
    exact hxne (mem_bot.mp (hfixed ▸ hxfix))
  have hbcomm (a : A) : Commute b (a • b) := by
    by_cases ha : a = 1
    · simpa only [ha, one_smul] using Commute.refl b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    by_contra hc
    have hcL : ⁅b, a • b⁆ ∈ L :=
      commutator_mem_commutator (mem_zpowers b) (mem_top _)
    have hcR : ⁅b, a • b⁆ ∈ L.map (α a).toMonoidHom := by
      rw [hmap, Subgroup.commutator_comm]
      exact commutator_mem_commutator (mem_top _) (mem_zpowers _)
    exact hmove a ha (order_two_line_eq_of_common_nonidentity _ _
      (by rw [card_map_of_injective (f := (α a).toMonoidHom) (α a).injective]; exact htwo)
      htwo hcR hcL hc)
  have hcomm : ∀ x ∈ Set.range (fun a : A => a • b),
      ∀ y ∈ Set.range (fun a : A => a • b), x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    have hh := congrArg (fun x : G => a • x) (hbcomm (a⁻¹ * c)).eq
    simpa only [smul_mul', ← mul_smul, mul_inv_cancel_left] using hh
  have habelian : IsMulCommutative G := by
    let ht : IsMulCommutative (⊤ : Subgroup G) :=
      hgen ▸ isMulCommutative_closure hcomm
    exact ⟨⟨fun x y => setLike_mul_comm (s := (⊤ : Subgroup G)) (mem_top x) (mem_top y)⟩⟩
  have hbot : L = ⊥ := by
    apply eq_bot_iff.mpr
    exact (commutator_mono le_top le_rfl).trans_eq
      ((commutator_eq_bot_iff G).mpr habelian)
  have hc : Nat.card L = 1 := card_eq_one.mpr hbot
  change Nat.card L = 2 at htwo
  omega

end Theory.GroupAction
