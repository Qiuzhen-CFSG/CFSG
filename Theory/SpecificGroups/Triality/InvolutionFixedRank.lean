module
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.GroupAction.InnerInvolutionGeometry
/-!
# Derived three-rank of binary triality involution fixed groups

An inner involution is conjugation by an actual element of order two, since
this carrier has trivial center. Its centralizer normalizes that element's
cyclic two-subgroup. The finite Borel–Tits cover therefore conjugates the
whole fixed group into a genuine full parabolic. The derived parabolic lies
in its local factor because the torus quotient is cyclic; the local factor
has three-rank at most one by its actual PSL₂ quotient and two-core.

The proof covers every positive binary exponent, including q = 2, and uses
no fixed-group classification or assumed parabolic-containment callback.

Sources: Aschbacher–Smith E.6.18 and E.6.23, printed pp.252–254, using
F.1.12(I)(4), pp.263–264, and 16.1.4(1), p.1171 (`refs/quasithin.pdf`);
GLS3 Theorems 2.6.5 and 3.1.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.InvolutionFixedRank
open Parabolics

/-- The cyclic torus disappears on passing to the derived full parabolic. -/
theorem derived_parabolic_threeRank_le_one (P : Parameters) (hp : P.prime = 2)
    (a : Node) : primeRank 3 (commutator (parabolic P a)) ≤ 1 := by
  let N := (localFactor P a).subgroupOf (parabolic P a)
  let := parabolic_quotient_isCyclic P hp a
  have hle : commutator (parabolic P a) ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp inferInstance
  have h := primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle)
  have hr : primeRank 3 N ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe (localFactor_le_parabolic P a))]
    exact localFactor_threeRank_le_one P hp a
  exact h.trans hr

/-- The original inner involution has a fixed group whose derived three-rank is at most one. -/
theorem inner_fixed_derived_threeRank_le_one (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    primeRank 3 (commutator a.fixedSubgroup) ≤ 1 := by
  obtain ⟨x, hx⟩ := hi
  have ho : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (binaryCarrier_center_eq_bot n hn) x).symm.trans
      ((congrArg orderOf hx).trans ha)
  change MulAut.conj x = a at hx
  have hR : zpowers x ≠ ⊥ := by
    intro h
    have hx1 := zpowers_eq_bot.mp h
    simp only [hx1, orderOf_one] at ho
    omega
  have htwo : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨g, b, hcover⟩ := TwoLocalCover.normalizer_cover n hn (zpowers x) hR htwo
  have hCN : a.fixedSubgroup ≤ normalizer (zpowers x : Set (BinaryCarrier n hn)) := by
    rw [← hx, MulAut.fixedSubgroup_conj]
    rw [← centralizer_closure ({x} : Set (BinaryCarrier n hn)), ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  let f : a.fixedSubgroup →* parabolic (binaryParameters n hn) b :=
    ((MulAut.conj g).toMonoidHom.comp a.fixedSubgroup.subtype).codRestrict _
      (fun y => hcover (mem_map_of_mem _ (hCN y.property)))
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hd : (commutator a.fixedSubgroup).map f ≤
      commutator (parabolic (binaryParameters n hn) b) := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let k : commutator a.fixedSubgroup →* commutator (parabolic (binaryParameters n hn) b) :=
    (f.comp (commutator a.fixedSubgroup).subtype).codRestrict _
      (fun y => hd (mem_map_of_mem f y.property))
  have hk : Function.Injective k := by
    intro y z h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  exact (primeRank_le_of_injective 3 k hk).trans
    (derived_parabolic_threeRank_le_one (binaryParameters n hn) rfl b)
end Triality.Standard.InvolutionFixedRank
