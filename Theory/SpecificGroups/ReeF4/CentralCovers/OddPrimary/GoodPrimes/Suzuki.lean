module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Suzuki.Factors
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Suzuki.Commutation
public import Theory.SpecificGroups.Suzuki.NonsplitTori

/-!
# Both nonsplit Suzuki product tori in the Ree group

The two orthogonal B₂ planes give commuting copies of the literal Suzuki
matrix group in `ReeF4.Model m`. Their product is injective for `m ≥ 1`.
Restricting both coordinates to either checked nonsplit torus gives the
marked cyclic product of order `(q ± 2^(m+1) + 1)²`.

The square of the Suzuki normalizer's Frobenius element inverts the first
torus and commutes with the second factor. This supplies the literal ambient
`ReversesPair` equations, without requiring the interchange to square to one
on the chosen cyclic coordinates. The Weyl interchange of the two full
Suzuki factor ranges is retained in `SuzukiFactors.interchange_ranges`.

Sources: GLS3 Example 2.6.3 and Theorem 6.5.4(c), in
`refs/KGroup/GLS3/chapter2.tex` and `chapter6.tex`; the torus application in
§4.10. The Suzuki torus construction is the checked Huppert--Blackburn XI.3.10
implementation in `Theory.SpecificGroups.Suzuki.NonsplitTori`.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary
open Subgroup BenderSuzuki.MatrixGroups

/-- The concrete root calculation supplies commutation of the marked factors. -/
theorem SuzukiFactors.commuteFactors (m : ℕ) : SuzukiFactors.CommuteFactors m := by
  intro x y
  apply SuzukiOrthogonal.standard_commute m
  · rw [← SuzukiFactors.first_range]
    exact ⟨x, rfl⟩
  · rw [← SuzukiFactors.second_range]
    exact ⟨y, rfl⟩

private theorem nonsplit_inverter {m : ℕ} (hm : 1 ≤ m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    ∃ r : SuzukiMatrixGroup m, ∀ u ∈ U, r * u * r⁻¹ = u⁻¹ := by
  obtain ⟨t, _, _, _, _, ht⟩ := hU.normalizer_complement hm
  let a : MulAut (SuzukiMatrixGroup m) := MulAut.conj t⁻¹
  have ha (u : SuzukiMatrixGroup m) (hu : u ∈ U) : a u = u ^ (2 ^ (2 * m + 1)) := by
    simpa only [a, MulAut.conj_apply, inv_inv] using ht u hu
  refine ⟨t⁻¹ * t⁻¹, ?_⟩
  intro u hu
  have he : (u ^ (2 ^ (2 * m + 1))) ^ (2 ^ (2 * m + 1)) = u⁻¹ := by
    rw [← pow_mul, ← pow_two]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact orderOf_dvd_iff_pow_eq_one.mp ((U.orderOf_dvd_natCard hu).trans hU.card_dvd)
  calc
    (t⁻¹ * t⁻¹) * u * (t⁻¹ * t⁻¹)⁻¹ = a (a u) := by
      simp only [a, MulAut.conj_apply, inv_inv, mul_inv_rev, mul_assoc]
    _ = _ := by rw [ha u hu, map_pow, ha u hu, he]

/-- Restrict the faithful pair of Suzuki factors to a specified nonsplit torus.
The reversing element is an actual element of the first ambient factor. -/
def suzukiProductTorusEmbedding {m n : ℕ} (hm : 1 ≤ m)
    (U : Subgroup (SuzukiMatrixGroup m)) (hU : IsSuzukiMaximalNonsplit m U)
    (hcard : Nat.card U = n) : ProductTorusEmbedding m n := by
  letI : IsCyclic U := hU.isCyclic hm
  let e : Multiplicative (ZMod n) ≃* U := mulEquivOfCyclicCardEq (by
    change Nat.card (ZMod n) = Nat.card U
    rw [Nat.card_zmod, hcard])
  let i : Multiplicative (ZMod n) →* SuzukiMatrixGroup m := U.subtype.comp e.toMonoidHom
  have hi : Function.Injective i := U.subtype_injective.comp e.injective
  let j := (SuzukiFactors.product m (SuzukiFactors.commuteFactors m)).comp (i.prodMap i)
  refine ⟨j, (SuzukiFactors.product_injective hm (SuzukiFactors.commuteFactors m)).comp
    (fun a b hab => Prod.ext (hi (congrArg Prod.fst hab)) (hi (congrArg Prod.snd hab))), ?_⟩
  obtain ⟨r, hr⟩ := nonsplit_inverter hm hU
  intro z
  have hj1 : j (z, 1) = SuzukiFactors.first m (i z) := by
    change SuzukiFactors.product m (SuzukiFactors.commuteFactors m) (i z, i 1) = _
    rw [map_one, SuzukiFactors.product_first]
  have hj2 : j (1, z) = SuzukiFactors.second m (i z) := by
    change SuzukiFactors.product m (SuzukiFactors.commuteFactors m) (i 1, i z) = _
    rw [map_one, SuzukiFactors.product_second]
  rw [hj1, hj2]
  apply Or.inr
  refine ⟨SuzukiFactors.first m r, ?_, SuzukiFactors.commuteFactors m r (i z)⟩
  rw [← map_inv, ← map_mul, ← map_mul, hr (i z) (e z).property, map_inv]

/-- The smaller nonsplit Suzuki torus embeds in each of the two commuting factors. -/
theorem exists_suzuki_minus_productTorusEmbedding (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1)) := by
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  refine ⟨suzukiProductTorusEmbedding hm T.minus T.minus_maximal ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using T.minus_card

/-- The larger nonsplit Suzuki torus embeds with the same literal coordinate convention. -/
theorem exists_suzuki_plus_productTorusEmbedding (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1)) := by
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  refine ⟨suzukiProductTorusEmbedding hm T.plus T.plus_maximal ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using T.plus_card

end ReeF4.CentralCovers.OddPrimary
