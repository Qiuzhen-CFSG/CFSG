module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor.Model
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor.NaturalRank
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Rank exclusion for the simultaneous A₆ × C₃ extension

On the concrete equal-sign subgroup of S₆ × S₃, every nonidentity involution
has displacement rank four on the actual natural tensor product. In the even
product, an involution has trivial C₃ component; the A₆ natural-module rank two
therefore doubles. A nontrivial S₃ component gives the general tensor lower
bound four. In characteristic two an involution's displacement image lies in
its kernel, giving the matching upper bound by rank-nullity.

The construction includes the full outer action, a faithful tensor
representation, the literal product kernel and cyclic quotient, and the
transposition/inversion conjugation formula. The final export uses the moved
space convention of the rank-two exclusion consumer. No rank assumption is
part of the model. Transport from an arbitrary source realization remains
with the source theorem's assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(10), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor
open BinaryPermutation

private theorem rank_le_four (g : GroupModel) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) ≤ 4 := by
  have h2 : representation g * representation g = 1 := by
    rw [← map_mul, hg, map_one]
  have hn (v : TensorSpace) : -v = v := by
    apply neg_eq_of_add_eq_zero_left
    calc
      v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
  have hfix (v : TensorSpace) :
      representation g (representation g v - v) = representation g v - v := by
    rw [map_sub]
    have hv : representation g (representation g v) = v := LinearMap.congr_fun h2 v
    rw [hv, sub_eq_add_neg, sub_eq_add_neg, hn, hn, add_comm]
  have hle : LinearMap.range (representation g - LinearMap.id) ≤
      LinearMap.ker (representation g - LinearMap.id) := by
    rintro _ ⟨v, rfl⟩
    change representation g (representation g v - v) - (representation g v - v) = 0
    rw [hfix, sub_self]
  have hh := (representation g - LinearMap.id).finrank_range_add_finrank_ker
  have hb := Submodule.finrank_mono hle
  rw [finrank_tensorSpace] at hh
  omega

/-- Every involution with a nontrivial cubic-module actor moves exactly four dimensions. -/
theorem finrank_outer_involution (g : GroupModel) (hg : g * g = 1)
    (h3 : g.val.2 ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) = 4 := by
  have hlo := ThreeTensor.dimension_le_displacement
    (naturalRepresentation (Fin 6)) g.val h3
  rw [finrank_fourSpace] at hlo
  have hup := rank_le_four g hg
  exact Nat.le_antisymm hup hlo

private theorem cubic_involution_eq_one : ∀ p : Equiv.Perm (Fin 3),
    p.sign = 1 → p * p = 1 → p = 1 := by decide +kernel

/-- On the even product an involution acts trivially on C₃ and has rank zero or four. -/
theorem finrank_inner_involution (g : GroupModel) (hg : g * g = 1)
    (heven : parity g = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) =
      if g = 1 then 0 else 4 := by
  classical
  have h6 : g.val.1 * g.val.1 = 1 := congrArg (fun h : GroupModel => h.val.1) hg
  have h3 : g.val.2 = 1 := cubic_involution_eq_one _
    (g.property.symm.trans heven) (congrArg (fun h : GroupModel => h.val.2) hg)
  have he : g.val = (g.val.1, 1) := Prod.ext rfl h3
  have hact : representation g = ThreeTensor.action (naturalRepresentation (Fin 6))
      (g.val.1, 1) := congrArg (ThreeTensor.action (naturalRepresentation (Fin 6))) he
  rw [hact, ThreeTensor.displacement_first]
  by_cases h : g = 1
  · subst g
    simp [Module.End.one_eq_id]
  · rw [if_neg h]
    have hr : Module.finrank (ZMod 2)
        (LinearMap.range (naturalRepresentation (Fin 6) g.val.1 - LinearMap.id)) = 2 :=
      finrank_natural_involution g.val.1 (show g.val.1.sign = 1 from heven) h6
        (fun hp => h (Subtype.ext (Prod.ext hp h3)))
    rw [hr]

/-- All nonidentity involutions of the concrete extension have displacement rank four. -/
theorem finrank_involution (g : GroupModel) (hg : g * g = 1) (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) = 4 := by
  by_cases h3 : g.val.2 = 1
  · have heven : parity g = 1 := by
      change g.val.1.sign = 1
      exact g.property.trans (by change g.val.2.sign = 1; rw [h3, map_one])
    simpa [hne] using finrank_inner_involution g hg heven
  · exact finrank_outer_involution g hg h3

/-- Rank two is excluded, including in the simultaneous outer-inversion coset. -/
theorem involution_not_rankTwo (g : GroupModel) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) ≠ 2 := by
  by_cases h : g = 1
  · subst g
    have hz : Module.finrank (ZMod 2)
        (LinearMap.range (representation (1 : GroupModel) - LinearMap.id)) = 0 :=
      finrank_inner_involution 1 (one_mul 1) (map_one parity)
    exact fun htwo => (by decide : (0 : ℕ) ≠ 2) (hz.symm.trans htwo)
  · rw [finrank_involution g hg h]
    decide
end Representation.RankTwo.Imprimitive.AlternatingSixTensor

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor
open BinaryPermutation

instance base_normal : base.range.Normal := by
  rw [base_range]
  infer_instance

/-- The cubic factor is the natural two-dimensional module, using the odd-degree core model. -/
noncomputable def twoSpaceEquivNatural : TwoSpace ≃ₗ[ZMod 2] natural (Fin 3) :=
  coreEquivNatural (Fin 3) (by decide)

theorem twoSpaceEquivNatural_equivariant (p : S3) (v : TwoSpace) :
    twoSpaceEquivNatural (coreRepresentation (Fin 3) p v) =
      naturalRepresentation (Fin 3) p (twoSpaceEquivNatural v) :=
  coreEquivNatural_equivariant (Fin 3) (by decide) p v

/-- The extension acts faithfully on the actual eight-dimensional tensor product. -/
theorem representation_injective : Function.Injective representation := by
  apply (injective_iff_map_eq_one representation).mpr
  intro g hg
  have hz : Module.finrank (ZMod 2)
      (LinearMap.range (ThreeTensor.action (naturalRepresentation (Fin 6)) g.val - LinearMap.id)) = 0 := by
    have hact : ThreeTensor.action (naturalRepresentation (Fin 6)) g.val = LinearMap.id := hg
    rw [hact, sub_self, LinearMap.range_zero]
    simp
  have h3 : g.val.2 = 1 := by
    by_contra h
    have hh := ThreeTensor.dimension_le_displacement (naturalRepresentation (Fin 6)) g.val h
    rw [hz, show Module.finrank (ZMod 2) (natural (Fin 6)) = 4 from finrank_fourSpace] at hh
    omega
  have he : g.val = (g.val.1, 1) := Prod.ext rfl h3
  rw [he, ThreeTensor.displacement_first] at hz
  have hzero : Module.finrank (ZMod 2)
      (LinearMap.range (naturalRepresentation (Fin 6) g.val.1 - LinearMap.id)) = 0 := by omega
  have hfirst : naturalRepresentation (Fin 6) g.val.1 = 1 :=
    sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero))
  have h6 : g.val.1 = 1 := naturalRepresentation_injective (Fin 6) (by decide)
    (hfirst.trans (map_one _).symm)
  exact Subtype.ext (Prod.ext h6 h3)

/-- In particular the whole odd-sign coset, including the distinguished x, has rank four. -/
theorem finrank_odd_involution (g : GroupModel) (hg : g * g = 1)
    (hodd : parity g = -1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - LinearMap.id)) = 4 := by
  apply finrank_outer_involution g hg
  intro h
  have hp : parity g = 1 := g.property.trans (by change g.val.2.sign = 1; rw [h, map_one])
  rw [hp] at hodd
  exact (by decide : (1 : ℤˣ) ≠ -1) hodd

theorem finrank_outer :
    Module.finrank (ZMod 2) (LinearMap.range (representation outer - LinearMap.id)) = 4 :=
  finrank_odd_involution outer outer_sq parity_outer

end Representation.RankTwo.Imprimitive.AlternatingSixTensor

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor

theorem outer_not_mem_base : outer ∉ base.range := by
  rw [base_range]
  change parity outer ≠ 1
  rw [parity_outer]
  decide

/-- The quotient is the cyclic group of order two. -/
noncomputable def quotientEquivTwo : GroupModel ⧸ parity.ker ≃* Multiplicative (ZMod 2) :=
  quotientEquiv.trans (mulEquivOfPrimeCardEq (p := 2)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]) (by simp))

end Representation.RankTwo.Imprimitive.AlternatingSixTensor

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor

/-- The rank exclusion in the moved-space convention used by the 6.2.19 consumer. -/
theorem movedSpace_not_rankTwo (g : GroupModel) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace representation g) ≠ 2 :=
  involution_not_rankTwo g hg

/-- The embedded product is the literal kernel of the quotient homomorphism. -/
noncomputable def baseEquivKernel : (A6 × C3) ≃* parity.ker :=
  (MonoidHom.ofInjective base_injective).trans (MulEquiv.subgroupCongr base_range)

end Representation.RankTwo.Imprimitive.AlternatingSixTensor
