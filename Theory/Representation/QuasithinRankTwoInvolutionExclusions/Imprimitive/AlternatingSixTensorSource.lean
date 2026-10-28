module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer

/-!
# The A₆ tensor exclusion in arbitrary extension coordinates

An embedded normal A₆ × C₃ and an involution x generate the source extension.
Only the restriction to this normal product is identified with the natural
binary tensor module. Its cubic generator has no nonzero fixed vectors, as
shown in the actual three-point augmentation coordinates. Every element of
the outer coset inverts that generator. The fixed and moved spaces of an outer
involution coincide, so its displacement rank is four. Inner ranks transport
from the concrete equal-sign model. No action formula for x on the tensor
product is assumed, and its additional transposition action on A₆ is not needed
for this stronger rank statement.

The final application supplies all hypotheses from the actual equal-sign
subgroup of S₆ × S₃, including normality, generation and cubic inversion.
Source: Aschbacher–Smith G.11.2(10), printed p.364/PDF p.375, and the exclusion
in 6.2.19, printed p.691/PDF p.708.
-/

@[expose] public section

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor
open BinaryPermutation

def cubicGenerator : C3 := ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
  change (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2).sign = 1
  decide⟩

private theorem cubic_relations : cubicGenerator ^ 3 = 1 ∧
    cubicGenerator⁻¹ = cubicGenerator ^ 2 ∧
    ∀ c : C3, Commute c cubicGenerator := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · change ∀ c : C3, c * cubicGenerator = cubicGenerator * c
    decide +kernel

private theorem cubic_core_coordinates (w : TwoSpace) :
    (coreRepresentation (Fin 3) cubicGenerator.val w).val 0 = w.val 1 ∧
    (coreRepresentation (Fin 3) cubicGenerator.val w).val 1 = w.val 0 + w.val 1 := by
  constructor
  · rfl
  · change w.val 2 = w.val 0 + w.val 1
    have h := w.property
    rw [mem_core, Fin.sum_univ_three] at h
    have hn (a : ZMod 2) : -a = a := by revert a; decide
    calc
      w.val 2 = -(w.val 0 + w.val 1) := eq_neg_of_add_eq_zero_right h
      _ = w.val 0 + w.val 1 := hn _

private theorem cubic_tensor_coordinates (v : TensorSpace) :
    ThreeTensor.pairEquiv (representation (base (1,cubicGenerator)) v) =
      TensorCoordinates.cubic (ThreeTensor.pairEquiv v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v w =>
    rw [representation_tmul, ThreeTensor.pairEquiv_tmul, ThreeTensor.pairEquiv_tmul]
    have hc := cubic_core_coordinates w
    change ((coreRepresentation (Fin 3) cubicGenerator.val w).val 0 •
      naturalRepresentation (Fin 6) 1 v,
      (coreRepresentation (Fin 3) cubicGenerator.val w).val 1 •
      naturalRepresentation (Fin 6) 1 v) =
      (w.val 1 • v, w.val 0 • v + w.val 1 • v)
    rw [hc.1, hc.2, map_one, Module.End.one_apply, add_smul]
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv

/-- The cubic factor acts without nonzero fixed vectors on the actual tensor module. -/
theorem cubic_fixed_free (v : TensorSpace)
    (hv : representation (base (1,cubicGenerator)) v = v) : v = 0 := by
  apply ThreeTensor.pairEquiv.injective
  rw [map_zero]
  apply TensorCoordinates.cubic_fixed_free
  rw [← cubic_tensor_coordinates, hv]

end Representation.RankTwo.Imprimitive.AlternatingSixTensor

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor

private theorem extension_two_cosets {H : Type*} [Group H]
    (i : (A6 × C3) →* H) [i.range.Normal] (x : H) (hx : x * x = 1)
    (hgen : Subgroup.zpowers x ⊔ i.range = ⊤) (g : H) :
    ∃ a : A6 × C3, g = i a ∨ g = x * i a := by
  classical
  have hg : g ∈ Subgroup.zpowers x ⊔ i.range := hgen ▸ Subgroup.mem_top g
  obtain ⟨y, hy, b, ⟨a, rfl⟩, h⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hp : x ^ 2 = 1 := by simpa only [pow_two] using hx
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hp⟩
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hy)
  have hn2 : n < 2 := lt_of_lt_of_le (Finset.mem_range.mp hn)
    (orderOf_le_of_pow_eq_one (by decide) hp)
  refine ⟨a, ?_⟩
  interval_cases n
  · exact Or.inl (by simpa using h.symm)
  · exact Or.inr (by simpa using h.symm)

/-- Case (10) in an arbitrary realization of the extension. Only the restriction
to the actual normal product is identified with the natural tensor module.
The outer operator is determined enough for the rank calculation by its
inversion of the cubic factor, without assuming an equivariant extension. -/
theorem source_not_rankTwo
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (A6 × C3) →* H) (hi : Function.Injective i) [i.range.Normal]
    (x : H) (hx : x * x = 1)
    (hgen : Subgroup.zpowers x ⊔ i.range = ⊤)
    (hinvert : ∀ c : C3, x * i (1,c) * x⁻¹ = i (1,c⁻¹))
    (f : V ≃ₗ[ZMod 2] TensorSpace)
    (hbase : ∀ a : A6 × C3, ∀ v, f (ρ (i a) v) = representation (base a) (f v))
    (g : H) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  obtain ⟨⟨a,c⟩, rfl | rfl⟩ := extension_two_cosets i x hx hgen g
  · have h2 : (a,c) * (a,c) = (1 : A6 × C3) := hi (by rw [map_mul, hg, map_one])
    have hm : base (a,c) * base (a,c) = 1 := by rw [← map_mul, h2, map_one]
    have he := (displacementRangeEquiv f (ρ (i (a,c))) (representation (base (a,c)))
      (fun v => (hbase (a,c) v).symm)).finrank_eq
    intro hr
    exact movedSpace_not_rankTwo (base (a,c)) hm (he.symm.trans hr)
  · let z := i (1,cubicGenerator)
    have hz3 : z ^ 3 = 1 := by
      change (i (1,cubicGenerator)) ^ 3 = 1
      rw [← map_pow, show (1,cubicGenerator) ^ 3 = (1 : A6 × C3) by
        exact Prod.ext (one_pow _) cubic_relations.1, map_one]
    have hzfree : ∀ v, ρ z v = v → v = 0 := by
      intro v hv
      apply f.injective
      rw [map_zero]
      apply cubic_fixed_free
      rw [← hbase, hv]
    have hcz : Commute (i (a,c)) z := by
      exact (show Commute (a,c) (1,cubicGenerator) from
        Prod.ext ((mul_one a).trans (one_mul a).symm) (cubic_relations.2.2 c).eq).map i
    have hxz : x * z = z ^ 2 * x := by
      have h := congrArg (fun h : H => h * x) (hinvert cubicGenerator)
      simpa only [mul_assoc, inv_mul_cancel, mul_one, cubic_relations.2.1,
        z, ← map_pow, Prod.pow_mk, one_pow] using h
    have hgz : (x * i (a,c)) * z = z ^ 2 * (x * i (a,c)) := by
      calc
        (x * i (a,c)) * z = x * (i (a,c) * z) := mul_assoc _ _ _
        _ = x * (z * i (a,c)) := by rw [hcz.eq]
        _ = (x * z) * i (a,c) := (mul_assoc _ _ _).symm
        _ = z ^ 2 * (x * i (a,c)) := by rw [hxz, mul_assoc]
    have hr := finrank_range_inverting_cubic (ρ z) (ρ (x * i (a,c)))
      (by rw [← map_pow, hz3, map_one]) hzfree
      (by rw [← map_mul, hg, map_one])
      (by rw [← map_pow, ← map_mul, ← map_mul, hgz])
    have hd : Module.finrank (ZMod 2) V = 8 := f.finrank_eq.trans finrank_tensorSpace
    rw [hd] at hr
    intro htwo
    have he : Module.finrank (ZMod 2)
        (LinearMap.range (ρ (x * i (a,c)) - 1)) = 2 := htwo
    rw [he] at hr
    omega

end Representation.RankTwo.Imprimitive.AlternatingSixTensor

namespace Representation.RankTwo.Imprimitive.AlternatingSixTensor

/-- The literal model supplies every extension and tensor premise of the source
adapter, including the full normal product and the outer inversion relation. -/
theorem model_via_source_not_rankTwo (g : GroupModel) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (movedSpace representation g) ≠ 2 := by
  apply source_not_rankTwo representation base base_injective outer outer_sq
    ?_ ?_ (LinearEquiv.refl (ZMod 2) TensorSpace) (fun _ _ => rfl) g hg
  · apply top_unique
    intro b _
    obtain ⟨a, rfl | rfl⟩ := two_cosets b
    · exact Subgroup.mem_sup_right ⟨a, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers outer))
        (Subgroup.mem_sup_right ⟨a, rfl⟩)
  · intro c
    simpa only [map_one] using outer_conjugates_base 1 c

end Representation.RankTwo.Imprimitive.AlternatingSixTensor