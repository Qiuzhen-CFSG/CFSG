module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Literal
/-!
# Coefficients in the literal Hall--Janko norm corner

Corner coefficients are constant under both left and right multiplication by
the fixed subgroup, without any normality assumption. Expanding only the final
norm gives a 25-term formula for right multiplication by each literal e*g*e.
The explicit power-pair enumeration is injective on permutation point zero;
the existing subgroup order proves it is exhaustive.

This supplies the group-algebra step used in Coordinates.lean. The finite
right-coset identification is a separate obligation. Source application:
Guralnick--Malle Proposition 5.1; data provenance in Presentation/source/README.md.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2

namespace CoefficientTheory
local instance : Fintype subgroup := Fintype.ofFinite subgroup

abbrev PowerIndex := Fin 5 × Fin 5

def subgroupElement (t : PowerIndex) : subgroup :=
  ⟨leftGenerator ^ t.1.val * rightGenerator ^ t.2.val,
    Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)⟩

theorem subgroupElement_injective : Function.Injective subgroupElement := by
  have h : Function.Injective (fun t : PowerIndex =>
      (leftTable ^ t.1.val * rightTable ^ t.2.val) (0 : Fin 100)) := by
    decide +kernel
  intro s t heq
  apply h
  have heq' := congrArg (fun p : subgroup => inclusion p.val (0 : Fin 100)) heq
  simpa only [subgroupElement, map_mul, map_pow, inclusion_leftGenerator,
    inclusion_rightGenerator] using heq'

def subgroupEquiv : PowerIndex ≃ subgroup :=
  Equiv.ofBijective subgroupElement <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨subgroupElement_injective, by
        rw [Fintype.card_prod, Fintype.card_fin,
          ← Nat.card_eq_fintype_card, card_subgroup]⟩

theorem norm_coeff [DecidablePred (· ∈ subgroup)] (g : Carrier) :
    (fiveNorm subgroup).coeff g = if g ∈ subgroup then 1 else 0 := by
  classical
  simp only [fiveNorm, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hg
  · rw [Finset.sum_eq_single (⟨g, hg⟩ : subgroup)]
    · simp
    · intro b _ hb
      simp only [ite_eq_right_iff]
      intro hbg
      exact (hb (Subtype.ext hbg)).elim
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    simp only [ite_eq_right_iff]
    intro hbg
    exact (hg (hbg ▸ b.property)).elim

theorem single_norm (p : subgroup) :
    MonoidAlgebra.single (p : Carrier) (1 : ZMod 2) * fiveNorm subgroup =
      fiveNorm subgroup := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp only [MonoidAlgebra.coeff_single_mul_apply, one_mul, norm_coeff]
  simp only [subgroup.mul_mem_cancel_left (subgroup.inv_mem p.property)]

theorem norm_single (p : subgroup) :
    fiveNorm subgroup * MonoidAlgebra.single (p : Carrier) (1 : ZMod 2) =
      fiveNorm subgroup := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp only [MonoidAlgebra.coeff_mul_single_apply, mul_one, norm_coeff]
  simp only [subgroup.mul_mem_cancel_right (subgroup.inv_mem p.property)]

theorem corner_single_left (he : IsIdempotentElem (fiveNorm subgroup))
    (z : he.Corner) (p : subgroup) :
    MonoidAlgebra.single (p : Carrier) (1 : ZMod 2) * z.val = z.val := by
  obtain ⟨r, hr⟩ := z.property
  rw [← hr, ← mul_assoc, ← mul_assoc, single_norm]

theorem corner_single_right (he : IsIdempotentElem (fiveNorm subgroup))
    (z : he.Corner) (p : subgroup) :
    z.val * MonoidAlgebra.single (p : Carrier) (1 : ZMod 2) = z.val := by
  obtain ⟨r, hr⟩ := z.property
  rw [← hr, mul_assoc, norm_single]

theorem coeff_double (he : IsIdempotentElem (fiveNorm subgroup))
    (z : he.Corner) (p q : subgroup) (g : Carrier) :
    z.val.coeff ((p : Carrier) * g * (q : Carrier)) = z.val.coeff g := by
  have hl := congrArg (fun a : MonoidAlgebra (ZMod 2) Carrier =>
    a.coeff ((p : Carrier) * g)) (corner_single_left he z p)
  have hr := congrArg (fun a : MonoidAlgebra (ZMod 2) Carrier =>
    a.coeff ((p : Carrier) * g * (q : Carrier))) (corner_single_right he z q)
  simp only [MonoidAlgebra.coeff_single_mul_mul, one_mul] at hl
  simp only [MonoidAlgebra.coeff_mul_single_mul, mul_one] at hr
  exact hr.symm.trans hl.symm

theorem coeff_mul_condensed (he : IsIdempotentElem (fiveNorm subgroup))
    (z : he.Corner) (g x : Carrier) :
    (z * condensed he g).val.coeff x =
      ∑ p : subgroup, z.val.coeff (x * (p : Carrier) * g⁻¹) := by
  have hz := ((Subsemigroup.mem_corner_iff he).mp z.property).2
  change (z.val * (fiveNorm subgroup * MonoidAlgebra.single g 1 * fiveNorm subgroup)).coeff x = _
  rw [← mul_assoc, ← mul_assoc, hz]
  classical
  simp only [fiveNorm, Finset.mul_sum, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_mul_single_apply, mul_one]
  exact Fintype.sum_equiv (Equiv.inv subgroup) _ _ (fun p => by simp)

end CoefficientTheory
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
