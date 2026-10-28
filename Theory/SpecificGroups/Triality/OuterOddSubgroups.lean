module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.IsPerfect

/-!
# Cyclic outer groups for binary triality carriers

The full automorphism group of GF(q³) acts on the genuine elementary central
quotient from `StandardModel`. Its image in the actual outer quotient is cyclic.
The proved inner–coefficient decomposition makes that image the entire outer
group at binary field order. The final two theorems use the equality with the
binary parameters to establish cyclicity and the odd-subgroup restriction for
every parameter record with q = 2^f and f ≥ 1. Simplicity and perfectness may
be inherited through a source consumer's actual model isomorphism.

The general conditional reductions are retained. Their binary applications
now discharge coverage using the concrete signed-root geometry and parameter
rigidity from `Coverage`, including the endpoint q = 2.

Sources: GLS3 2.5.12(b,c,d,f), `refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith,
combined 1 March 2004 manuscript, printed p.510 and Remark A.2.4 / Notation A.2.5
on p.33, `refs/quasithin.pdf`. The coefficient field is GF(q³), including its
order-three automorphisms when q = 2.
-/

@[expose] public section
noncomputable section

namespace Triality.Standard.OuterOdd
open Theory.GroupTheory

/-- The entire cubic coefficient automorphism group is cyclic. -/
theorem coefficientAut_isCyclic (P : Parameters) : IsCyclic (CoefficientAut P) :=
  Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic

/-- Coefficient automorphisms, modulo the actual inner automorphisms of the carrier. -/
def outerCoefficientAction (P : Parameters) :
    CoefficientAut P →* MulAut.Outer (Carrier P) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (Carrier P))).comp (coefficientAction P)

/-- The constructed outer coefficient image is cyclic, without a coverage assumption. -/
theorem outerCoefficientRange_isCyclic (P : Parameters) :
    IsCyclic (outerCoefficientAction P).range := by
  let := coefficientAut_isCyclic P
  exact isCyclic_of_surjective (outerCoefficientAction P).rangeRestrict
    (outerCoefficientAction P).rangeRestrict_surjective

/-- Coverage means precisely that all outer classes have a coefficient representative.
The equation in the second clause is an equality of actual carrier automorphisms. -/
theorem outerCoefficientAction_surjective_iff (P : Parameters) :
    Function.Surjective (outerCoefficientAction P) ↔
      ∀ a : MulAut (Carrier P), ∃ g : Carrier P, ∃ e : CoefficientAut P,
        a = MulAut.conj g * coefficientAction P e := by
  constructor
  · intro h a
    obtain ⟨e, he⟩ := h (QuotientGroup.mk' (MulAut.innerSubgroup (Carrier P)) a)
    have hi : a / coefficientAction P e ∈ MulAut.innerSubgroup (Carrier P) :=
      QuotientGroup.eq_iff_div_mem.mp he.symm
    obtain ⟨g, hg⟩ := hi
    exact ⟨g, e, div_eq_iff_eq_mul.mp hg.symm⟩
  · intro h q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Carrier P)) q
    obtain ⟨g, e, rfl⟩ := h a
    refine ⟨e, ?_⟩
    have hg : QuotientGroup.mk' (MulAut.innerSubgroup (Carrier P)) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change QuotientGroup.mk' _ (coefficientAction P e) =
      QuotientGroup.mk' _ (MulAut.conj g * coefficientAction P e)
    rw [map_mul, hg, one_mul]

/-- Inner–coefficient coverage makes the full outer group cyclic. -/
theorem outer_isCyclic_of_inner_coefficient (P : Parameters)
    (hcover : ∀ a : MulAut (Carrier P), ∃ g : Carrier P, ∃ e : CoefficientAut P,
      a = MulAut.conj g * coefficientAction P e) :
    IsCyclic (MulAut.Outer (Carrier P)) := by
  let := coefficientAut_isCyclic P
  exact isCyclic_of_surjective (outerCoefficientAction P)
    ((outerCoefficientAction_surjective_iff P).mpr hcover)

/-- The odd outer restriction follows from the concrete inner–coefficient decomposition. -/
theorem outer_cyclicNormalOddQuotient_of_inner_coefficient (P : Parameters)
    (hcover : ∀ a : MulAut (Carrier P), ∃ g : Carrier P, ∃ e : CoefficientAut P,
      a = MulAut.conj g * coefficientAction P e) :
    HasCyclicNormalOddQuotient (MulAut.Outer (Carrier P)) := by
  let := outer_isCyclic_of_inner_coefficient P hcover
  exact hasCyclicNormalOddQuotient_of_isCyclic

/-- Coverage for the binary representatives suffices for every parameter record
at binary field order. Simplicity and perfectness may be inherited from a source
consumer; this reduction does not ask for independent model certification. -/
theorem outer_cyclicNormalOddQuotient_of_binary_coverage
    (hcover : ∀ (f : ℕ) (hf : 0 < f),
      IsSimpleGroup (BinaryCarrier f hf) → Group.IsPerfect (BinaryCarrier f hf) →
      ∀ a : MulAut (BinaryCarrier f hf), ∃ g : BinaryCarrier f hf,
        ∃ e : CoefficientAut (binaryParameters f hf),
          a = MulAut.conj g * coefficientAction (binaryParameters f hf) e)
    (P : Parameters) (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f)
    [IsSimpleGroup (Carrier P)] [Group.IsPerfect (Carrier P)] :
    HasCyclicNormalOddQuotient (MulAut.Outer (Carrier P)) := by
  have hP := P.eq_binaryParameters_of_q_eq f hf hq
  subst P
  exact outer_cyclicNormalOddQuotient_of_inner_coefficient _
    (hcover f hf inferInstance inferInstance)

/-- The full outer group of every genuine binary triality carrier is cyclic.
The parameter equality transports the proved inner–coefficient coverage,
retaining the full cubic coefficient field also at f = 1. -/
theorem outer_isCyclic (P : Parameters) (f : ℕ) (hf : 1 ≤ f)
    (hq : P.q = 2 ^ f)
    [IsSimpleGroup (Carrier P)] [Group.IsPerfect (Carrier P)] :
    IsCyclic (MulAut.Outer (Carrier P)) := by
  have hP := P.eq_binaryParameters_of_q_eq f hf hq
  subst P
  exact outer_isCyclic_of_inner_coefficient _ (Coverage.binary_inner_coefficient f hf)

/-- The odd outer restriction from the inspection on printed p.510, for every
binary parameter record. No automorphism-coverage premise remains. -/
theorem outer_cyclicNormalOddQuotient (P : Parameters) (f : ℕ) (hf : 1 ≤ f)
    (hq : P.q = 2 ^ f)
    [IsSimpleGroup (Carrier P)] [Group.IsPerfect (Carrier P)] :
    HasCyclicNormalOddQuotient (MulAut.Outer (Carrier P)) := by
  let := outer_isCyclic P f hf hq
  exact hasCyclicNormalOddQuotient_of_isCyclic

end Triality.Standard.OuterOdd
