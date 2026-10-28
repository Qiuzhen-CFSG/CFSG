module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.Normalization
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity

/-!
# Inner–coefficient coverage for binary triality automorphisms

First normalize the actual positive Sylow subgroup by an inner automorphism.
An alignment of the four signed simple-root groups then reduces the problem
to their parameter maps. Parameter rigidity realizes those maps by a single
cubic coefficient automorphism and conjugation by an element of the actual
torus. Generation then identifies the resulting automorphism on the whole
central quotient.

The conditional reduction is retained, and `binary_inner_coefficient`
discharges all three geometric premises for every positive binary exponent,
including one. Its simplicity and perfectness instances may be inherited
from the component in an application; no independent certification is needed.

Source: GLS3 2.5.1, 2.5.8 and 2.5.12(b,c,d,f)
(`refs/KGroup/GLS3/chapter2.tex`); Steinberg, Theorem 36 and Theorem 30,
steps (1)--(4) (`refs/KGroup/GLS3/Chapter2St1.tex`). The coefficient field
is GF(q³), retaining the order-three contribution in Notation A.2.5 of
Aschbacher--Smith (`refs/quasithin.pdf`, printed p.33).
-/

public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage
open Parabolics ConcreteBruhat

/-- The root-geometric route to the exact inner--coefficient decomposition.
The three explicit premises are upstream mathematical obligations. -/
theorem inner_coefficient_of_root_geometry (P : Parameters) (hp : P.prime = 2)
    (hgen : Subgroup.closure (rootGenerators P hp) = ⊤)
    (halign : ∀ a : MulAut (Carrier P),
      (unipotent P).map a.toMonoidHom = unipotent P →
      ∃ u ∈ unipotent P, PreservesRootFrame P hp (MulAut.conj u * a))
    (hparameters : ∀ a : MulAut (Carrier P), PreservesRootFrame P hp a →
      ∃ t ∈ torus P, ∃ e : CoefficientAut P,
        ∀ s i r, a (rootElement P hp s i r) =
          t * rootElement P hp s i (coefficientRootField P e i r) * t⁻¹)
    (a : MulAut (Carrier P)) :
    ∃ g : Carrier P, ∃ e : CoefficientAut P,
      a = MulAut.conj g * coefficientAction P e := by
  obtain ⟨g, hg⟩ := exists_inner_unipotent_invariant P hp a
  obtain ⟨u, _, hu⟩ := halign (MulAut.conj g * a) hg
  obtain ⟨t, _, e, he⟩ := hparameters (MulAut.conj u * (MulAut.conj g * a)) hu
  have ha := eq_inner_coefficient_of_root_formulas P hp hgen _ t e he
  refine ⟨g⁻¹ * u⁻¹ * t, e, ?_⟩
  have hcancel : a = (MulAut.conj g)⁻¹ * (MulAut.conj u)⁻¹ *
      (MulAut.conj t * coefficientAction P e) := by
    rw [← ha]
    group
  simpa only [map_mul, map_inv, mul_assoc] using hcancel

/-- Every automorphism of the genuine binary triality carrier is inner followed
by the existing cubic coefficient action. All root-geometric premises are
discharged, including at f = 1, where the coefficient field is GF(8). -/
theorem binary_inner_coefficient (f : ℕ) (hf : 0 < f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (a : MulAut (BinaryCarrier f hf)) :
    ∃ g : BinaryCarrier f hf, ∃ e : CoefficientAut (binaryParameters f hf),
      a = MulAut.conj g * coefficientAction (binaryParameters f hf) e :=
  inner_coefficient_of_root_geometry (binaryParameters f hf) rfl
    (RootGeometry.rootGenerators_closure_eq_top f hf)
    (RootGeometry.exists_unipotent_rootFrame f hf)
    (binary_parameters_of_preservesRootFrame f hf) a

end Triality.Standard.OuterOdd.Coverage
