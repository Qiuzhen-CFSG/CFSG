module

public import Theory.Representation.Suzuki.SmallDegree.Reduction
public import Theory.Representation.Suzuki.SmallDegree.Classification
public import Theory.Representation.Suzuki.SmallDegree.Descent

/-!
# Small faithful binary representations of Suzuki groups

For every `m ≥ 1`, a faithful irreducible binary representation of the concrete
Suzuki matrix group with dimension less than `10*(2*m+1)` is equivalent to its
natural binary module. The equivalence intertwines the original matrix group
action, including for `m = 1` (Sz(8)).

Embed the defining field in the algebraic closure of the actual Schur field.
The absolute representation is a nonempty concrete Frobenius tensor. The
field-period divisibility and the binary dimension tower force its support to
be a singleton. Scalar descent and the natural-module automorphism intertwiners
then give the required binary equivalence. Every classification and descent
premise is discharged; no coefficient-field structure is required of the input.

Sources: Guralnick–Malle, *Classification of 2F-modules, II*, §3.1,
Lemma 8.3 and Theorem 8.1/Table 17; Aschbacher–Smith, reduction preceding
K.3.5–K.3.6, printed p.457.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural FrobeniusTensor

/-- Every small faithful irreducible binary Suzuki representation is the
natural module, with an actual linear intertwiner on the original matrix group.
This includes Sz(8) and requires no separately supplied field of definition. -/
theorem natural_equiv_of_smallDegree {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) :
    Nonempty (ρ.Equiv (natural m)) := by
  let := hirr
  let : Algebra (F m) (Closure ρ) :=
    (IsAlgClosed.lift : F m →ₐ[ZMod 2] Closure ρ).toRingHom.toAlgebra
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_nonempty_tensorRep_equiv hm
    (absoluteRep ρ) inferInstance (absoluteRep_injective ρ hfaith)
  exact natural_equiv_of_smallDegree_tensor_model ρ hm I hI
    (tensorRep_irreducible hm) (fun _ _ => tensorRep_equiv_imp_eq hm) e hsmall

end Representation.SuzukiSmallDegree
