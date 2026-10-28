module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.Mathieu.M23.Basic
public import Theory.Mathieu.M24.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The remaining Mathieu centralizer tables

Specifications for Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(4)–(7), printed pp.1171–1172. These definitions do not assert the tables.
The fixed subgroups belong to automorphisms of the actual Witt-design models.
The covering-group and central-quotient transports are separate obligations.

Notation E.2.16, printed p.228, explicitly defines Q₈² and D₈³ as central
products with the centers identified. The kernel descriptions below retain
embedded factors, commutation, the order-two intersections, and generation.
The slash denotes an extension with the denominator as normal kernel; no
splitting is asserted. In the M₂₂ outer case Sz(2) is the actual Suzuki matrix
group at parameter zero, not a name attached to an arbitrary group of order 20.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

open Subgroup Sporadic.Mathieu

abbrev C2 := Multiplicative (ZMod 2)
abbrev Elementary (n : ℕ) := Fin n → C2
abbrev A5 := alternatingGroup (Fin 5)
abbrev S3 := Equiv.Perm (Fin 3)
abbrev S4 := Equiv.Perm (Fin 4)
abbrev S5 := Equiv.Perm (Fin 5)
abbrev L3Two := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
noncomputable abbrev SzTwo := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0

/-- Two actual commuting dihedral eights with their centers identified. -/
def IsDihedralSquareProduct (Q : Type*) [Group Q] : Prop :=
  ∃ B D : Subgroup Q,
    Nonempty (B ≃* DihedralGroup 4) ∧ Nonempty (D ≃* DihedralGroup 4) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤

/-- The central product (D₈ * D₈) * D₈ of source 16.1.5(7). -/
def IsDihedralCubeProduct (Q : Type*) [Group Q] : Prop :=
  ∃ B D : Subgroup Q,
    IsDihedralSquareProduct B ∧ Nonempty (D ≃* DihedralGroup 4) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤

/-- S₃/Q₈², with an actual normal quaternion central-product kernel. -/
def IsM12QuaternionExtension (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    Nonempty (QuaternionCentralProductData Q) ∧ Nonempty (C ⧸ Q ≃* S3)

/-- L₃(2)/D₈³, with an actual normal dihedral central-product kernel. -/
def IsM24DihedralExtension (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    IsDihedralCubeProduct Q ∧ Nonempty (C ⧸ Q ≃* L3Two)

/-- The inner and outer M₁₂ alternatives, retaining both inner shapes. -/
def M12InvolutionAlternative (r : MulAut M12) : Prop :=
  ((∃ g, r = MulAut.conj g) ∧
    (IsM12QuaternionExtension r.fixedSubgroup ∨ Nonempty (r.fixedSubgroup ≃* C2 × S5))) ∨
  ((¬ ∃ g, r = MulAut.conj g) ∧ Nonempty (r.fixedSubgroup ≃* C2 × A5))

/-- The inner and both outer M₂₂ alternatives, without an assumed splitting. -/
def M22InvolutionAlternative (r : MulAut M22) : Prop :=
  ((∃ g, r = MulAut.conj g) ∧
    Nonempty (GroupExtension (Elementary 4) r.fixedSubgroup S4)) ∨
  ((¬ ∃ g, r = MulAut.conj g) ∧
    (Nonempty (GroupExtension (Elementary 3) r.fixedSubgroup L3Two) ∨
      Nonempty (GroupExtension (Elementary 4) r.fixedSubgroup SzTwo)))

/-- Every M₂₃ involutory automorphism is inner, with E₁₆ kernel and L₃(2) quotient. -/
def M23InvolutionAlternative (r : MulAut M23) : Prop :=
  (∃ g, r = MulAut.conj g) ∧
    Nonempty (GroupExtension (Elementary 4) r.fixedSubgroup L3Two)

/-- Every M₂₄ involutory automorphism is inner, with either exact kernel shape. -/
def M24InvolutionAlternative (r : MulAut M24) : Prop :=
  (∃ g, r = MulAut.conj g) ∧
    (IsM24DihedralExtension r.fixedSubgroup ∨
      Nonempty (GroupExtension (Elementary 6) r.fixedSubgroup S5))

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
