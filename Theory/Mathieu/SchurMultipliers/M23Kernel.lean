module

public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# The trivial Schur multiplier of native M₂₃

Every finite perfect central cover of the actual Mathieu model has trivial
kernel. The source proof first excludes odd primes, then rules out a perfect
double cover by constructing a section over the odd-index heptad stabilizer.
This module exposes the resulting finite-cover and multiplier interfaces.

The universal-kernel theorem uses the constructed universal projection, as
required by the M₂₃-image exclusion in 15.3.38. The central-quotient and
two-core applications retain the given comparison with M₂₃ and the literal
quotient homomorphism; the latter is the map used in the surviving M₂₃
case of 2.3.9(7)(f).

Source: Aschbacher–Smith I.1.1 and I.1.3, printed pp.407–408, and GLS3,
Section 6.1 (the trivial M₂₃ entry). The complete local proof is in
`M23TwoKernelSource`; no additional multiplier or splitting premise remains.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace Sporadic.Mathieu.SchurMultipliers

/-- Every finite perfect central cover of native M₂₃ has trivial kernel. -/
theorem m23_cover_kernel_eq_bot {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) : f.toMonoidHom.ker = ⊥ :=
  M23TwoKernelSource.kernel_eq_bot f

/-- In particular, two does not divide the kernel order of an M₂₃ cover. -/
theorem m23_cover_kernel_not_two {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) : ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  rw [(Subgroup.card_eq_one.mpr (m23_cover_kernel_eq_bot f))]
  decide

/-- The exact canonical M₂₃ kernel premise of the 15.3.38 cover embedding
argument, discharged for the constructed universal projection. -/
theorem m23_universalProjection_ker_eq_bot : (universalProjection M23).ker = ⊥ :=
  m23_cover_kernel_eq_bot (universalCover M23)

/-- The trivial M₂₃ multiplier for every chosen quasisimple covering.
The universal property is unnecessary for this stronger statement. -/
theorem m23_schurMultiplier
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (f : Covering E M23) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 1)) := by
  let c : Cover E M23 :=
    { toMonoidHom := f.toMonoidHom
      surjective := f.surjective
      isPerfect := inferInstance
      ker_le_center := f.ker_le_center }
  have hk : f.toMonoidHom.ker = ⊥ := m23_cover_kernel_eq_bot c
  have : Subsingleton f.toMonoidHom.ker := by
    rw [hk]
    infer_instance
  let : Unique f.toMonoidHom.ker := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  let : Unique (Multiplicative (ZMod 1)) := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  exact ⟨MulEquiv.ofUnique⟩

/-- The source central-quotient cover, with its literal marked projection. -/
theorem m23_centralQuotient_kernel_eq_bot
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* M23) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center E))).ker = ⊥ :=
  m23_cover_kernel_eq_bot (centralQuotientCover e)

/-- A finite perfect group whose marked central quotient is M₂₃ is centerless. -/
theorem m23_center_eq_bot_of_centralQuotientEquiv
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* M23) : center E = ⊥ := by
  rw [← centralQuotientCover_ker e]
  exact m23_centralQuotient_kernel_eq_bot e

/-- The exact two-core quotient projection in the surviving M₂₃ cover case.
Quasisimplicity supplies centrality of O₂(E); no kernel premise is assumed. -/
theorem m23_pCoreQuotient_kernel_eq_bot
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (e : E ⧸ pCore 2 E ≃* M23) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))).ker = ⊥ := by
  let f : Cover E M23 :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
        exact IsQuasisimple.pCore_le_center 2 }
  exact m23_cover_kernel_eq_bot f

/-- The marked M₂₃ quotient forces the original quasisimple group's two-core
to be trivial, discharging the covering-kernel obstruction in 2.3.9(7)(f). -/
theorem m23_pCore_eq_bot_of_quotientEquiv
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (e : E ⧸ pCore 2 E ≃* M23) : pCore 2 E = ⊥ := by
  have hk := m23_pCoreQuotient_kernel_eq_bot e
  rwa [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk'] at hk

end Sporadic.Mathieu.SchurMultipliers
