module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Section
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Marked

/-!
# Marking the binary action by the original product quotient

The action on `U/E` is pulled back along the specified decomposition
`G_E/Q_E ≃ S₃ × Ċ_E`. The second factor remains the actual image of
`C_G(E)`, with no assumed isomorphism type. Its elements act exactly as
the corresponding original centralizer elements.

`ActionData` specifies the intermediate action identities and the genuine
fixed-point lifting that the decomposition proof needs. It does not assert
the paired decomposition or its existence from source hypotheses. The source
assembly must construct this data from the original local geometry.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
open Descent.QuotientIdentification
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]
variable {Y T : Subgroup G} (d : MarkedDecomposition Y T E)
variable (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E)

/-- The section action in the original, partly unidentified product coordinates. -/
noncomputable def markedRepresentation :
    Representation (ZMod 2) (Equiv.Perm (Fin 3) × centralizerImage E) (SectionSpace V E) :=
  (coreQuotientRepresentation V E hcomm).comp d.equiv.symm.toMonoidHom

/-- The marking preserves the action of each original normalizer element. -/
theorem markedRepresentation_apply (g : lineNormalizer E) :
    markedRepresentation V E d hcomm (d.equiv (quotientMap E g)) =
      sectionRepresentation V E g := by
  change coreQuotientRepresentation V E hcomm (d.equiv.symm (d.equiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The second coordinate acts by the original centralizer conjugation. -/
theorem markedRepresentation_centralizer (c : centralizer (E : Set G)) :
    markedRepresentation V E d hcomm (1, centralizerImageMap E c) =
      sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c) := by
  rw [← d.centralizer_factor c]
  exact markedRepresentation_apply V E d hcomm _

omit [IsElementaryAbelian 2 (lineV V E)] in
/-- The selected `τ` belongs to the first marked factor. -/
theorem marked_tau_second :
    (d.equiv (quotientMap E ⟨d.tau, d.tau_mem.2⟩)).2 = 1 := by
  have ht : (⟨d.tau, d.tau_mem.2⟩ : lineNormalizer E) ∈
      (lineY Y E ⊔ zpowers d.tau).subgroupOf (lineNormalizer E) :=
    mem_sup_right (mem_zpowers d.tau)
  have hi := mem_map_of_mem (d.equiv.toMonoidHom.comp (quotientMap E)) ht
  rw [d.first_factor] at hi
  exact hi.2

/-- The intermediate action identities needed for the paired calculation.
These are outputs to be derived from the preceding local geometry, not
additional assumptions of a completed source theorem. In particular, no
decomposition, paired equivalence, or offender inequality is a field. -/
structure ActionData where
  y : lineNormalizer E
  y_mem : (y : G) ∈ lineY Y E
  y_order : orderOf (d.equiv (quotientMap E y)).1 = 3
  y_second : (d.equiv (quotientMap E y)).2 = 1
  tau_order : orderOf (d.equiv (quotientMap E ⟨d.tau, d.tau_mem.2⟩)).1 = 2
  norm_eq_zero : ∀ x : SectionSpace V E,
    x + sectionRepresentation V E y x + sectionRepresentation V E (y * y) x = 0
  fixedImage_eq : fixedImage V E d.tau =
    LinearMap.ker (sectionRepresentation V E ⟨d.tau, d.tau_mem.2⟩ - 1)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
