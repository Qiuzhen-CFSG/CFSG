module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.DualSpaces
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Equivariant annihilation for the outer M22 code

The native coordinate pairing reverses inclusions of cocode subspaces and
identifies V/ann(P) with P*, as well as (cocode/P)* with ann(P). Both linear
equivalences intertwine the literal stabilizer actions. Cyclic displacement
is unchanged by this duality. These constructions do not identify a module
from its dimension and do not assume any chief-factor conclusion.

Source: Aschbacher--Smith, H.16.4(1)--(3), printed p.403, combined manuscript
of 1 March 2004. The remaining identification with the six-point core and
the dual conjugation module must be supplied through actual action maps.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag

/-- Each cyclic actor has the same displacement on the actual code and
cocode; this is not asserted for arbitrary noncyclic subgroups. -/
theorem code_cocode_fixedCodim (g : m22PairStabilizer) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) =
      fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) := by
  have he := fixedCodim_map_equivariant m22OuterCodeRepresentation
    m22OuterCocodeRepresentation.dual (MonoidHom.id m22PairStabilizer)
    m22CodeCocodeDuality m22CodeCocodeDuality_equivariant (Subgroup.zpowers g)
  simpa only [Subgroup.map_id, fixedCodim_zpowers_dual] using he

/-- Annihilation using the genuine coordinate code/cocode pairing. -/
def annihilator (P : Submodule (ZMod 2) M22Cocode) : Submodule (ZMod 2) M22Code :=
  P.dualAnnihilator.comap m22CodeCocodeDuality.toLinearMap

theorem annihilator_map (P : Submodule (ZMod 2) M22Cocode) :
    (annihilator P).map m22CodeCocodeDuality.toLinearMap = P.dualAnnihilator :=
  Submodule.map_comap_eq_of_surjective m22CodeCocodeDuality.surjective _

theorem annihilator_finrank (P : Submodule (ZMod 2) M22Cocode) :
    Module.finrank (ZMod 2) P + Module.finrank (ZMod 2) (annihilator P) = 10 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  rw [← annihilator_map, LinearEquiv.finrank_map_eq, finrank_m22Cocode] at hd
  exact hd

theorem annihilator_le_iff (P Q : Submodule (ZMod 2) M22Cocode) :
    annihilator P ≤ annihilator Q ↔ Q ≤ P := by
  calc
    _ ↔ (annihilator P).map m22CodeCocodeDuality.toLinearMap ≤
        (annihilator Q).map m22CodeCocodeDuality.toLinearMap :=
      (Submodule.map_le_map_iff_of_injective m22CodeCocodeDuality.injective _ _).symm
    _ ↔ Q ≤ P := by
      rw [annihilator_map, annihilator_map, Subspace.dualAnnihilator_le_dualAnnihilator_iff]

theorem annihilator_injective : Function.Injective annihilator := by
  intro P Q he
  apply le_antisymm
  · exact (annihilator_le_iff Q P).mp he.ge
  · exact (annihilator_le_iff P Q).mp he.le

theorem annihilator_lt_iff (P Q : Submodule (ZMod 2) M22Cocode) :
    annihilator P < annihilator Q ↔ Q < P := by
  simp only [lt_iff_le_not_ge, annihilator_le_iff]

theorem codeFixedSpace_eq_annihilator_commutator (K : Subgroup m22PairStabilizer) :
    fixedSpace m22OuterCodeRepresentation K =
      annihilator (Coinvariants.ker (m22OuterCocodeRepresentation.comp K.subtype)) := by
  ext v
  change (∀ g : K, m22OuterCodeRepresentation g.val v = v) ↔
    m22CodeCocodeDuality v ∈
      (Coinvariants.ker (m22OuterCocodeRepresentation.comp K.subtype)).dualAnnihilator
  rw [← Representation.invariants_dual_eq_commutator_annihilator]
  constructor
  · intro hv g
    change m22OuterCocodeRepresentation.dual g.val (m22CodeCocodeDuality v) =
      m22CodeCocodeDuality v
    rw [← m22CodeCocodeDuality_equivariant, hv g]
  · intro hv g
    apply m22CodeCocodeDuality.injective
    rw [m22CodeCocodeDuality_equivariant]
    exact hv g

/-- Restricting the coordinate pairing to P identifies V/ann(P) with P*. -/
def quotientDualEquiv (P : Submodule (ZMod 2) M22Cocode) :
    (M22Code ⧸ annihilator P) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) P :=
  (Submodule.Quotient.equiv (annihilator P) P.dualAnnihilator
    m22CodeCocodeDuality (annihilator_map P)).trans (Subspace.quotAnnihilatorEquiv P)

theorem quotientDualEquiv_mk (P : Submodule (ZMod 2) M22Cocode)
    (v : M22Code) (u : P) :
    quotientDualEquiv P ((annihilator P).mkQ v) u = m22CodeCocodeDuality v u := rfl

/-- The dual of the literal cocode quotient identifies with ann(P). -/
def quotientDualAnnihilatorEquiv (P : Submodule (ZMod 2) M22Cocode) :
    Module.Dual (ZMod 2) (M22Cocode ⧸ P) ≃ₗ[ZMod 2] annihilator P :=
  P.dualQuotEquivDualAnnihilator.trans
    (m22CodeCocodeDuality.ofSubmodule' P.dualAnnihilator).symm

theorem pairing_quotientDualAnnihilatorEquiv (P : Submodule (ZMod 2) M22Cocode)
    (f : Module.Dual (ZMod 2) (M22Cocode ⧸ P)) (u : M22Cocode) :
    m22CodeCocodeDuality (quotientDualAnnihilatorEquiv P f).val u = f (P.mkQ u) := by
  change m22CodeCocodeDuality (m22CodeCocodeDuality.symm
    (P.dualQuotEquivDualAnnihilator f).val) u = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (H : Subgroup m22PairStabilizer)
variable (P : Subrepresentation (m22OuterCocodeRepresentation.comp H.subtype))

/-- An invariant cocode subspace has an invariant code annihilator. -/
def annihilatorSubrepresentation :
    Subrepresentation (m22OuterCodeRepresentation.comp H.subtype) where
  toSubmodule := annihilator P.toSubmodule
  apply_mem_toSubmodule g v hv := by
    change m22CodeCocodeDuality (m22OuterCodeRepresentation g.val v) ∈
      P.toSubmodule.dualAnnihilator
    rw [m22CodeCocodeDuality_equivariant]
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro u hu
    exact (Submodule.mem_dualAnnihilator _).mp hv _ (P.apply_mem_toSubmodule g⁻¹ hu)

theorem quotientDualEquiv_equivariant (g : H)
    (v : M22Code ⧸ annihilator P.toSubmodule) :
    quotientDualEquiv P.toSubmodule
        ((annihilatorSubrepresentation H P).quotientRepresentation g v) =
      P.toRepresentation.dual g (quotientDualEquiv P.toSubmodule v) := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply LinearMap.ext
  intro u
  change m22CodeCocodeDuality (m22OuterCodeRepresentation g.val w) u.val =
    m22CodeCocodeDuality w (m22OuterCocodeRepresentation g.val⁻¹ u.val)
  exact LinearMap.congr_fun (m22CodeCocodeDuality_equivariant g.val w) u.val

theorem quotientDualAnnihilatorEquiv_equivariant (g : H)
    (f : Module.Dual (ZMod 2) (M22Cocode ⧸ P.toSubmodule)) :
    quotientDualAnnihilatorEquiv P.toSubmodule (P.quotientRepresentation.dual g f) =
      (annihilatorSubrepresentation H P).toRepresentation g
        (quotientDualAnnihilatorEquiv P.toSubmodule f) := by
  apply Subtype.ext
  apply m22CodeCocodeDuality.injective
  apply LinearMap.ext
  intro u
  change m22CodeCocodeDuality
      (quotientDualAnnihilatorEquiv P.toSubmodule (P.quotientRepresentation.dual g f)).val u =
    m22CodeCocodeDuality (m22OuterCodeRepresentation g.val
      (quotientDualAnnihilatorEquiv P.toSubmodule f).val) u
  rw [pairing_quotientDualAnnihilatorEquiv, m22CodeCocodeDuality_equivariant]
  change f (P.quotientRepresentation g⁻¹ (P.toSubmodule.mkQ u)) =
    m22CodeCocodeDuality (quotientDualAnnihilatorEquiv P.toSubmodule f).val
      (m22OuterCocodeRepresentation g.val⁻¹ u)
  exact (pairing_quotientDualAnnihilatorEquiv P.toSubmodule f
    (m22OuterCocodeRepresentation g.val⁻¹ u)).symm

end MathieuCode.Hexad.ChiefFlag
