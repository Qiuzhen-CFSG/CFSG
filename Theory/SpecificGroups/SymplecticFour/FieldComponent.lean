module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.AutomorphismFixerTransport
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual component in a symplectic field-involution fixed group

Descent identifies the fixed group with Sp₄ over the half field. Its derived
subgroup is simple: use the polar equivalence with A₆ at field order two, and
symplectic simplicity and perfectness otherwise. A component lies in the derived
subgroup by perfectness, and subnormality in that simple subgroup forces equality.
Mapping this equality back retains the ambient coefficient inclusion.

A compatible ambient equivalence therefore carries the actual component to the
embedded derived subfield group. This proves component placement once a field
conjugator is supplied; it does not assert existence of that conjugator. The
representative belongs to the full fixer, whose order is exactly two if every
fixer element is a power of the representative. That rigidity is a separate
calculation, including at the binary derived endpoint.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(4)
and 16.1.7(3a), printed pp.1171–1173; application in 16.3.5, pp.1178–1179.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.FieldComponent
open DiagramAutomorphisms DiagramAutomorphisms.FieldFixedResidual
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The derived half-field matrix group with its literal coefficient embedding. -/
noncomputable def embedded (n : ℕ) : Subgroup (Sp F) :=
  (commutator (Sp (halfField (F := F) n))).map
    (coefficientInclusion (halfField (F := F) n))

/-- The embedded derived group is the embedded two-residual, also at n = 1. -/
theorem embedded_eq_residual (n : ℕ) : embedded (F := F) n =
    (pResidual 2 (representative (F := F) n).fixedSubgroup).map
      (representative (F := F) n).fixedSubgroup.subtype :=
  (embedded_residual_eq _).symm

/-- Simplicity of the exact derived carrier over every positive binary degree. -/
theorem derived_isSimple {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    IsSimpleGroup (commutator (Sp F)) := by
  by_cases h : n = 1
  · have htwo : Nat.card F = 2 := by simpa [h] using hF
    let := alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
    exact (Binary.derivedEquivAlternatingSix htwo).isSimpleGroup
  · have hq : 3 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    let := perfect_of_card_gt_two (by omega : 2 < Nat.card F)
    let := SimpleQuotients.isSimpleGroup hq
    let e : commutator (Sp F) ≃* (Sp F ⧸ center (Sp F)) :=
      ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans
        Subgroup.topEquiv).trans EvenProjective.equiv
    exact e.isSimpleGroup

private theorem component_eq_derived {G : Type*} [Group G]
    [IsSimpleGroup (commutator G)] {P : Subgroup G} (hP : IsComponent G P) :
    P = commutator G := by
  let := hP.2
  have hle : P ≤ commutator G := by
    calc
      P = ⁅P, P⁆ := commutator_eq_self.symm
      _ ≤ ⁅⊤, ⊤⁆ := commutator_mono le_top le_top
  rcases hP.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (commutator G)) with hb | ht
  · have hpbot : P = ⊥ := by
      simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using
        congrArg (Subgroup.map (commutator G).subtype) hb
    let : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
    have : Nontrivial P := (QuotientGroup.mk'_surjective (center P)).nontrivial
    exact ((nontrivial_iff_ne_bot P).mp this hpbot).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

/-- Every component of this explicit fixed group is the embedded derived group. -/
theorem component_eq_embedded {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (2 * n)) (P : Subgroup (Sp F))
    (hP : IsComponentIn P (representative (F := F) n).fixedSubgroup) :
    P = embedded n := by
  let H := (representative (F := F) n).fixedSubgroup
  let e := fixedEquiv ((frobeniusEquiv F 2) ^ n)
  let := derived_isSimple hn (card_halfField hn hF)
  have he := component_eq_derived (hP.2.map_equiv e)
  have hi : (coefficientInclusion (halfField (F := F) n)).comp e.toMonoidHom =
      H.subtype := by
    ext x : 1
    exact fixedEquiv_inclusion _ x
  have hm := congrArg (Subgroup.map (coefficientInclusion (halfField (F := F) n))) he
  rw [map_map, hi, map_subgroupOf_eq_of_le hP.1] at hm
  exact hm

/-- A supplied field conjugator places the actual component, with its embedding. -/
theorem component_map_eq_embedded_of_compatible {G : Type*} [Group G]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ (2 * n))
    (e : G ≃* Sp F) (a : MulAut G) (he : ∀ x, e (a x) = representative n (e x))
    (P : Subgroup G) (hP : IsComponentIn P a.fixedSubgroup) :
    P.map e.toMonoidHom = embedded n := by
  have hf : a.fixedSubgroup.map e.toMonoidHom = (representative n).fixedSubgroup := by
    ext x
    rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    rw [← e.injective.eq_iff, he, e.apply_symm_apply]
  exact component_eq_embedded hn hF _ (hf ▸ hP.map e)

/-- The binary endpoint uses the actual polar equivalence with A₆. -/
noncomputable def binaryEmbeddedEquivAlternatingSix (hF : Nat.card F = 4) :
    embedded (F := F) 1 ≃* alternatingGroup (Fin 6) :=
  (MulEquiv.subgroupCongr (embedded_eq_residual 1)).trans
    (((pResidual 2 (representative (F := F) 1).fixedSubgroup).equivMapOfInjective
      (representative (F := F) 1).fixedSubgroup.subtype Subtype.val_injective).symm.trans
      (binaryFixedResidualEquivAlternatingSix hF))

/-- The field representative fixes the embedded derived subgroup pointwise. -/
theorem representative_mem_fixer (n : ℕ) :
    representative (F := F) n ∈ fixingSubgroup (MulAut (Sp F)) (embedded (F := F) n : Set (Sp F)) := by
  have hle : embedded (F := F) n ≤ (representative n).fixedSubgroup := by
    rw [embedded_eq_residual]
    exact map_subtype_le _
  exact fun x => (MulAut.mem_fixedSubgroup _ _).mp (hle x.property)

/-- Full fixer rigidity gives order exactly two, including the lower bound. -/
theorem card_fixer_eq_two_of_le_zpowers {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (2 * n))
    (hfix : fixingSubgroup (MulAut (Sp F)) (embedded (F := F) n : Set (Sp F)) ≤
      zpowers (representative n)) :
    Nat.card (fixingSubgroup (MulAut (Sp F)) (embedded (F := F) n : Set (Sp F))) = 2 := by
  have he := le_antisymm hfix (zpowers_le.mpr (representative_mem_fixer n))
  rw [he, Nat.card_zpowers, representative_orderOf hn hF]

end Theory.SpecificGroups.SymplecticFour.FieldComponent
