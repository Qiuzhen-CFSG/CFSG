module
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.SevenMultiplicity.Sections
/-!
# Rigidity of saturated square-zero sections

If B=[B,D] contains an element acting without fixed vectors, equal D-fixed
codimensions of nested invariant spaces force equality: D, hence B, fixes
the intervening quotient, while the fixed-free element remains fixed-free
there. For a square-zero equivariant map, a constituent costing n dimensions
and an ambient budget of 2n therefore identify both its image and kernel
with that constituent. No splitting or semisimplicity is assumed.

Source application: Aschbacher--Smith C.1.34, printed pp.136--137, the
whole-central-omega saturated branch at a nontrivial quotient scalar.
The argument uses the section inequality of B.1.5(8), printed pp.69--70.
-/

public noncomputable section
open Subgroup Representation
open Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A component containing a fixed-free element makes a saturated nested section exact. -/
theorem subrepresentation_eq_of_fixedCodim_eq_fixedFree
    (ρ : Representation (ZMod 2) G V) (B D : Subgroup G) (hm : ⁅B,D⁆ = B)
    (a : G) (ha : a ∈ B) (hf : ∀ v, ρ a v = v → v = 0)
    (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (he : fixedCodim U.toRepresentation D = fixedCodim W.toRepresentation D) : U = W := by
  let N := sectionLower ρ U W
  have hn : fixedCodim N.toRepresentation D = fixedCodim U.toRepresentation D := by
    have hh := fixedCodim_map_equivariant N.toRepresentation U.toRepresentation
      (MonoidHom.id G) (sectionLowerEquiv ρ hUW) (fun _ _ => rfl) D
    simpa only [Subgroup.map_id] using hh
  have hb := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation N D
  have hz : fixedCodim N.quotientRepresentation D = 0 := by omega
  have hD : D ≤ N.quotientRepresentation.ker := by
    intro d hd
    apply LinearMap.ext
    intro v
    exact (show v ∈ fixedSpace N.quotientRepresentation D from
      (fixedCodim_eq_zero_iff _ _).mp hz ▸ Submodule.mem_top) ⟨d,hd⟩
  have hB : B ≤ N.quotientRepresentation.ker := by
    rw [←hm]
    exact (commutator_mono le_rfl hD).trans (commutator_le_right _ _)
  have hfree := FixedFreeSections.quotient_fixedFree W.toRepresentation a
    (FixedFreeSections.subrepresentation_fixedFree ρ a hf W) N
  apply le_antisymm hUW
  intro v hv
  have hq : N.toSubmodule.mkQ ⟨v,hv⟩ = 0 :=
    hfree _ (LinearMap.congr_fun (hB ha) _)
  exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hq

/-- A square-zero equivariant displacement with a saturated two-section budget
has identical image and kernel, equal to the prescribed constituent. -/
theorem square_zero_range_ker_eq_of_saturation
    (ρ : Representation (ZMod 2) G V) (B D : Subgroup G) (hm : ⁅B,D⁆ = B)
    (a : G) (ha : a ∈ B) (hf : ∀ v, ρ a v = v → v = 0)
    (f : V →ₗ[ZMod 2] V) (hs : ∀ v, f (f v) = 0)
    (hc : ∀ g v, f (ρ g v) = ρ g (f v))
    (I : Subrepresentation ρ) (hI : I.toSubmodule ≤ f.range)
    (n : ℕ) (hi : n ≤ fixedCodim I.toRepresentation D)
    (ht : fixedCodim ρ D ≤ 2*n) :
    f.range = I.toSubmodule ∧ f.ker = I.toSubmodule ∧
      Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I.toSubmodule := by
  let W : Subrepresentation ρ := ⟨f.range,by
    intro g v hv
    obtain ⟨w,rfl⟩ := hv
    exact ⟨ρ g w,hc g w⟩⟩
  let T : Subrepresentation ρ := ⟨f.ker,by
    intro g v hv
    change f (ρ g v) = 0
    rw [hc,show f v = 0 from hv,map_zero]⟩
  have hWT : W ≤ T := by
    rintro v ⟨w,rfl⟩
    exact hs w
  have mono (U W : Subrepresentation ρ) (h : U ≤ W) :
      fixedCodim U.toRepresentation D ≤ fixedCodim W.toRepresentation D := by
    have hh := fixedCodim_map_le_of_embedding W.toRepresentation U.toRepresentation
      (MonoidHom.id G) (Submodule.inclusion h) (Submodule.inclusion_injective h)
      (fun _ _ => rfl) D
    simpa only [Subgroup.map_id] using hh
  have hl := mono I W hI
  have hu := mono W T hWT
  let e : (V ⧸ T.toSubmodule) ≃ₗ[ZMod 2] W.toSubmodule := f.quotKerEquivRange
  have he (g : G) (v : V ⧸ T.toSubmodule) :
      e (T.quotientRepresentation g v) = W.toRepresentation g (e v) := by
    obtain ⟨v,rfl⟩ := T.toSubmodule.mkQ_surjective v
    exact Subtype.ext (hc g v)
  have hq := fixedCodim_map_equivariant T.quotientRepresentation W.toRepresentation
    (MonoidHom.id G) e he D
  simp only [Subgroup.map_id] at hq
  have hb := fixedCodim_quotient_add_subrepresentation_le ρ T D
  have hiw : fixedCodim I.toRepresentation D = fixedCodim W.toRepresentation D := by omega
  have hwt : fixedCodim W.toRepresentation D = fixedCodim T.toRepresentation D := by omega
  have eIW := subrepresentation_eq_of_fixedCodim_eq_fixedFree ρ B D hm a ha hf I W hI hiw
  have eWT := subrepresentation_eq_of_fixedCodim_eq_fixedFree ρ B D hm a ha hf W T hWT hwt
  have eW : f.range = I.toSubmodule := congrArg Subrepresentation.toSubmodule eIW.symm
  have eT : f.ker = I.toSubmodule := congrArg Subrepresentation.toSubmodule (eIW.trans eWT).symm
  refine ⟨eW,eT,?_⟩
  have hb := f.finrank_range_add_finrank_ker
  rw [eW,eT] at hb
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- The actual displacement induces an equivariant quotient-to-image equivalence
when its image and kernel are the same invariant space. -/
theorem quotient_equiv_of_range_ker_eq
    (ρ : Representation (ZMod 2) G V) (f : V →ₗ[ZMod 2] V)
    (hc : ∀ g v, f (ρ g v) = ρ g (f v)) (I : Subrepresentation ρ)
    (hr : f.range = I.toSubmodule) (hk : f.ker = I.toSubmodule) :
    ∃ e : (V ⧸ I.toSubmodule) ≃ₗ[ZMod 2] I.toSubmodule,
      (∀ v, (e (I.toSubmodule.mkQ v) : V) = f v) ∧
      ∀ g v, e (I.quotientRepresentation g v) = I.toRepresentation g (e v) := by
  let e : (V ⧸ I.toSubmodule) ≃ₗ[ZMod 2] I.toSubmodule :=
    ((Submodule.quotEquivOfEq I.toSubmodule f.ker hk.symm).trans f.quotKerEquivRange).trans
      (LinearEquiv.ofEq f.range I.toSubmodule hr)
  refine ⟨e,fun _ => rfl,?_⟩
  intro g v
  obtain ⟨v,rfl⟩ := I.toSubmodule.mkQ_surjective v
  exact Subtype.ext (hc g v)

end Representation.BinaryOffender
