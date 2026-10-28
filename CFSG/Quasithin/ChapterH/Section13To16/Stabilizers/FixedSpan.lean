module

public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.CommonFour
public import CFSG.Quasithin.ChapterH.Section13To16.FixedSpanReduction

/-!
# The common-four geometry in the H.16.8 fixed-space-span argument

Every native elementary subgroup of order sixteen contains a native conjugate
of the literal common four. Conjugation preserves the codimension of the sum
of nonidentity element fixed spaces, and subgroup inclusion enlarges that sum.
Thus its codimension for any E16 is bounded by the codimension for this one
marked four-group. This applies to every finite-dimensional binary M23 action.

The code application combines that geometric theorem with the existing
7, 7, 4 dimension calculation and the actual code-model transport. Only those
independent fixed-space dimensions remain explicit; the native order, Sylow
classification and common-four coverage are proved inputs. This reduction
does not assert H.16.8 before its module calculations are supplied.

Source: Aschbacher–Smith H.14.1(6), H.14.2(1) and the proof of H.16.8,
printed pp.397,405, combined manuscript of 1 March 2004.
-/

public section

open Representation.BinaryOffender Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.ChapterH.Section13To16

private theorem common_codim_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M23 V) (g : M23) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ m23CommonKernel) =
      Module.finrank (ZMod 2)
        (V ⧸ fixedSpaceSpan ρ (m23CommonKernel.map (MulAut.conj g).toMonoidHom)) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  apply fixedSpaceSpan_codim_map_equivariant ρ ρ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective e
  intro a v
  change ρ g (ρ a v) = ρ (g * a * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- The proved H.14 coverage reduces every native E16 actor to the literal common four. -/
theorem m23_fixedSpan_codim_le_commonKernel {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M23 V) (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤
      Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ m23CommonKernel) := by
  obtain ⟨g, hg⟩ := standardM23_card16_contains_common_conjugate A hA hcard
  rw [common_codim_conj ρ g]
  have hm := Submodule.finrank_mono (fixedSpaceSpan_mono ρ hg)
  have h₁ := (fixedSpaceSpan ρ A).finrank_quotient_add_finrank
  have h₂ := (fixedSpaceSpan ρ
    (m23CommonKernel.map (MulAut.conj g).toMonoidHom)).finrank_quotient_add_finrank
  omega

/-- H.16.8 after the independent 7, 7, 4 fixed-space calculation on two marked elements.
All common-subgroup order, containment and conjugacy premises are discharged. -/
theorem m23Code_fixedSpan_bound_of_common_pair
    {a b : M23} (ha : a ∈ m23CommonKernel) (ha1 : a ≠ 1)
    (hb : b ∈ m23CommonKernel) (hb1 : b ≠ 1)
    (hfa : Module.finrank (ZMod 2)
      (fixedSpace m23CodeRepresentation (Subgroup.zpowers a)) = 7)
    (hfb : Module.finrank (ZMod 2)
      (fixedSpace m23CodeRepresentation (Subgroup.zpowers b)) = 7)
    (hab : Module.finrank (ZMod 2)
      ↥(fixedSpace m23CodeRepresentation (Subgroup.zpowers a) ⊓
        fixedSpace m23CodeRepresentation (Subgroup.zpowers b)) = 4)
    (A : Subgroup M23) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (Code ⧸ fixedSpaceSpan m23CodeRepresentation A) ≤ 1 :=
  (m23_fixedSpan_codim_le_commonKernel m23CodeRepresentation A hA hcard).trans
    (fixedSpan_codim_le_one_of_pair m23CodeRepresentation finrank_code
      ha ha1 hb hb1 hfa hfb hab)

/-- The same reduction for an actual M23 code model, using its group and linear markings. -/
theorem m23Code_fixedSpan_bound_of_common_pair_model
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : IsM23Code ρ)
    {a b : M23} (ha : a ∈ m23CommonKernel) (ha1 : a ≠ 1)
    (hb : b ∈ m23CommonKernel) (hb1 : b ≠ 1)
    (hfa : Module.finrank (ZMod 2)
      (fixedSpace m23CodeRepresentation (Subgroup.zpowers a)) = 7)
    (hfb : Module.finrank (ZMod 2)
      (fixedSpace m23CodeRepresentation (Subgroup.zpowers b)) = 7)
    (hab : Module.finrank (ZMod 2)
      ↥(fixedSpace m23CodeRepresentation (Subgroup.zpowers a) ⊓
        fixedSpace m23CodeRepresentation (Subgroup.zpowers b)) = 4)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤ 1 :=
  m23Code_fixedSpan_bound_of_native ρ hρ
    (m23Code_fixedSpan_bound_of_common_pair ha ha1 hb hb1 hfa hfb hab) A hA hcard

end CFSG.Quasithin.ChapterH.Section13To16
