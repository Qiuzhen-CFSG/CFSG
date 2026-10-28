module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.CoverComparison
public import CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.SpecificGroups.PSL3.OuterSolvable
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# The original ambient group in the faithful Hermitian image

The coordinate homomorphism conjugates the given binary action and maps the
specified component onto the literal Hermitian image. Its range is therefore
an actual copy of the original faithful ambient group. Perfectness of the
component, self-centralization of F*(G), and solvability of the outer group
of its actual PSL₃ central quotient imply G∞ = L. Surjective functoriality
then proves the exact residual equation required by Chapter H's
`SourceOvergroup`, before using that API.

The resulting congruence formula retains GL₃ diagonal factors and coefficient
automorphisms. Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
K.3.2(c), printed pp.454–456, and H.4.2–H.4.4, pp.380–381.
-/

@[expose] public section
open Theory.GroupTheory Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

private theorem quotient_solvable_of_outer [L.Normal]
    (hC : centralizer (L : Set G) ≤ L) [Group.IsSolvable (MulAut.Outer L)] :
    Group.IsSolvable (G ⧸ L) := by
  apply Group.isSolvable_of_isSolvable_injective (f := MulAut.outerAction L)
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.map _ _ _ _).ker = ⊥
  rw [QuotientGroup.ker_map, MulAut.conjNormal_comap_innerSubgroup,
    sup_eq_left.mpr hC, QuotientGroup.map_mk'_self]

/-- The source residual equation follows from the actual central quotient. -/
theorem residual_eq_of_linearThree_quotient [Finite G] [L.Normal] [Group.IsPerfect L]
    (hF : generalizedFitting G = L) (B : BinaryField)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier) :
    solvableResidual G = L := by
  let : Group.IsSolvable (MulAut.Outer
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)) :=
    Matrix.PSL3.OuterSolvable.outer_isSolvable_of_standard_inputs B.Carrier
      (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card B.Carrier
        B.degree_pos B.card_eq)
      (Matrix.PSL3.OuterSolvable.standardOuter_isSolvable B.Carrier)
  let : Group.IsSolvable (MulAut.Outer L) :=
    Group.isSolvable_of_isSolvable_injective (MulAut.centralQuotientOuter_injective e)
  have hC : centralizer (L : Set G) ≤ L := by
    simpa only [hF] using centralizer_generalizedFitting_le G
  let : Group.IsSolvable (G ⧸ L) := quotient_solvable_of_outer L hC
  exact le_antisymm (solvableResidual_le_of_solvable_quotient L)
    (le_solvableResidual_of_isPerfect L)

variable (n : ℕ) [NeZero n]

local instance : Module (ZMod 2) (F n) := (fixedBinaryAlgebra n).toModule

def coordinateHom (e : V ≃ₗ[ZMod 2] Space n) : G →* (Space n ≃ₗ[ZMod 2] Space n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n)).toMonoidHom.comp
    ((Units.mapEquiv e.conjRingEquiv.toMulEquiv).toMonoidHom.comp ρ.asGroupHom)

@[simp] theorem coordinateHom_apply (e : V ≃ₗ[ZMod 2] Space n) (g : G) (X : Space n) :
    coordinateHom ρ n e g X = e (ρ g (e.symm X)) := rfl

theorem coordinateHom_injective (hf : Function.Injective ρ) (e : V ≃ₗ[ZMod 2] Space n) :
    Function.Injective (coordinateHom ρ n e) := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro v
  apply e.injective
  simpa only [coordinateHom_apply, e.symm_apply_apply] using
    LinearEquiv.congr_fun he (e v)

variable (h : ActionEquiv (ρ.comp L.subtype) (overgroupAction n (binaryImage n)))

/-- The literal image of the original ambient representation in tensor coordinates. -/
def sourceImage : Subgroup (Space n ≃ₗ[ZMod 2] Space n) :=
  (coordinateHom ρ n h.linearEquiv).range

theorem coordinateHom_on_component (g : L) :
    coordinateHom ρ n h.linearEquiv g = (h.groupEquiv g).val := by
  apply LinearEquiv.ext
  intro X
  change h.linearEquiv (ρ g (h.linearEquiv.symm X)) = (h.groupEquiv g).val X
  rw [show ρ g (h.linearEquiv.symm X) =
    (ρ.comp L.subtype) g (h.linearEquiv.symm X) from rfl,
    h.intertwines, h.linearEquiv.apply_symm_apply]
  rfl

theorem component_map : L.map (coordinateHom ρ n h.linearEquiv) = binaryImage n := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [coordinateHom_on_component ρ L n h ⟨g, hg⟩]
    exact (h.groupEquiv ⟨g, hg⟩).property
  · intro hf
    let g := h.groupEquiv.symm ⟨f, hf⟩
    refine ⟨g, g.property, ?_⟩
    rw [coordinateHom_on_component ρ L n h g]
    exact congrArg Subtype.val (h.groupEquiv.apply_symm_apply ⟨f, hf⟩)

/-- Faithfulness identifies the original group and its transported binary action. -/
def sourceActionEquiv (hf : Function.Injective ρ) :
    ActionEquiv ρ (overgroupAction n (sourceImage ρ L n h)) where
  groupEquiv := MonoidHom.ofInjective (coordinateHom_injective ρ n hf h.linearEquiv)
  linearEquiv := h.linearEquiv
  intertwines g v := by
    change h.linearEquiv (ρ g v) = h.linearEquiv (ρ g (h.linearEquiv.symm (h.linearEquiv v)))
    rw [h.linearEquiv.symm_apply_apply]

theorem sourceImage_residual [Finite G] (hres : solvableResidual G = L) :
    SourceOvergroup n (sourceImage ρ L n h) := by
  let f := coordinateHom ρ n h.linearEquiv
  have hr := map_solvableResidual_eq f.rangeRestrict f.rangeRestrict_surjective
  change (solvableResidual f.range).map f.range.subtype = binaryImage n
  rw [← hr, map_map]
  change (solvableResidual G).map f = binaryImage n
  rw [hres]
  exact component_map ρ L n h

/-- All premises of the Chapter H overgroup API are discharged from the source structure. -/
theorem sourceImage_isSource [Finite G] [L.Normal] [Group.IsPerfect L]
    (hF : generalizedFitting G = L) (B : BinaryField)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier) :
    SourceOvergroup n (sourceImage ρ L n h) :=
  sourceImage_residual ρ L n h (residual_eq_of_linearThree_quotient L hF B e)

/-- Source application: every ambient actor has the permitted diagonal/field expression. -/
theorem sourceImage_congruence [Finite G] [L.Normal] [Group.IsPerfect L]
    (hF : generalizedFitting G = L) (B : BinaryField)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier) (g : G) :
    HasCongruenceExpression n (coordinateHom ρ n h.linearEquiv g) := by
  apply sourceOvergroup_hasCongruenceExpression n (sourceImage ρ L n h)
    (sourceImage_isSource ρ L n h hF B e)
  exact ⟨g, rfl⟩

/-- Application to the original source action after tensor scalar descent:
the image group, binary intertwiner and residual equation are all constructed.
The scalar-extension equivalence is the recognition premise which the cubic
module sieve must eventually supply; no overgroup or residual is assumed. -/
theorem exists_sourceImage_of_scalarExtension [Finite G] [L.Normal] [Group.IsPerfect L]
    [Module (F n) V] [FiniteDimensional (F n) V]
    (hf : Function.Injective ρ) (hF : generalizedFitting G = L) (B : BinaryField)
    (eQ : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (π : Cover n →* L) (hπ : Function.Surjective π)
    (τ : Representation (F n) (Cover n) V)
    (hrestrict : restrictScalars (k := ZMod 2) τ = (ρ.comp L.subtype).comp π)
    (hmodel : Nonempty ((extendScalars (E n) τ).Equiv (tensorAction n))) :
    ∃ M : Subgroup (Space n ≃ₗ[ZMod 2] Space n),
      SourceOvergroup n M ∧ Nonempty (ActionEquiv ρ (overgroupAction n M)) := by
  obtain ⟨e⟩ := HermitianDescent.binary_equiv_of_scalarExtension n τ hmodel
  rw [hrestrict] at e
  let h := hermitianActionEquiv (ρ.comp L.subtype) n π hπ
    (hf.comp L.subtype_injective) e
  exact ⟨sourceImage ρ L n h, sourceImage_isSource ρ L n h hF B eQ,
    ⟨sourceActionEquiv ρ L n h hf⟩⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition
