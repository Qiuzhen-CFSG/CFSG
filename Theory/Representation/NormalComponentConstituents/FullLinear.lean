module
public import Theory.Representation.NormalComponentConstituents.Exchanged
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Full constituent images and the center of a normal actor

If a constituent has centerless full image, the center of its normal actor
fixes it pointwise. Ambient irreducibility and faithfulness then kill that
center. Consequently a central constituent kernel is trivial. For binary
linear groups the scalar-center calculation applies in every positive degree.
A moved homogeneous constituent also detects outer conjugation, using the
inverse-action convention of `conjugateSubrepresentation`.

The original terminal action supplies ambient irreducibility, so this is an
alternative to the multiplier calculation in Aschbacher--Smith G.10.15(3),
printed p.363. It supplies faithfulness, not the final Sylow obstruction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Module
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- A central constituent kernel vanishes when the full image has trivial center. -/
theorem faithful_constituent_of_centerless_surjective
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (H : Subgroup D) [H.Normal] (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer ρ I) (hne : I ≠ ⊥)
    (hs : Function.Surjective (invariantSubspace ρ H I hI).toRepresentation.asGroupHom)
    (hc : center (LinearMap.GeneralLinearGroup (ZMod 2) I) = ⊥)
    (hk : (invariantSubspace ρ H I hI).toRepresentation.asGroupHom.ker ≤ center H) :
    Function.Injective (invariantSubspace ρ H I hI).toRepresentation.asGroupHom := by
  let f := (invariantSubspace ρ H I hI).toRepresentation.asGroupHom
  let Z := (center H).map H.subtype
  let : Z.Normal := inferInstanceAs ((center H).map H.subtype).Normal
  have hfix : I ≤ fixedSpace ρ Z := by
    intro u hu z
    obtain ⟨a, ha, he⟩ := z.property
    have ha1 : f a = 1 := by
      apply mem_bot.mp
      change f a ∈ (⊥ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I))
      rw [← hc]
      apply mem_center_iff.mpr
      intro b
      obtain ⟨c, rfl⟩ := hs b
      exact (map_mul f c a).symm.trans ((congrArg f (mem_center_iff.mp ha c)).trans (map_mul f a c))
    have hh := congrArg (fun t => ((t : LinearMap.GeneralLinearGroup (ZMod 2) I).val ⟨u,hu⟩ : V)) ha1
    change ρ (z : D) u = u
    change ρ (a : D) u = u at hh
    change (a : D) = (z : D) at he
    rwa [he] at hh
  have hZ : Z = ⊥ := by
    by_contra hz
    have hzero := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi Z hz
    exact hne (bot_unique (hzero ▸ hfix))
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro a ha
  have hz : (a : D) ∈ Z := ⟨a,hk ha,rfl⟩
  rw [hZ,mem_bot] at hz
  exact mem_bot.mpr (Subtype.ext hz)

/-- The full linear group over the binary field has trivial center. -/
theorem binary_full_center_eq_bot [FiniteDimensional (ZMod 2) V]
    (hd : 0 < finrank (ZMod 2) V) :
    center (LinearMap.GeneralLinearGroup (ZMod 2) V) = ⊥ := by
  let b := Module.finBasis (ZMod 2) V
  let e : LinearMap.GeneralLinearGroup (ZMod 2) V ≃*
      BinaryLinear.OuterCyclic.LinearGroup (finrank (ZMod 2) V) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)
  let q := e.trans (BinaryLinear.OuterCyclic.slEquivLinear _).symm
  apply bot_unique
  intro a ha
  have h := ((centerCongr q) ⟨a,ha⟩).property
  change q a ∈ center _ at h
  rw [BinaryLinear.OuterCyclic.binary_center_eq_bot hd, mem_bot] at h
  exact mem_bot.mpr (q.map_eq_one_iff.mp h)

/-- A moved homogeneous constituent detects a genuinely outer action. -/
theorem Homogeneous.IsIrrPlusWith.conjugation_not_inner
    {H X : Subgroup D} [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (x : X) (hx : I.map (ρ (x : D)⁻¹) ≠ I) :
    (MulAut.conjNormal (x : D) : MulAut H) ∉ MulAut.innerSubgroup H := by
  rintro ⟨a, ha⟩
  let R := invariantSubspace ρ H I hI.invariant
  have hh (b : H) :
      (MulAut.conjNormal (x : D) : MulAut H) b = a * b * a⁻¹ := by
    rw [← ha]
    rfl
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (R.toRepresentation.asGroupHom a)
  have he : Nonempty (Representation.Equiv R.toRepresentation
      (conjugateSubrepresentation ρ H R (x : D)).toRepresentation) := by
    let e : Representation.RepEquiv R.toRepresentation
        (conjugateRep R.toRepresentation (x : D)) := .mk c (by
      intro b
      apply LinearMap.ext
      intro u
      change R.toRepresentation a (R.toRepresentation b u) =
        R.toRepresentation ((MulAut.conjNormal (x : D) : MulAut H) b)
          (R.toRepresentation a u)
      rw [hh]
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one])
    exact ⟨(e.trans (conjugateSubrepresentationEquiv ρ H R (x : D)).symm).toRepresentationEquiv⟩
  exact hI.not_equiv_moved ρ hfix x hx he
end Representation.BinaryOffender

