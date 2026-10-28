module
public import Theory.Representation.NormalComponentConstituents.Exchanged
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Central kernels and centerless constituent images

For a faithful irreducible ambient representation and a normal subgroup,
a nonzero constituent with centerless action image has trivial central kernel.
Indeed, the center of the normal subgroup fixes the constituent. Its fixed
space is ambient invariant, hence is the whole representation; ambient
faithfulness then kills that center.

This supplies the kernel step before transporting automorphisms to a recognized
constituent image. Source: the central-kernel branch of Aschbacher--Smith
G.10.15, printed p.363.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- A central constituent kernel is trivial if the actual image has trivial
center and the ambient representation is faithful and irreducible. -/
theorem faithful_constituent_of_centerless_image
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (H : Subgroup D) [H.Normal] (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer ρ I) (hne : I ≠ ⊥)
    (hc : center
      (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
        (invariantSubspace ρ H I hI).toRepresentation.asGroupHom).range) = ⊥)
    (hk : (invariantSubspace ρ H I hI).toRepresentation.asGroupHom.ker ≤ center H) :
    Function.Injective (invariantSubspace ρ H I hI).toRepresentation.asGroupHom := by
  let f := (invariantSubspace ρ H I hI).toRepresentation.asGroupHom
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I
  let f' := e.toMonoidHom.comp f
  let Z := (center H).map H.subtype
  let : Z.Normal := inferInstanceAs ((center H).map H.subtype).Normal
  have hfix : I ≤ fixedSpace ρ Z := by
    intro u hu z
    obtain ⟨a,ha,he⟩ := z.property
    have ha1 : f'.rangeRestrict a = 1 := by
      apply mem_bot.mp
      rw [← hc]
      apply mem_center_iff.mpr
      intro b
      obtain ⟨c,rfl⟩ := f'.rangeRestrict_surjective b
      exact (map_mul f'.rangeRestrict c a).symm.trans
        ((congrArg f'.rangeRestrict (mem_center_iff.mp ha c)).trans
          (map_mul f'.rangeRestrict a c))
    have haf : f a = 1 := by
      apply e.injective
      exact (congrArg Subtype.val ha1).trans e.map_one.symm
    have hh := congrArg (fun t => ((t : LinearMap.GeneralLinearGroup (ZMod 2) I).val ⟨u,hu⟩ : V)) haf
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


/-- A concrete module-invariance condition, including an intertwining operator
for every automorphism of the actual image group. -/
@[expose] def ImageAutomorphismsLinear {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (K : Subgroup (U ≃ₗ[ZMod 2] U)) : Prop :=
  ∀ α : MulAut K, ∃ c : U ≃ₗ[ZMod 2] U,
    ∀ k : K, ∀ u : U, c (k.val u) = (α k).val (c u)

/-- For a faithful constituent, a moved homogeneous partner rules out
invariance of its actual module under all automorphisms of the image.
The proof transports conjugation through the literal faithful action map. -/
theorem Homogeneous.IsIrrPlusWith.not_imageAutomorphismsLinear
    {H X : Subgroup D} [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (hf : Function.Injective
      (invariantSubspace ρ H I hI.invariant).toRepresentation.asGroupHom)
    (x : X) (hx : I.map (ρ (x : D)⁻¹) ≠ I) :
    ¬ ImageAutomorphismsLinear
      (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
        (invariantSubspace ρ H I hI.invariant).toRepresentation.asGroupHom).range) := by
  intro hAut
  let R := invariantSubspace ρ H I hI.invariant
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    R.toRepresentation.asGroupHom
  have hf' : Function.Injective f :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective.comp hf
  let e : H ≃* f.range := MonoidHom.ofInjective hf'
  let α : MulAut f.range := (e.symm.trans (MulAut.conjNormal (x : D))).trans e
  obtain ⟨c,hc⟩ := hAut α
  have hα (h : H) : α (e h) = e (MulAut.conjNormal (x : D) h) := by
    change e (MulAut.conjNormal (x : D) (e.symm (e h))) = _
    rw [e.symm_apply_apply]
  let a : RepEquiv R.toRepresentation (conjugateRep R.toRepresentation (x : D)) :=
    .mk c (by
      intro h
      apply LinearMap.ext
      intro u
      have he := hc (e h) u
      rw [hα] at he
      exact he)
  exact hI.not_equiv_moved ρ hfix x hx
    ⟨(a.trans (conjugateSubrepresentationEquiv ρ H R (x : D)).symm).toRepresentationEquiv⟩

end Representation.BinaryOffender
