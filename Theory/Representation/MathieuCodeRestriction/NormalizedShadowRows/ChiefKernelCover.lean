module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.ChiefKernel

/-!
# Covered subgroups in the whole-span action image

A quotient of the faithful whole-span action by its two-core restricts to
any original subgroup. If that subgroup has a marked image in the reduced
actor, its whole-span image covers the marked group with kernel exactly
the intersection with the whole-action two-core. The cover preserves every
original action map; it makes no assertion that the kernel upstairs in the
original group is a two-group.

Source application: the original Cartan in Aschbacher--Smith, 3.1.9(6),
printed pp.577--578, as used in 8.2.2(1), p.715.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows
variable {H W W' K : Type*} [Group H] [Group K]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W']

/-- Restrict the actual two-core quotient to a marked subgroup image,
retaining its full kernel and the original action homomorphisms. -/
theorem ActionImageReduction.cover_subgroup
    {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) H W'}
    (d : ActionImageReduction ρ σ) (B : Subgroup H)
    (t : K →* actionImage σ) (ht : Function.Injective t)
    (hB : B.map (actionHom σ) = t.range) :
    ∃ f : actionSubgroup ρ B →* K,
      Function.Surjective f ∧
      (∀ b : B, t (f ⟨actionHom ρ b,mem_map_of_mem _ b.property⟩) = actionHom σ b) ∧
      f.ker = (pCore 2 (actionImage ρ)).subgroupOf (actionSubgroup ρ B) := by
  let P := actionSubgroup ρ B
  let g : P →* actionImage σ := d.equiv.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 (actionImage ρ))).comp P.subtype)
  have hg (x : P) : g x ∈ t.range := by
    obtain ⟨b,hb,he⟩ := x.property
    change d.equiv (QuotientGroup.mk' (pCore 2 (actionImage ρ)) x.val) ∈ t.range
    rw [← he,d.map_action]
    rw [← hB]
    exact mem_map_of_mem _ hb
  let r := g.codRestrict t.range hg
  let e := MonoidHom.ofInjective ht
  let f : P →* K := e.symm.toMonoidHom.comp r
  have he (x : P) : t (f x) = g x :=
    congrArg Subtype.val (e.apply_symm_apply (r x))
  refine ⟨f,?_,?_,?_⟩
  · intro a
    have hm : t a ∈ B.map (actionHom σ) := hB.symm ▸ ⟨a,rfl⟩
    obtain ⟨b,hb,hba⟩ := hm
    let x : P := ⟨actionHom ρ b,mem_map_of_mem _ hb⟩
    refine ⟨x,ht ?_⟩
    rw [he]
    exact (d.map_action b).trans hba
  · intro b
    exact (he _).trans (d.map_action b)
  · have hcomp : t.comp f = g := MonoidHom.ext he
    have hk := congrArg MonoidHom.ker hcomp
    rw [MonoidHom.ker_comp_of_injective _ _ ht] at hk
    rw [hk]
    change (d.equiv.toMonoidHom.comp
      ((QuotientGroup.mk' (pCore 2 (actionImage ρ))).comp P.subtype)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ d.equiv.injective,
      ← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rfl

end MathieuCode.NormalizedShadowRows
